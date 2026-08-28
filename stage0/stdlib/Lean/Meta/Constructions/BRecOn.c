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
uint8_t v___x_9080__boxed_555_; lean_object* v_res_556_; 
v___x_9080__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9080__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
v_options_610_ = lean_ctor_get(v___y_602_, 2);
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
v_ref_627_ = lean_ctor_get(v___y_624_, 5);
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
lean_object* v_fileName_902_; lean_object* v_fileMap_903_; lean_object* v_options_904_; lean_object* v_currRecDepth_905_; lean_object* v_maxRecDepth_906_; lean_object* v_ref_907_; lean_object* v_currNamespace_908_; lean_object* v_openDecls_909_; lean_object* v_initHeartbeats_910_; lean_object* v_maxHeartbeats_911_; lean_object* v_quotContext_912_; lean_object* v_currMacroScope_913_; uint8_t v_diag_914_; lean_object* v_cancelTk_x3f_915_; uint8_t v_suppressElabErrors_916_; lean_object* v_inheritedTraceOptions_917_; lean_object* v_ref_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v_fileName_902_ = lean_ctor_get(v___y_899_, 0);
v_fileMap_903_ = lean_ctor_get(v___y_899_, 1);
v_options_904_ = lean_ctor_get(v___y_899_, 2);
v_currRecDepth_905_ = lean_ctor_get(v___y_899_, 3);
v_maxRecDepth_906_ = lean_ctor_get(v___y_899_, 4);
v_ref_907_ = lean_ctor_get(v___y_899_, 5);
v_currNamespace_908_ = lean_ctor_get(v___y_899_, 6);
v_openDecls_909_ = lean_ctor_get(v___y_899_, 7);
v_initHeartbeats_910_ = lean_ctor_get(v___y_899_, 8);
v_maxHeartbeats_911_ = lean_ctor_get(v___y_899_, 9);
v_quotContext_912_ = lean_ctor_get(v___y_899_, 10);
v_currMacroScope_913_ = lean_ctor_get(v___y_899_, 11);
v_diag_914_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*14);
v_cancelTk_x3f_915_ = lean_ctor_get(v___y_899_, 12);
v_suppressElabErrors_916_ = lean_ctor_get_uint8(v___y_899_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_917_ = lean_ctor_get(v___y_899_, 13);
v_ref_918_ = l_Lean_replaceRef(v_ref_895_, v_ref_907_);
lean_inc_ref(v_inheritedTraceOptions_917_);
lean_inc(v_cancelTk_x3f_915_);
lean_inc(v_currMacroScope_913_);
lean_inc(v_quotContext_912_);
lean_inc(v_maxHeartbeats_911_);
lean_inc(v_initHeartbeats_910_);
lean_inc(v_openDecls_909_);
lean_inc(v_currNamespace_908_);
lean_inc(v_maxRecDepth_906_);
lean_inc(v_currRecDepth_905_);
lean_inc_ref(v_options_904_);
lean_inc_ref(v_fileMap_903_);
lean_inc_ref(v_fileName_902_);
v___x_919_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_919_, 0, v_fileName_902_);
lean_ctor_set(v___x_919_, 1, v_fileMap_903_);
lean_ctor_set(v___x_919_, 2, v_options_904_);
lean_ctor_set(v___x_919_, 3, v_currRecDepth_905_);
lean_ctor_set(v___x_919_, 4, v_maxRecDepth_906_);
lean_ctor_set(v___x_919_, 5, v_ref_918_);
lean_ctor_set(v___x_919_, 6, v_currNamespace_908_);
lean_ctor_set(v___x_919_, 7, v_openDecls_909_);
lean_ctor_set(v___x_919_, 8, v_initHeartbeats_910_);
lean_ctor_set(v___x_919_, 9, v_maxHeartbeats_911_);
lean_ctor_set(v___x_919_, 10, v_quotContext_912_);
lean_ctor_set(v___x_919_, 11, v_currMacroScope_913_);
lean_ctor_set(v___x_919_, 12, v_cancelTk_x3f_915_);
lean_ctor_set(v___x_919_, 13, v_inheritedTraceOptions_917_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*14, v_diag_914_);
lean_ctor_set_uint8(v___x_919_, sizeof(void*)*14 + 1, v_suppressElabErrors_916_);
v___x_920_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_896_, v___y_897_, v___y_898_, v___x_919_, v___y_900_);
lean_dec_ref_known(v___x_919_, 14);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_921_, lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_921_, v_msg_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v_ref_921_);
return v_res_928_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_929_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_933_ = lean_unsigned_to_nat(0u);
v___x_934_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_ctor_set(v___x_934_, 2, v___x_933_);
lean_ctor_set(v___x_934_, 3, v___x_933_);
lean_ctor_set(v___x_934_, 4, v___x_932_);
lean_ctor_set(v___x_934_, 5, v___x_932_);
lean_ctor_set(v___x_934_, 6, v___x_932_);
lean_ctor_set(v___x_934_, 7, v___x_932_);
lean_ctor_set(v___x_934_, 8, v___x_932_);
lean_ctor_set(v___x_934_, 9, v___x_932_);
lean_ctor_set(v___x_934_, 10, v___x_932_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(32u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
v___x_937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_938_ = ((size_t)5ULL);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = lean_unsigned_to_nat(32u);
v___x_941_ = lean_mk_empty_array_with_capacity(v___x_940_);
v___x_942_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_943_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_943_, 0, v___x_942_);
lean_ctor_set(v___x_943_, 1, v___x_941_);
lean_ctor_set(v___x_943_, 2, v___x_939_);
lean_ctor_set(v___x_943_, 3, v___x_939_);
lean_ctor_set_usize(v___x_943_, 4, v___x_938_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_944_ = lean_box(1);
v___x_945_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_946_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_947_, 0, v___x_946_);
lean_ctor_set(v___x_947_, 1, v___x_945_);
lean_ctor_set(v___x_947_, 2, v___x_944_);
return v___x_947_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_950_ = l_Lean_stringToMessageData(v___x_949_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_956_ = l_Lean_stringToMessageData(v___x_955_);
return v___x_956_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_958_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_959_ = l_Lean_stringToMessageData(v___x_958_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_962_ = l_Lean_stringToMessageData(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_965_ = l_Lean_stringToMessageData(v___x_964_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; 
v___x_967_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_968_ = l_Lean_stringToMessageData(v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_969_, lean_object* v_declHint_970_, lean_object* v___y_971_){
_start:
{
lean_object* v___x_973_; lean_object* v_env_974_; uint8_t v___x_975_; 
v___x_973_ = lean_st_ref_get(v___y_971_);
v_env_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc_ref(v_env_974_);
lean_dec(v___x_973_);
v___x_975_ = l_Lean_Name_isAnonymous(v_declHint_970_);
if (v___x_975_ == 0)
{
uint8_t v_isExporting_976_; 
v_isExporting_976_ = lean_ctor_get_uint8(v_env_974_, sizeof(void*)*8);
if (v_isExporting_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec_ref(v_env_974_);
lean_dec(v_declHint_970_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_msg_969_);
return v___x_977_;
}
else
{
lean_object* v___x_978_; uint8_t v___x_979_; 
lean_inc_ref(v_env_974_);
v___x_978_ = l_Lean_Environment_setExporting(v_env_974_, v___x_975_);
lean_inc(v_declHint_970_);
lean_inc_ref(v___x_978_);
v___x_979_ = l_Lean_Environment_contains(v___x_978_, v_declHint_970_, v_isExporting_976_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v___x_978_);
lean_dec_ref(v_env_974_);
lean_dec(v_declHint_970_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_msg_969_);
return v___x_980_;
}
else
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_c_986_; lean_object* v___x_987_; 
v___x_981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_983_ = l_Lean_Options_empty;
v___x_984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_984_, 0, v___x_978_);
lean_ctor_set(v___x_984_, 1, v___x_981_);
lean_ctor_set(v___x_984_, 2, v___x_982_);
lean_ctor_set(v___x_984_, 3, v___x_983_);
lean_inc(v_declHint_970_);
v___x_985_ = l_Lean_MessageData_ofConstName(v_declHint_970_, v___x_975_);
v_c_986_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_986_, 0, v___x_984_);
lean_ctor_set(v_c_986_, 1, v___x_985_);
v___x_987_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_974_, v_declHint_970_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
lean_dec_ref(v_env_974_);
lean_dec(v_declHint_970_);
v___x_988_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v_c_986_);
v___x_990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = l_Lean_MessageData_note(v___x_991_);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v_msg_969_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
else
{
lean_object* v_val_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1030_; 
v_val_995_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_997_ = v___x_987_;
v_isShared_998_ = v_isSharedCheck_1030_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_val_995_);
lean_dec(v___x_987_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1030_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_mod_1002_; uint8_t v___x_1003_; 
v___x_999_ = lean_box(0);
v___x_1000_ = l_Lean_Environment_header(v_env_974_);
lean_dec_ref(v_env_974_);
v___x_1001_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1000_);
v_mod_1002_ = lean_array_get(v___x_999_, v___x_1001_, v_val_995_);
lean_dec(v_val_995_);
lean_dec_ref(v___x_1001_);
v___x_1003_ = l_Lean_isPrivateName(v_declHint_970_);
lean_dec(v_declHint_970_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_c_986_);
v___x_1006_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1005_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = l_Lean_MessageData_ofName(v_mod_1002_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_MessageData_note(v___x_1011_);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_msg_969_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
if (v_isShared_998_ == 0)
{
lean_ctor_set_tag(v___x_997_, 0);
lean_ctor_set(v___x_997_, 0, v___x_1013_);
v___x_1015_ = v___x_997_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1013_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
else
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1017_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_1018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
lean_ctor_set(v___x_1018_, 1, v_c_986_);
v___x_1019_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_1020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1018_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_MessageData_ofName(v_mod_1002_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1020_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
v___x_1023_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = l_Lean_MessageData_note(v___x_1024_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_msg_969_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
if (v_isShared_998_ == 0)
{
lean_ctor_set_tag(v___x_997_, 0);
lean_ctor_set(v___x_997_, 0, v___x_1026_);
v___x_1028_ = v___x_997_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1031_; 
lean_dec_ref(v_env_974_);
lean_dec(v_declHint_970_);
v___x_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1031_, 0, v_msg_969_);
return v___x_1031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1032_, lean_object* v_declHint_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1032_, v_declHint_1033_, v___y_1034_);
lean_dec(v___y_1034_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1037_, lean_object* v_declHint_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1054_; 
v___x_1044_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1037_, v_declHint_1038_, v___y_1042_);
v_a_1045_ = lean_ctor_get(v___x_1044_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1044_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1047_ = v___x_1044_;
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_1044_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1054_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1052_; 
v___x_1049_ = l_Lean_unknownIdentifierMessageTag;
v___x_1050_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_a_1045_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 0, v___x_1050_);
v___x_1052_ = v___x_1047_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1050_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1055_, lean_object* v_declHint_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1055_, v_declHint_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1063_, lean_object* v_msg_1064_, lean_object* v_declHint_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; lean_object* v_a_1072_; lean_object* v___x_1073_; 
v___x_1071_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1064_, v_declHint_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref(v___x_1071_);
v___x_1073_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1063_, v_a_1072_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1074_, lean_object* v_msg_1075_, lean_object* v_declHint_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1074_, v_msg_1075_, v_declHint_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_ref_1074_);
return v_res_1082_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1089_, lean_object* v_constName_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1096_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1097_ = 0;
lean_inc(v_constName_1090_);
v___x_1098_ = l_Lean_MessageData_ofConstName(v_constName_1090_, v___x_1097_);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1096_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1089_, v___x_1101_, v_constName_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1103_, lean_object* v_constName_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1103_, v_constName_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v_ref_1103_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v_ref_1117_; lean_object* v___x_1118_; 
v_ref_1117_ = lean_ctor_get(v___y_1114_, 5);
v___x_1118_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1117_, v_constName_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; lean_object* v_env_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; 
v___x_1132_ = lean_st_ref_get(v___y_1130_);
v_env_1133_ = lean_ctor_get(v___x_1132_, 0);
lean_inc_ref(v_env_1133_);
lean_dec(v___x_1132_);
v___x_1134_ = 0;
lean_inc(v_constName_1126_);
v___x_1135_ = l_Lean_Environment_find_x3f(v_env_1133_, v_constName_1126_, v___x_1134_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
return v___x_1136_;
}
else
{
lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_constName_1126_);
v_val_1137_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1135_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v___x_1135_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
lean_ctor_set_tag(v___x_1139_, 0);
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_val_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1160_ = l_Lean_stringToMessageData(v___x_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1161_, lean_object* v_nParams_1162_, lean_object* v_belowName_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v___x_1169_; 
lean_inc(v_recName_1161_);
v___x_1169_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1161_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref_known(v___x_1169_, 1);
if (lean_obj_tag(v_a_1170_) == 7)
{
lean_object* v_val_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1287_; 
v_val_1171_ = lean_ctor_get(v_a_1170_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_a_1170_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1173_ = v_a_1170_;
v_isShared_1174_ = v_isSharedCheck_1287_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_val_1171_);
lean_dec(v_a_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1287_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_toConstantVal_1175_; lean_object* v_numMotives_1176_; lean_object* v_numMinors_1177_; lean_object* v_levelParams_1178_; lean_object* v_type_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v_toConstantVal_1175_ = lean_ctor_get(v_val_1171_, 0);
lean_inc_ref(v_toConstantVal_1175_);
v_numMotives_1176_ = lean_ctor_get(v_val_1171_, 4);
lean_inc(v_numMotives_1176_);
v_numMinors_1177_ = lean_ctor_get(v_val_1171_, 5);
lean_inc(v_numMinors_1177_);
lean_dec_ref(v_val_1171_);
v_levelParams_1178_ = lean_ctor_get(v_toConstantVal_1175_, 1);
lean_inc_n(v_levelParams_1178_, 2);
v_type_1179_ = lean_ctor_get(v_toConstantVal_1175_, 2);
lean_inc_ref(v_type_1179_);
lean_dec_ref(v_toConstantVal_1175_);
v___x_1180_ = lean_box(0);
v___x_1181_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1178_, v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 1)
{
lean_object* v_head_1182_; lean_object* v_tail_1183_; lean_object* v___x_1184_; lean_object* v___f_1185_; uint8_t v___x_1186_; lean_object* v___x_1187_; 
v_head_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_head_1182_);
v_tail_1183_ = lean_ctor_get(v___x_1181_, 1);
lean_inc(v_tail_1183_);
lean_dec_ref_known(v___x_1181_, 2);
v___x_1184_ = l_Lean_instInhabitedExpr;
v___f_1185_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1185_, 0, v_nParams_1162_);
lean_closure_set(v___f_1185_, 1, v_numMotives_1176_);
lean_closure_set(v___f_1185_, 2, v_numMinors_1177_);
lean_closure_set(v___f_1185_, 3, v___x_1184_);
lean_closure_set(v___f_1185_, 4, v_head_1182_);
lean_closure_set(v___f_1185_, 5, v_tail_1183_);
lean_closure_set(v___f_1185_, 6, v_recName_1161_);
lean_closure_set(v___f_1185_, 7, v_belowName_1163_);
lean_closure_set(v___f_1185_, 8, v_levelParams_1178_);
v___x_1186_ = 0;
v___x_1187_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1179_, v___f_1185_, v___x_1186_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1190_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc_n(v_a_1188_, 2);
lean_dec_ref_known(v___x_1187_, 1);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 1);
lean_ctor_set(v___x_1173_, 0, v_a_1188_);
v___x_1190_ = v___x_1173_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1188_);
v___x_1190_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_addDecl(v___x_1190_, v___x_1186_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_toConstantVal_1192_; lean_object* v_name_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref_known(v___x_1191_, 1);
v_toConstantVal_1192_ = lean_ctor_get(v_a_1188_, 0);
lean_inc_ref(v_toConstantVal_1192_);
lean_dec(v_a_1188_);
v_name_1193_ = lean_ctor_get(v_toConstantVal_1192_, 0);
lean_inc_n(v_name_1193_, 2);
lean_dec_ref(v_toConstantVal_1192_);
v___x_1194_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1193_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1270_ == 0)
{
lean_object* v_unused_1271_; 
v_unused_1271_ = lean_ctor_get(v___x_1194_, 0);
lean_dec(v_unused_1271_);
v___x_1196_ = v___x_1194_;
v_isShared_1197_ = v_isSharedCheck_1270_;
goto v_resetjp_1195_;
}
else
{
lean_dec(v___x_1194_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1270_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v_env_1199_; lean_object* v_nextMacroScope_1200_; lean_object* v_ngen_1201_; lean_object* v_auxDeclNGen_1202_; lean_object* v_traceState_1203_; lean_object* v_messages_1204_; lean_object* v_infoState_1205_; lean_object* v_snapshotTasks_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1268_; 
v___x_1198_ = lean_st_ref_take(v_a_1167_);
v_env_1199_ = lean_ctor_get(v___x_1198_, 0);
v_nextMacroScope_1200_ = lean_ctor_get(v___x_1198_, 1);
v_ngen_1201_ = lean_ctor_get(v___x_1198_, 2);
v_auxDeclNGen_1202_ = lean_ctor_get(v___x_1198_, 3);
v_traceState_1203_ = lean_ctor_get(v___x_1198_, 4);
v_messages_1204_ = lean_ctor_get(v___x_1198_, 6);
v_infoState_1205_ = lean_ctor_get(v___x_1198_, 7);
v_snapshotTasks_1206_ = lean_ctor_get(v___x_1198_, 8);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v___x_1198_, 5);
lean_dec(v_unused_1269_);
v___x_1208_ = v___x_1198_;
v_isShared_1209_ = v_isSharedCheck_1268_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snapshotTasks_1206_);
lean_inc(v_infoState_1205_);
lean_inc(v_messages_1204_);
lean_inc(v_traceState_1203_);
lean_inc(v_auxDeclNGen_1202_);
lean_inc(v_ngen_1201_);
lean_inc(v_nextMacroScope_1200_);
lean_inc(v_env_1199_);
lean_dec(v___x_1198_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1268_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
lean_inc(v_name_1193_);
v___x_1210_ = l_Lean_markAuxRecursor(v_env_1199_, v_name_1193_);
v___x_1211_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 5, v___x_1211_);
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_nextMacroScope_1200_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_ngen_1201_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_auxDeclNGen_1202_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_traceState_1203_);
lean_ctor_set(v_reuseFailAlloc_1267_, 5, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1267_, 6, v_messages_1204_);
lean_ctor_set(v_reuseFailAlloc_1267_, 7, v_infoState_1205_);
lean_ctor_set(v_reuseFailAlloc_1267_, 8, v_snapshotTasks_1206_);
v___x_1213_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_mctx_1216_; lean_object* v_zetaDeltaFVarIds_1217_; lean_object* v_postponed_1218_; lean_object* v_diag_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1265_; 
v___x_1214_ = lean_st_ref_put(v_a_1167_, v___x_1213_);
v___x_1215_ = lean_st_ref_take(v_a_1165_);
v_mctx_1216_ = lean_ctor_get(v___x_1215_, 0);
v_zetaDeltaFVarIds_1217_ = lean_ctor_get(v___x_1215_, 2);
v_postponed_1218_ = lean_ctor_get(v___x_1215_, 3);
v_diag_1219_ = lean_ctor_get(v___x_1215_, 4);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v___x_1215_, 1);
lean_dec(v_unused_1266_);
v___x_1221_ = v___x_1215_;
v_isShared_1222_ = v_isSharedCheck_1265_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_diag_1219_);
lean_inc(v_postponed_1218_);
lean_inc(v_zetaDeltaFVarIds_1217_);
lean_inc(v_mctx_1216_);
lean_dec(v___x_1215_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1265_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1223_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___x_1223_);
v___x_1225_ = v___x_1221_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_mctx_1216_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_zetaDeltaFVarIds_1217_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_postponed_1218_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v_diag_1219_);
v___x_1225_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_env_1228_; lean_object* v_nextMacroScope_1229_; lean_object* v_ngen_1230_; lean_object* v_auxDeclNGen_1231_; lean_object* v_traceState_1232_; lean_object* v_messages_1233_; lean_object* v_infoState_1234_; lean_object* v_snapshotTasks_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1262_; 
v___x_1226_ = lean_st_ref_put(v_a_1165_, v___x_1225_);
v___x_1227_ = lean_st_ref_take(v_a_1167_);
v_env_1228_ = lean_ctor_get(v___x_1227_, 0);
v_nextMacroScope_1229_ = lean_ctor_get(v___x_1227_, 1);
v_ngen_1230_ = lean_ctor_get(v___x_1227_, 2);
v_auxDeclNGen_1231_ = lean_ctor_get(v___x_1227_, 3);
v_traceState_1232_ = lean_ctor_get(v___x_1227_, 4);
v_messages_1233_ = lean_ctor_get(v___x_1227_, 6);
v_infoState_1234_ = lean_ctor_get(v___x_1227_, 7);
v_snapshotTasks_1235_ = lean_ctor_get(v___x_1227_, 8);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1227_, 5);
lean_dec(v_unused_1263_);
v___x_1237_ = v___x_1227_;
v_isShared_1238_ = v_isSharedCheck_1262_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_snapshotTasks_1235_);
lean_inc(v_infoState_1234_);
lean_inc(v_messages_1233_);
lean_inc(v_traceState_1232_);
lean_inc(v_auxDeclNGen_1231_);
lean_inc(v_ngen_1230_);
lean_inc(v_nextMacroScope_1229_);
lean_inc(v_env_1228_);
lean_dec(v___x_1227_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1262_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = l_Lean_addProtected(v_env_1228_, v_name_1193_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 5, v___x_1211_);
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_nextMacroScope_1229_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_ngen_1230_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_auxDeclNGen_1231_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_traceState_1232_);
lean_ctor_set(v_reuseFailAlloc_1261_, 5, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1261_, 6, v_messages_1233_);
lean_ctor_set(v_reuseFailAlloc_1261_, 7, v_infoState_1234_);
lean_ctor_set(v_reuseFailAlloc_1261_, 8, v_snapshotTasks_1235_);
v___x_1241_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v_mctx_1244_; lean_object* v_zetaDeltaFVarIds_1245_; lean_object* v_postponed_1246_; lean_object* v_diag_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1259_; 
v___x_1242_ = lean_st_ref_put(v_a_1167_, v___x_1241_);
v___x_1243_ = lean_st_ref_take(v_a_1165_);
v_mctx_1244_ = lean_ctor_get(v___x_1243_, 0);
v_zetaDeltaFVarIds_1245_ = lean_ctor_get(v___x_1243_, 2);
v_postponed_1246_ = lean_ctor_get(v___x_1243_, 3);
v_diag_1247_ = lean_ctor_get(v___x_1243_, 4);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1243_, 1);
lean_dec(v_unused_1260_);
v___x_1249_ = v___x_1243_;
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_diag_1247_);
lean_inc(v_postponed_1246_);
lean_inc(v_zetaDeltaFVarIds_1245_);
lean_inc(v_mctx_1244_);
lean_dec(v___x_1243_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1259_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 1, v___x_1223_);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_mctx_1244_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_zetaDeltaFVarIds_1245_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_postponed_1246_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v_diag_1247_);
v___x_1252_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1253_ = lean_st_ref_put(v_a_1165_, v___x_1252_);
v___x_1254_ = lean_box(0);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v___x_1254_);
v___x_1256_ = v___x_1196_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
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
lean_dec(v_a_1188_);
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
lean_del_object(v___x_1173_);
v_a_1273_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v___x_1187_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1187_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v___x_1181_);
lean_dec_ref(v_type_1179_);
lean_dec(v_levelParams_1178_);
lean_dec(v_numMinors_1177_);
lean_dec(v_numMotives_1176_);
lean_del_object(v___x_1173_);
lean_dec(v_belowName_1163_);
lean_dec(v_nParams_1162_);
v___x_1281_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1282_ = l_Lean_MessageData_ofName(v_recName_1161_);
v___x_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1281_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
v___x_1284_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1285_, 0, v___x_1283_);
lean_ctor_set(v___x_1285_, 1, v___x_1284_);
v___x_1286_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1285_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1286_;
}
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v_a_1170_);
lean_dec(v_belowName_1163_);
lean_dec(v_nParams_1162_);
v___x_1288_ = l_Lean_MessageData_ofName(v_recName_1161_);
v___x_1289_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1288_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1290_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1291_;
}
}
else
{
lean_object* v_a_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1299_; 
lean_dec(v_belowName_1163_);
lean_dec(v_nParams_1162_);
lean_dec(v_recName_1161_);
v_a_1292_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1294_ = v___x_1169_;
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_a_1292_);
lean_dec(v___x_1169_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1299_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1297_; 
if (v_isShared_1295_ == 0)
{
v___x_1297_ = v___x_1294_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v_a_1292_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1300_, lean_object* v_nParams_1301_, lean_object* v_belowName_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1300_, v_nParams_1301_, v_belowName_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
lean_dec(v_a_1306_);
lean_dec_ref(v_a_1305_);
lean_dec(v_a_1304_);
lean_dec_ref(v_a_1303_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1309_, lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1317_, v_msg_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1325_, uint8_t v_s_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1325_, v_s_1326_, v___y_1328_, v___y_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1333_, lean_object* v_s_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
uint8_t v_s_boxed_1340_; lean_object* v_res_1341_; 
v_s_boxed_1340_ = lean_unbox(v_s_1334_);
v_res_1341_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1333_, v_s_boxed_1340_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1342_, lean_object* v_constName_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1350_, lean_object* v_constName_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1350_, v_constName_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1358_, lean_object* v_ref_1359_, lean_object* v_constName_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1359_, v_constName_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1367_, lean_object* v_ref_1368_, lean_object* v_constName_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1367_, v_ref_1368_, v_constName_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v_ref_1368_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1376_, lean_object* v_ref_1377_, lean_object* v_msg_1378_, lean_object* v_declHint_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1377_, v_msg_1378_, v_declHint_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_ref_1387_, lean_object* v_msg_1388_, lean_object* v_declHint_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1386_, v_ref_1387_, v_msg_1388_, v_declHint_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v_ref_1387_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1396_, lean_object* v_declHint_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1396_, v_declHint_1397_, v___y_1401_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1404_, lean_object* v_declHint_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1404_, v_declHint_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1412_, lean_object* v_ref_1413_, lean_object* v_msg_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1413_, v_msg_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1421_, lean_object* v_ref_1422_, lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1421_, v_ref_1422_, v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v_ref_1422_);
return v_res_1429_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_unsigned_to_nat(32u);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1433_ = ((size_t)5ULL);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_unsigned_to_nat(32u);
v___x_1436_ = lean_mk_empty_array_with_capacity(v___x_1435_);
v___x_1437_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1438_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1434_);
lean_ctor_set(v___x_1438_, 3, v___x_1434_);
lean_ctor_set_usize(v___x_1438_, 4, v___x_1433_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1439_){
_start:
{
lean_object* v___x_1441_; lean_object* v_traceState_1442_; lean_object* v_traces_1443_; lean_object* v___x_1444_; lean_object* v_traceState_1445_; lean_object* v_env_1446_; lean_object* v_nextMacroScope_1447_; lean_object* v_ngen_1448_; lean_object* v_auxDeclNGen_1449_; lean_object* v_cache_1450_; lean_object* v_messages_1451_; lean_object* v_infoState_1452_; lean_object* v_snapshotTasks_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1472_; 
v___x_1441_ = lean_st_ref_get(v___y_1439_);
v_traceState_1442_ = lean_ctor_get(v___x_1441_, 4);
lean_inc_ref(v_traceState_1442_);
lean_dec(v___x_1441_);
v_traces_1443_ = lean_ctor_get(v_traceState_1442_, 0);
lean_inc_ref(v_traces_1443_);
lean_dec_ref(v_traceState_1442_);
v___x_1444_ = lean_st_ref_take(v___y_1439_);
v_traceState_1445_ = lean_ctor_get(v___x_1444_, 4);
v_env_1446_ = lean_ctor_get(v___x_1444_, 0);
v_nextMacroScope_1447_ = lean_ctor_get(v___x_1444_, 1);
v_ngen_1448_ = lean_ctor_get(v___x_1444_, 2);
v_auxDeclNGen_1449_ = lean_ctor_get(v___x_1444_, 3);
v_cache_1450_ = lean_ctor_get(v___x_1444_, 5);
v_messages_1451_ = lean_ctor_get(v___x_1444_, 6);
v_infoState_1452_ = lean_ctor_get(v___x_1444_, 7);
v_snapshotTasks_1453_ = lean_ctor_get(v___x_1444_, 8);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1455_ = v___x_1444_;
v_isShared_1456_ = v_isSharedCheck_1472_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_snapshotTasks_1453_);
lean_inc(v_infoState_1452_);
lean_inc(v_messages_1451_);
lean_inc(v_cache_1450_);
lean_inc(v_traceState_1445_);
lean_inc(v_auxDeclNGen_1449_);
lean_inc(v_ngen_1448_);
lean_inc(v_nextMacroScope_1447_);
lean_inc(v_env_1446_);
lean_dec(v___x_1444_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1472_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
uint64_t v_tid_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1470_; 
v_tid_1457_ = lean_ctor_get_uint64(v_traceState_1445_, sizeof(void*)*1);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_traceState_1445_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_traceState_1445_, 0);
lean_dec(v_unused_1471_);
v___x_1459_ = v_traceState_1445_;
v_isShared_1460_ = v_isSharedCheck_1470_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v_traceState_1445_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1470_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1461_);
lean_ctor_set_uint64(v_reuseFailAlloc_1469_, sizeof(void*)*1, v_tid_1457_);
v___x_1463_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
lean_object* v___x_1465_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 4, v___x_1463_);
v___x_1465_ = v___x_1455_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v_env_1446_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_nextMacroScope_1447_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_ngen_1448_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_auxDeclNGen_1449_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1468_, 5, v_cache_1450_);
lean_ctor_set(v_reuseFailAlloc_1468_, 6, v_messages_1451_);
lean_ctor_set(v_reuseFailAlloc_1468_, 7, v_infoState_1452_);
lean_ctor_set(v_reuseFailAlloc_1468_, 8, v_snapshotTasks_1453_);
v___x_1465_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1466_ = lean_st_ref_put(v___y_1439_, v___x_1465_);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v_traces_1443_);
return v___x_1467_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1473_);
lean_dec(v___y_1473_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1479_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1487_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1488_, lean_object* v_opt_1489_){
_start:
{
lean_object* v_name_1490_; lean_object* v_defValue_1491_; lean_object* v_map_1492_; lean_object* v___x_1493_; 
v_name_1490_ = lean_ctor_get(v_opt_1489_, 0);
v_defValue_1491_ = lean_ctor_get(v_opt_1489_, 1);
v_map_1492_ = lean_ctor_get(v_opts_1488_, 0);
v___x_1493_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1492_, v_name_1490_);
if (lean_obj_tag(v___x_1493_) == 0)
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_unbox(v_defValue_1491_);
return v___x_1494_;
}
else
{
lean_object* v_val_1495_; 
v_val_1495_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v___x_1493_, 1);
if (lean_obj_tag(v_val_1495_) == 1)
{
uint8_t v_v_1496_; 
v_v_1496_ = lean_ctor_get_uint8(v_val_1495_, 0);
lean_dec_ref_known(v_val_1495_, 0);
return v_v_1496_;
}
else
{
uint8_t v___x_1497_; 
lean_dec(v_val_1495_);
v___x_1497_ = lean_unbox(v_defValue_1491_);
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1498_, lean_object* v_opt_1499_){
_start:
{
uint8_t v_res_1500_; lean_object* v_r_1501_; 
v_res_1500_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1498_, v_opt_1499_);
lean_dec_ref(v_opt_1499_);
lean_dec_ref(v_opts_1498_);
v_r_1501_ = lean_box(v_res_1500_);
return v_r_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1502_, lean_object* v_x_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = l_Lean_MessageData_ofName(v_indName_1502_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_mkBelow___lam__0(v_indName_1511_, v_x_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_x_1512_);
return v_res_1518_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1519_){
_start:
{
if (lean_obj_tag(v_e_1519_) == 0)
{
uint8_t v___x_1520_; 
v___x_1520_ = 2;
return v___x_1520_;
}
else
{
uint8_t v___x_1521_; 
v___x_1521_ = 0;
return v___x_1521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1522_){
_start:
{
uint8_t v_res_1523_; lean_object* v_r_1524_; 
v_res_1523_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1522_);
lean_dec_ref(v_e_1522_);
v_r_1524_ = lean_box(v_res_1523_);
return v_r_1524_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1525_){
_start:
{
if (lean_obj_tag(v_x_1525_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
v_a_1527_ = lean_ctor_get(v_x_1525_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_x_1525_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v_x_1525_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v_x_1525_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 1);
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1542_; 
v_a_1535_ = lean_ctor_get(v_x_1525_, 0);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_x_1525_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1537_ = v_x_1525_;
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v_x_1525_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1542_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1540_; 
if (v_isShared_1538_ == 0)
{
lean_ctor_set_tag(v___x_1537_, 0);
v___x_1540_ = v___x_1537_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1543_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1546_, lean_object* v_opt_1547_){
_start:
{
lean_object* v_name_1548_; lean_object* v_defValue_1549_; lean_object* v_map_1550_; lean_object* v___x_1551_; 
v_name_1548_ = lean_ctor_get(v_opt_1547_, 0);
v_defValue_1549_ = lean_ctor_get(v_opt_1547_, 1);
v_map_1550_ = lean_ctor_get(v_opts_1546_, 0);
v___x_1551_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1550_, v_name_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_inc(v_defValue_1549_);
return v_defValue_1549_;
}
else
{
lean_object* v_val_1552_; 
v_val_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_val_1552_);
lean_dec_ref_known(v___x_1551_, 1);
if (lean_obj_tag(v_val_1552_) == 3)
{
lean_object* v_v_1553_; 
v_v_1553_ = lean_ctor_get(v_val_1552_, 0);
lean_inc(v_v_1553_);
lean_dec_ref_known(v_val_1552_, 1);
return v_v_1553_;
}
else
{
lean_dec(v_val_1552_);
lean_inc(v_defValue_1549_);
return v_defValue_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1554_, lean_object* v_opt_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1554_, v_opt_1555_);
lean_dec_ref(v_opt_1555_);
lean_dec_ref(v_opts_1554_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1557_, size_t v_i_1558_, lean_object* v_bs_1559_){
_start:
{
uint8_t v___x_1560_; 
v___x_1560_ = lean_usize_dec_lt(v_i_1558_, v_sz_1557_);
if (v___x_1560_ == 0)
{
return v_bs_1559_;
}
else
{
lean_object* v_v_1561_; lean_object* v_msg_1562_; lean_object* v___x_1563_; lean_object* v_bs_x27_1564_; size_t v___x_1565_; size_t v___x_1566_; lean_object* v___x_1567_; 
v_v_1561_ = lean_array_uget_borrowed(v_bs_1559_, v_i_1558_);
v_msg_1562_ = lean_ctor_get(v_v_1561_, 1);
lean_inc_ref(v_msg_1562_);
v___x_1563_ = lean_unsigned_to_nat(0u);
v_bs_x27_1564_ = lean_array_uset(v_bs_1559_, v_i_1558_, v___x_1563_);
v___x_1565_ = ((size_t)1ULL);
v___x_1566_ = lean_usize_add(v_i_1558_, v___x_1565_);
v___x_1567_ = lean_array_uset(v_bs_x27_1564_, v_i_1558_, v_msg_1562_);
v_i_1558_ = v___x_1566_;
v_bs_1559_ = v___x_1567_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1569_, lean_object* v_i_1570_, lean_object* v_bs_1571_){
_start:
{
size_t v_sz_boxed_1572_; size_t v_i_boxed_1573_; lean_object* v_res_1574_; 
v_sz_boxed_1572_ = lean_unbox_usize(v_sz_1569_);
lean_dec(v_sz_1569_);
v_i_boxed_1573_ = lean_unbox_usize(v_i_1570_);
lean_dec(v_i_1570_);
v_res_1574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1572_, v_i_boxed_1573_, v_bs_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1575_, lean_object* v_data_1576_, lean_object* v_ref_1577_, lean_object* v_msg_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_fileName_1584_; lean_object* v_fileMap_1585_; lean_object* v_options_1586_; lean_object* v_currRecDepth_1587_; lean_object* v_maxRecDepth_1588_; lean_object* v_ref_1589_; lean_object* v_currNamespace_1590_; lean_object* v_openDecls_1591_; lean_object* v_initHeartbeats_1592_; lean_object* v_maxHeartbeats_1593_; lean_object* v_quotContext_1594_; lean_object* v_currMacroScope_1595_; uint8_t v_diag_1596_; lean_object* v_cancelTk_x3f_1597_; uint8_t v_suppressElabErrors_1598_; lean_object* v_inheritedTraceOptions_1599_; lean_object* v___x_1600_; lean_object* v_traceState_1601_; lean_object* v_traces_1602_; lean_object* v_ref_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; lean_object* v_msg_1609_; lean_object* v___x_1610_; lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1648_; 
v_fileName_1584_ = lean_ctor_get(v___y_1581_, 0);
v_fileMap_1585_ = lean_ctor_get(v___y_1581_, 1);
v_options_1586_ = lean_ctor_get(v___y_1581_, 2);
v_currRecDepth_1587_ = lean_ctor_get(v___y_1581_, 3);
v_maxRecDepth_1588_ = lean_ctor_get(v___y_1581_, 4);
v_ref_1589_ = lean_ctor_get(v___y_1581_, 5);
v_currNamespace_1590_ = lean_ctor_get(v___y_1581_, 6);
v_openDecls_1591_ = lean_ctor_get(v___y_1581_, 7);
v_initHeartbeats_1592_ = lean_ctor_get(v___y_1581_, 8);
v_maxHeartbeats_1593_ = lean_ctor_get(v___y_1581_, 9);
v_quotContext_1594_ = lean_ctor_get(v___y_1581_, 10);
v_currMacroScope_1595_ = lean_ctor_get(v___y_1581_, 11);
v_diag_1596_ = lean_ctor_get_uint8(v___y_1581_, sizeof(void*)*14);
v_cancelTk_x3f_1597_ = lean_ctor_get(v___y_1581_, 12);
v_suppressElabErrors_1598_ = lean_ctor_get_uint8(v___y_1581_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1599_ = lean_ctor_get(v___y_1581_, 13);
v___x_1600_ = lean_st_ref_get(v___y_1582_);
v_traceState_1601_ = lean_ctor_get(v___x_1600_, 4);
lean_inc_ref(v_traceState_1601_);
lean_dec(v___x_1600_);
v_traces_1602_ = lean_ctor_get(v_traceState_1601_, 0);
lean_inc_ref(v_traces_1602_);
lean_dec_ref(v_traceState_1601_);
v_ref_1603_ = l_Lean_replaceRef(v_ref_1577_, v_ref_1589_);
lean_inc_ref(v_inheritedTraceOptions_1599_);
lean_inc(v_cancelTk_x3f_1597_);
lean_inc(v_currMacroScope_1595_);
lean_inc(v_quotContext_1594_);
lean_inc(v_maxHeartbeats_1593_);
lean_inc(v_initHeartbeats_1592_);
lean_inc(v_openDecls_1591_);
lean_inc(v_currNamespace_1590_);
lean_inc(v_maxRecDepth_1588_);
lean_inc(v_currRecDepth_1587_);
lean_inc_ref(v_options_1586_);
lean_inc_ref(v_fileMap_1585_);
lean_inc_ref(v_fileName_1584_);
v___x_1604_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1604_, 0, v_fileName_1584_);
lean_ctor_set(v___x_1604_, 1, v_fileMap_1585_);
lean_ctor_set(v___x_1604_, 2, v_options_1586_);
lean_ctor_set(v___x_1604_, 3, v_currRecDepth_1587_);
lean_ctor_set(v___x_1604_, 4, v_maxRecDepth_1588_);
lean_ctor_set(v___x_1604_, 5, v_ref_1603_);
lean_ctor_set(v___x_1604_, 6, v_currNamespace_1590_);
lean_ctor_set(v___x_1604_, 7, v_openDecls_1591_);
lean_ctor_set(v___x_1604_, 8, v_initHeartbeats_1592_);
lean_ctor_set(v___x_1604_, 9, v_maxHeartbeats_1593_);
lean_ctor_set(v___x_1604_, 10, v_quotContext_1594_);
lean_ctor_set(v___x_1604_, 11, v_currMacroScope_1595_);
lean_ctor_set(v___x_1604_, 12, v_cancelTk_x3f_1597_);
lean_ctor_set(v___x_1604_, 13, v_inheritedTraceOptions_1599_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*14, v_diag_1596_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*14 + 1, v_suppressElabErrors_1598_);
v___x_1605_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1602_);
lean_dec_ref(v_traces_1602_);
v_sz_1606_ = lean_array_size(v___x_1605_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1606_, v___x_1607_, v___x_1605_);
v_msg_1609_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1609_, 0, v_data_1576_);
lean_ctor_set(v_msg_1609_, 1, v_msg_1578_);
lean_ctor_set(v_msg_1609_, 2, v___x_1608_);
v___x_1610_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1609_, v___y_1579_, v___y_1580_, v___x_1604_, v___y_1582_);
lean_dec_ref_known(v___x_1604_, 14);
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1613_ = v___x_1610_;
v_isShared_1614_ = v_isSharedCheck_1648_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1610_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1648_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1615_; lean_object* v_traceState_1616_; lean_object* v_env_1617_; lean_object* v_nextMacroScope_1618_; lean_object* v_ngen_1619_; lean_object* v_auxDeclNGen_1620_; lean_object* v_cache_1621_; lean_object* v_messages_1622_; lean_object* v_infoState_1623_; lean_object* v_snapshotTasks_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1647_; 
v___x_1615_ = lean_st_ref_take(v___y_1582_);
v_traceState_1616_ = lean_ctor_get(v___x_1615_, 4);
v_env_1617_ = lean_ctor_get(v___x_1615_, 0);
v_nextMacroScope_1618_ = lean_ctor_get(v___x_1615_, 1);
v_ngen_1619_ = lean_ctor_get(v___x_1615_, 2);
v_auxDeclNGen_1620_ = lean_ctor_get(v___x_1615_, 3);
v_cache_1621_ = lean_ctor_get(v___x_1615_, 5);
v_messages_1622_ = lean_ctor_get(v___x_1615_, 6);
v_infoState_1623_ = lean_ctor_get(v___x_1615_, 7);
v_snapshotTasks_1624_ = lean_ctor_get(v___x_1615_, 8);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1626_ = v___x_1615_;
v_isShared_1627_ = v_isSharedCheck_1647_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_snapshotTasks_1624_);
lean_inc(v_infoState_1623_);
lean_inc(v_messages_1622_);
lean_inc(v_cache_1621_);
lean_inc(v_traceState_1616_);
lean_inc(v_auxDeclNGen_1620_);
lean_inc(v_ngen_1619_);
lean_inc(v_nextMacroScope_1618_);
lean_inc(v_env_1617_);
lean_dec(v___x_1615_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1647_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
uint64_t v_tid_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1645_; 
v_tid_1628_ = lean_ctor_get_uint64(v_traceState_1616_, sizeof(void*)*1);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_traceState_1616_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v_traceState_1616_, 0);
lean_dec(v_unused_1646_);
v___x_1630_ = v_traceState_1616_;
v_isShared_1631_ = v_isSharedCheck_1645_;
goto v_resetjp_1629_;
}
else
{
lean_dec(v_traceState_1616_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1645_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_ref_1577_);
lean_ctor_set(v___x_1632_, 1, v_a_1611_);
v___x_1633_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1575_, v___x_1632_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1633_);
v___x_1635_ = v___x_1630_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1633_);
lean_ctor_set_uint64(v_reuseFailAlloc_1644_, sizeof(void*)*1, v_tid_1628_);
v___x_1635_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 4, v___x_1635_);
v___x_1637_ = v___x_1626_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_env_1617_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_nextMacroScope_1618_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_ngen_1619_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_auxDeclNGen_1620_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1643_, 5, v_cache_1621_);
lean_ctor_set(v_reuseFailAlloc_1643_, 6, v_messages_1622_);
lean_ctor_set(v_reuseFailAlloc_1643_, 7, v_infoState_1623_);
lean_ctor_set(v_reuseFailAlloc_1643_, 8, v_snapshotTasks_1624_);
v___x_1637_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1638_ = lean_st_ref_put(v___y_1582_, v___x_1637_);
v___x_1639_ = lean_box(0);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1639_);
v___x_1641_ = v___x_1613_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1649_, lean_object* v_data_1650_, lean_object* v_ref_1651_, lean_object* v_msg_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1649_, v_data_1650_, v_ref_1651_, v_msg_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
return v_res_1658_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1659_; double v___x_1660_; 
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = lean_float_of_nat(v___x_1659_);
return v___x_1660_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1662_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1663_ = l_Lean_stringToMessageData(v___x_1662_);
return v___x_1663_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1664_; double v___x_1665_; 
v___x_1664_ = lean_unsigned_to_nat(1000u);
v___x_1665_ = lean_float_of_nat(v___x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1666_, uint8_t v_collapsed_1667_, lean_object* v_tag_1668_, lean_object* v_opts_1669_, uint8_t v_clsEnabled_1670_, lean_object* v_oldTraces_1671_, lean_object* v_msg_1672_, lean_object* v_resStartStop_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v_fst_1679_; lean_object* v_snd_1680_; lean_object* v___y_1682_; lean_object* v___y_1683_; lean_object* v_data_1684_; lean_object* v_fst_1687_; lean_object* v_snd_1688_; lean_object* v___x_1689_; uint8_t v___x_1690_; lean_object* v___y_1692_; lean_object* v_a_1693_; uint8_t v___y_1708_; double v___y_1739_; 
v_fst_1679_ = lean_ctor_get(v_resStartStop_1673_, 0);
lean_inc(v_fst_1679_);
v_snd_1680_ = lean_ctor_get(v_resStartStop_1673_, 1);
lean_inc(v_snd_1680_);
lean_dec_ref(v_resStartStop_1673_);
v_fst_1687_ = lean_ctor_get(v_snd_1680_, 0);
lean_inc(v_fst_1687_);
v_snd_1688_ = lean_ctor_get(v_snd_1680_, 1);
lean_inc(v_snd_1688_);
lean_dec(v_snd_1680_);
v___x_1689_ = l_Lean_trace_profiler;
v___x_1690_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1669_, v___x_1689_);
if (v___x_1690_ == 0)
{
v___y_1708_ = v___x_1690_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1745_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1669_, v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; double v___x_1748_; double v___x_1749_; double v___x_1750_; 
v___x_1746_ = l_Lean_trace_profiler_threshold;
v___x_1747_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1669_, v___x_1746_);
v___x_1748_ = lean_float_of_nat(v___x_1747_);
v___x_1749_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1750_ = lean_float_div(v___x_1748_, v___x_1749_);
v___y_1739_ = v___x_1750_;
goto v___jp_1738_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; double v___x_1753_; 
v___x_1751_ = l_Lean_trace_profiler_threshold;
v___x_1752_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1669_, v___x_1751_);
v___x_1753_ = lean_float_of_nat(v___x_1752_);
v___y_1739_ = v___x_1753_;
goto v___jp_1738_;
}
}
v___jp_1681_:
{
lean_object* v___x_1685_; 
lean_inc(v___y_1682_);
v___x_1685_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1671_, v_data_1684_, v___y_1682_, v___y_1683_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v___x_1686_; 
lean_dec_ref_known(v___x_1685_, 1);
v___x_1686_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1679_);
return v___x_1686_;
}
else
{
lean_dec(v_fst_1679_);
return v___x_1685_;
}
}
v___jp_1691_:
{
uint8_t v_result_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; double v___x_1697_; lean_object* v_data_1698_; 
v_result_1694_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1679_);
v___x_1695_ = lean_box(v_result_1694_);
v___x_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
v___x_1697_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1668_);
lean_inc_ref(v___x_1696_);
lean_inc(v_cls_1666_);
v_data_1698_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1698_, 0, v_cls_1666_);
lean_ctor_set(v_data_1698_, 1, v___x_1696_);
lean_ctor_set(v_data_1698_, 2, v_tag_1668_);
lean_ctor_set_float(v_data_1698_, sizeof(void*)*3, v___x_1697_);
lean_ctor_set_float(v_data_1698_, sizeof(void*)*3 + 8, v___x_1697_);
lean_ctor_set_uint8(v_data_1698_, sizeof(void*)*3 + 16, v_collapsed_1667_);
if (v___x_1690_ == 0)
{
lean_dec_ref_known(v___x_1696_, 1);
lean_dec(v_snd_1688_);
lean_dec(v_fst_1687_);
lean_dec_ref(v_tag_1668_);
lean_dec(v_cls_1666_);
v___y_1682_ = v___y_1692_;
v___y_1683_ = v_a_1693_;
v_data_1684_ = v_data_1698_;
goto v___jp_1681_;
}
else
{
lean_object* v_data_1699_; double v___x_1700_; double v___x_1701_; 
lean_dec_ref_known(v_data_1698_, 3);
v_data_1699_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1699_, 0, v_cls_1666_);
lean_ctor_set(v_data_1699_, 1, v___x_1696_);
lean_ctor_set(v_data_1699_, 2, v_tag_1668_);
v___x_1700_ = lean_unbox_float(v_fst_1687_);
lean_dec(v_fst_1687_);
lean_ctor_set_float(v_data_1699_, sizeof(void*)*3, v___x_1700_);
v___x_1701_ = lean_unbox_float(v_snd_1688_);
lean_dec(v_snd_1688_);
lean_ctor_set_float(v_data_1699_, sizeof(void*)*3 + 8, v___x_1701_);
lean_ctor_set_uint8(v_data_1699_, sizeof(void*)*3 + 16, v_collapsed_1667_);
v___y_1682_ = v___y_1692_;
v___y_1683_ = v_a_1693_;
v_data_1684_ = v_data_1699_;
goto v___jp_1681_;
}
}
v___jp_1702_:
{
lean_object* v_ref_1703_; lean_object* v___x_1704_; 
v_ref_1703_ = lean_ctor_get(v___y_1676_, 5);
lean_inc(v___y_1677_);
lean_inc_ref(v___y_1676_);
lean_inc(v___y_1675_);
lean_inc_ref(v___y_1674_);
lean_inc(v_fst_1679_);
v___x_1704_ = lean_apply_6(v_msg_1672_, v_fst_1679_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, lean_box(0));
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v___y_1692_ = v_ref_1703_;
v_a_1693_ = v_a_1705_;
goto v___jp_1691_;
}
else
{
lean_object* v___x_1706_; 
lean_dec_ref_known(v___x_1704_, 1);
v___x_1706_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1692_ = v_ref_1703_;
v_a_1693_ = v___x_1706_;
goto v___jp_1691_;
}
}
v___jp_1707_:
{
if (v_clsEnabled_1670_ == 0)
{
if (v___y_1708_ == 0)
{
lean_object* v___x_1709_; lean_object* v_traceState_1710_; lean_object* v_env_1711_; lean_object* v_nextMacroScope_1712_; lean_object* v_ngen_1713_; lean_object* v_auxDeclNGen_1714_; lean_object* v_cache_1715_; lean_object* v_messages_1716_; lean_object* v_infoState_1717_; lean_object* v_snapshotTasks_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1737_; 
lean_dec(v_snd_1688_);
lean_dec(v_fst_1687_);
lean_dec_ref(v_msg_1672_);
lean_dec_ref(v_tag_1668_);
lean_dec(v_cls_1666_);
v___x_1709_ = lean_st_ref_take(v___y_1677_);
v_traceState_1710_ = lean_ctor_get(v___x_1709_, 4);
v_env_1711_ = lean_ctor_get(v___x_1709_, 0);
v_nextMacroScope_1712_ = lean_ctor_get(v___x_1709_, 1);
v_ngen_1713_ = lean_ctor_get(v___x_1709_, 2);
v_auxDeclNGen_1714_ = lean_ctor_get(v___x_1709_, 3);
v_cache_1715_ = lean_ctor_get(v___x_1709_, 5);
v_messages_1716_ = lean_ctor_get(v___x_1709_, 6);
v_infoState_1717_ = lean_ctor_get(v___x_1709_, 7);
v_snapshotTasks_1718_ = lean_ctor_get(v___x_1709_, 8);
v_isSharedCheck_1737_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1720_ = v___x_1709_;
v_isShared_1721_ = v_isSharedCheck_1737_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_snapshotTasks_1718_);
lean_inc(v_infoState_1717_);
lean_inc(v_messages_1716_);
lean_inc(v_cache_1715_);
lean_inc(v_traceState_1710_);
lean_inc(v_auxDeclNGen_1714_);
lean_inc(v_ngen_1713_);
lean_inc(v_nextMacroScope_1712_);
lean_inc(v_env_1711_);
lean_dec(v___x_1709_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1737_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
uint64_t v_tid_1722_; lean_object* v_traces_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1736_; 
v_tid_1722_ = lean_ctor_get_uint64(v_traceState_1710_, sizeof(void*)*1);
v_traces_1723_ = lean_ctor_get(v_traceState_1710_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_traceState_1710_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1725_ = v_traceState_1710_;
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_traces_1723_);
lean_dec(v_traceState_1710_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1736_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1671_, v_traces_1723_);
lean_dec_ref(v_traces_1723_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1727_);
lean_ctor_set_uint64(v_reuseFailAlloc_1735_, sizeof(void*)*1, v_tid_1722_);
v___x_1729_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1731_; 
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 4, v___x_1729_);
v___x_1731_ = v___x_1720_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_env_1711_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_nextMacroScope_1712_);
lean_ctor_set(v_reuseFailAlloc_1734_, 2, v_ngen_1713_);
lean_ctor_set(v_reuseFailAlloc_1734_, 3, v_auxDeclNGen_1714_);
lean_ctor_set(v_reuseFailAlloc_1734_, 4, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1734_, 5, v_cache_1715_);
lean_ctor_set(v_reuseFailAlloc_1734_, 6, v_messages_1716_);
lean_ctor_set(v_reuseFailAlloc_1734_, 7, v_infoState_1717_);
lean_ctor_set(v_reuseFailAlloc_1734_, 8, v_snapshotTasks_1718_);
v___x_1731_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1732_ = lean_st_ref_put(v___y_1677_, v___x_1731_);
v___x_1733_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1679_);
return v___x_1733_;
}
}
}
}
}
else
{
goto v___jp_1702_;
}
}
else
{
goto v___jp_1702_;
}
}
v___jp_1738_:
{
double v___x_1740_; double v___x_1741_; double v___x_1742_; uint8_t v___x_1743_; 
v___x_1740_ = lean_unbox_float(v_snd_1688_);
v___x_1741_ = lean_unbox_float(v_fst_1687_);
v___x_1742_ = lean_float_sub(v___x_1740_, v___x_1741_);
v___x_1743_ = lean_float_decLt(v___y_1739_, v___x_1742_);
v___y_1708_ = v___x_1743_;
goto v___jp_1707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1754_, lean_object* v_collapsed_1755_, lean_object* v_tag_1756_, lean_object* v_opts_1757_, lean_object* v_clsEnabled_1758_, lean_object* v_oldTraces_1759_, lean_object* v_msg_1760_, lean_object* v_resStartStop_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v_collapsed_boxed_1767_; uint8_t v_clsEnabled_boxed_1768_; lean_object* v_res_1769_; 
v_collapsed_boxed_1767_ = lean_unbox(v_collapsed_1755_);
v_clsEnabled_boxed_1768_ = lean_unbox(v_clsEnabled_1758_);
v_res_1769_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1754_, v_collapsed_boxed_1767_, v_tag_1756_, v_opts_1757_, v_clsEnabled_boxed_1768_, v_oldTraces_1759_, v_msg_1760_, v_resStartStop_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec_ref(v_opts_1757_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, lean_object* v___x_1773_, lean_object* v_a_1774_, lean_object* v_b_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_lt(v_a_1774_, v_upperBound_1770_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1782_; 
lean_dec(v_a_1774_);
lean_dec(v___x_1773_);
lean_dec(v___x_1772_);
lean_dec(v___x_1771_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_b_1775_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1783_ = lean_unsigned_to_nat(1u);
v___x_1784_ = lean_nat_add(v_a_1774_, v___x_1783_);
lean_dec(v_a_1774_);
lean_inc_n(v___x_1784_, 2);
lean_inc(v___x_1771_);
v___x_1785_ = lean_name_append_index_after(v___x_1771_, v___x_1784_);
lean_inc(v___x_1772_);
v___x_1786_ = lean_name_append_index_after(v___x_1772_, v___x_1784_);
lean_inc(v___x_1773_);
v___x_1787_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1785_, v___x_1773_, v___x_1786_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v___x_1788_; 
lean_dec_ref_known(v___x_1787_, 1);
v___x_1788_ = lean_box(0);
v_a_1774_ = v___x_1784_;
v_b_1775_ = v___x_1788_;
goto _start;
}
else
{
lean_dec(v___x_1784_);
lean_dec(v___x_1773_);
lean_dec(v___x_1772_);
lean_dec(v___x_1771_);
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1790_, lean_object* v___x_1791_, lean_object* v___x_1792_, lean_object* v___x_1793_, lean_object* v_a_1794_, lean_object* v_b_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1790_, v___x_1791_, v___x_1792_, v___x_1793_, v_a_1794_, v_b_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v_upperBound_1790_);
return v_res_1801_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1811_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1812_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1813_ = l_Lean_Name_append(v___x_1812_, v___x_1811_);
return v___x_1813_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1814_; double v___x_1815_; 
v___x_1814_ = lean_unsigned_to_nat(1000000000u);
v___x_1815_ = lean_float_of_nat(v___x_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
lean_object* v_options_1822_; lean_object* v_inheritedTraceOptions_1823_; uint8_t v_hasTrace_1824_; lean_object* v___x_1825_; 
v_options_1822_ = lean_ctor_get(v_a_1819_, 2);
v_inheritedTraceOptions_1823_ = lean_ctor_get(v_a_1819_, 13);
v_hasTrace_1824_ = lean_ctor_get_uint8(v_options_1822_, sizeof(void*)*1);
v___x_1825_ = lean_box(0);
if (v_hasTrace_1824_ == 0)
{
lean_object* v___x_1826_; 
lean_inc(v_indName_1816_);
v___x_1826_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1890_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1890_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1890_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
if (lean_obj_tag(v_a_1827_) == 5)
{
lean_object* v_val_1831_; uint8_t v_isRec_1832_; 
v_val_1831_ = lean_ctor_get(v_a_1827_, 0);
lean_inc_ref(v_val_1831_);
lean_dec_ref_known(v_a_1827_, 1);
v_isRec_1832_ = lean_ctor_get_uint8(v_val_1831_, sizeof(void*)*6);
if (v_isRec_1832_ == 0)
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_dec_ref(v_val_1831_);
lean_dec(v_indName_1816_);
v___x_1833_ = lean_box(0);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1833_);
v___x_1835_ = v___x_1829_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
else
{
lean_object* v_toConstantVal_1837_; lean_object* v_numParams_1838_; lean_object* v_all_1839_; lean_object* v_numNested_1840_; lean_object* v_type_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1829_);
v_toConstantVal_1837_ = lean_ctor_get(v_val_1831_, 0);
lean_inc_ref(v_toConstantVal_1837_);
v_numParams_1838_ = lean_ctor_get(v_val_1831_, 1);
lean_inc(v_numParams_1838_);
v_all_1839_ = lean_ctor_get(v_val_1831_, 3);
lean_inc(v_all_1839_);
v_numNested_1840_ = lean_ctor_get(v_val_1831_, 5);
lean_inc(v_numNested_1840_);
lean_dec_ref(v_val_1831_);
v_type_1841_ = lean_ctor_get(v_toConstantVal_1837_, 2);
lean_inc_ref(v_type_1841_);
lean_dec_ref(v_toConstantVal_1837_);
v___x_1842_ = l_Lean_Meta_isPropFormerType(v_type_1841_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1877_; 
v_a_1843_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1845_ = v___x_1842_;
v_isShared_1846_ = v_isSharedCheck_1877_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1877_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_unbox(v_a_1843_);
lean_dec(v_a_1843_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
lean_del_object(v___x_1845_);
lean_inc_n(v_indName_1816_, 2);
v___x_1848_ = l_Lean_mkRecName(v_indName_1816_);
v___x_1849_ = l_Lean_mkBelowName(v_indName_1816_);
lean_inc(v___x_1849_);
lean_inc(v_numParams_1838_);
lean_inc(v___x_1848_);
v___x_1850_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1848_, v_numParams_1838_, v___x_1849_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1871_; 
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1871_ == 0)
{
lean_object* v_unused_1872_; 
v_unused_1872_ = lean_ctor_get(v___x_1850_, 0);
lean_dec(v_unused_1872_);
v___x_1852_ = v___x_1850_;
v_isShared_1853_ = v_isSharedCheck_1871_;
goto v_resetjp_1851_;
}
else
{
lean_dec(v___x_1850_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1871_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = l_List_get_x21Internal___redArg(v___x_1825_, v_all_1839_, v___x_1854_);
lean_dec(v_all_1839_);
v___x_1856_ = lean_name_eq(v___x_1855_, v_indName_1816_);
lean_dec(v_indName_1816_);
lean_dec(v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1859_; 
lean_dec(v___x_1849_);
lean_dec(v___x_1848_);
lean_dec(v_numNested_1840_);
lean_dec(v_numParams_1838_);
v___x_1857_ = lean_box(0);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1857_);
v___x_1859_ = v___x_1852_;
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
lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_del_object(v___x_1852_);
v___x_1861_ = lean_box(0);
v___x_1862_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1840_, v___x_1848_, v___x_1849_, v_numParams_1838_, v___x_1854_, v___x_1861_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_numNested_1840_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1869_; 
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1869_ == 0)
{
lean_object* v_unused_1870_; 
v_unused_1870_ = lean_ctor_get(v___x_1862_, 0);
lean_dec(v_unused_1870_);
v___x_1864_ = v___x_1862_;
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v___x_1862_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1869_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1867_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1861_);
v___x_1867_ = v___x_1864_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1861_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
}
else
{
return v___x_1862_;
}
}
}
}
else
{
lean_dec(v___x_1849_);
lean_dec(v___x_1848_);
lean_dec(v_numNested_1840_);
lean_dec(v_all_1839_);
lean_dec(v_numParams_1838_);
lean_dec(v_indName_1816_);
return v___x_1850_;
}
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1875_; 
lean_dec(v_numNested_1840_);
lean_dec(v_all_1839_);
lean_dec(v_numParams_1838_);
lean_dec(v_indName_1816_);
v___x_1873_ = lean_box(0);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1873_);
v___x_1875_ = v___x_1845_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1873_);
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
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1885_; 
lean_dec(v_numNested_1840_);
lean_dec(v_all_1839_);
lean_dec(v_numParams_1838_);
lean_dec(v_indName_1816_);
v_a_1878_ = lean_ctor_get(v___x_1842_, 0);
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1880_ = v___x_1842_;
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1842_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1885_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1883_; 
if (v_isShared_1881_ == 0)
{
v___x_1883_ = v___x_1880_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1888_; 
lean_dec(v_a_1827_);
lean_dec(v_indName_1816_);
v___x_1886_ = lean_box(0);
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1886_);
v___x_1888_ = v___x_1829_;
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
lean_dec(v_indName_1816_);
v_a_1891_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1826_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1826_);
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
else
{
lean_object* v___f_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v_a_1907_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v_a_1922_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v_a_1927_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v_a_1932_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v_a_1944_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v_a_1949_; 
lean_inc(v_indName_1816_);
v___f_1899_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1899_, 0, v_indName_1816_);
v___x_1900_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1901_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1902_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1903_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1823_, v_options_1822_, v___x_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2016_ = l_Lean_trace_profiler;
v___x_2017_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1822_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec_ref(v___f_1899_);
lean_inc(v_indName_1816_);
v___x_2018_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2082_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2082_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2082_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
if (lean_obj_tag(v_a_2019_) == 5)
{
lean_object* v_val_2023_; uint8_t v_isRec_2024_; 
v_val_2023_ = lean_ctor_get(v_a_2019_, 0);
lean_inc_ref(v_val_2023_);
lean_dec_ref_known(v_a_2019_, 1);
v_isRec_2024_ = lean_ctor_get_uint8(v_val_2023_, sizeof(void*)*6);
if (v_isRec_2024_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_dec_ref(v_val_2023_);
lean_dec(v_indName_1816_);
v___x_2025_ = lean_box(0);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2025_);
v___x_2027_ = v___x_2021_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
else
{
lean_object* v_toConstantVal_2029_; lean_object* v_numParams_2030_; lean_object* v_all_2031_; lean_object* v_numNested_2032_; lean_object* v_type_2033_; lean_object* v___x_2034_; 
lean_del_object(v___x_2021_);
v_toConstantVal_2029_ = lean_ctor_get(v_val_2023_, 0);
lean_inc_ref(v_toConstantVal_2029_);
v_numParams_2030_ = lean_ctor_get(v_val_2023_, 1);
lean_inc(v_numParams_2030_);
v_all_2031_ = lean_ctor_get(v_val_2023_, 3);
lean_inc(v_all_2031_);
v_numNested_2032_ = lean_ctor_get(v_val_2023_, 5);
lean_inc(v_numNested_2032_);
lean_dec_ref(v_val_2023_);
v_type_2033_ = lean_ctor_get(v_toConstantVal_2029_, 2);
lean_inc_ref(v_type_2033_);
lean_dec_ref(v_toConstantVal_2029_);
v___x_2034_ = l_Lean_Meta_isPropFormerType(v_type_2033_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2069_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2037_ = v___x_2034_;
v_isShared_2038_ = v_isSharedCheck_2069_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_2034_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2069_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
uint8_t v___x_2039_; 
v___x_2039_ = lean_unbox(v_a_2035_);
lean_dec(v_a_2035_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_del_object(v___x_2037_);
lean_inc_n(v_indName_1816_, 2);
v___x_2040_ = l_Lean_mkRecName(v_indName_1816_);
v___x_2041_ = l_Lean_mkBelowName(v_indName_1816_);
lean_inc(v___x_2041_);
lean_inc(v_numParams_2030_);
lean_inc(v___x_2040_);
v___x_2042_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2040_, v_numParams_2030_, v___x_2041_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2063_; 
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_2042_, 0);
lean_dec(v_unused_2064_);
v___x_2044_ = v___x_2042_;
v_isShared_2045_ = v_isSharedCheck_2063_;
goto v_resetjp_2043_;
}
else
{
lean_dec(v___x_2042_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2063_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = l_List_get_x21Internal___redArg(v___x_1825_, v_all_2031_, v___x_2046_);
lean_dec(v_all_2031_);
v___x_2048_ = lean_name_eq(v___x_2047_, v_indName_1816_);
lean_dec(v_indName_1816_);
lean_dec(v___x_2047_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2051_; 
lean_dec(v___x_2041_);
lean_dec(v___x_2040_);
lean_dec(v_numNested_2032_);
lean_dec(v_numParams_2030_);
v___x_2049_ = lean_box(0);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2049_);
v___x_2051_ = v___x_2044_;
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
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_del_object(v___x_2044_);
v___x_2053_ = lean_box(0);
v___x_2054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2032_, v___x_2040_, v___x_2041_, v_numParams_2030_, v___x_2046_, v___x_2053_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_numNested_2032_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2062_);
v___x_2056_ = v___x_2054_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v___x_2054_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2053_);
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2053_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
else
{
return v___x_2054_;
}
}
}
}
else
{
lean_dec(v___x_2041_);
lean_dec(v___x_2040_);
lean_dec(v_numNested_2032_);
lean_dec(v_all_2031_);
lean_dec(v_numParams_2030_);
lean_dec(v_indName_1816_);
return v___x_2042_;
}
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
lean_dec(v_numNested_2032_);
lean_dec(v_all_2031_);
lean_dec(v_numParams_2030_);
lean_dec(v_indName_1816_);
v___x_2065_ = lean_box(0);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2065_);
v___x_2067_ = v___x_2037_;
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
lean_dec(v_numNested_2032_);
lean_dec(v_all_2031_);
lean_dec(v_numParams_2030_);
lean_dec(v_indName_1816_);
v_a_2070_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2034_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2034_);
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
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_dec(v_a_2019_);
lean_dec(v_indName_1816_);
v___x_2078_ = lean_box(0);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2078_);
v___x_2080_ = v___x_2021_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
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
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_indName_1816_);
v_a_2083_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2018_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2018_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
goto v___jp_1951_;
}
}
else
{
goto v___jp_1951_;
}
v___jp_1904_:
{
lean_object* v___x_1908_; double v___x_1909_; double v___x_1910_; double v___x_1911_; double v___x_1912_; double v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1908_ = lean_io_mono_nanos_now();
v___x_1909_ = lean_float_of_nat(v___y_1906_);
v___x_1910_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1911_ = lean_float_div(v___x_1909_, v___x_1910_);
v___x_1912_ = lean_float_of_nat(v___x_1908_);
v___x_1913_ = lean_float_div(v___x_1912_, v___x_1910_);
v___x_1914_ = lean_box_float(v___x_1911_);
v___x_1915_ = lean_box_float(v___x_1913_);
v___x_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_a_1907_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1900_, v_hasTrace_1824_, v___x_1901_, v_options_1822_, v___x_1903_, v___y_1905_, v___f_1899_, v___x_1917_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
return v___x_1918_;
}
v___jp_1919_:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_a_1922_);
v___y_1905_ = v___y_1920_;
v___y_1906_ = v___y_1921_;
v_a_1907_ = v___x_1923_;
goto v___jp_1904_;
}
v___jp_1924_:
{
lean_object* v___x_1928_; 
v___x_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1928_, 0, v_a_1927_);
v___y_1905_ = v___y_1925_;
v___y_1906_ = v___y_1926_;
v_a_1907_ = v___x_1928_;
goto v___jp_1904_;
}
v___jp_1929_:
{
lean_object* v___x_1933_; double v___x_1934_; double v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1933_ = lean_io_get_num_heartbeats();
v___x_1934_ = lean_float_of_nat(v___y_1931_);
v___x_1935_ = lean_float_of_nat(v___x_1933_);
v___x_1936_ = lean_box_float(v___x_1934_);
v___x_1937_ = lean_box_float(v___x_1935_);
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1939_, 0, v_a_1932_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1900_, v_hasTrace_1824_, v___x_1901_, v_options_1822_, v___x_1903_, v___y_1930_, v___f_1899_, v___x_1939_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
return v___x_1940_;
}
v___jp_1941_:
{
lean_object* v___x_1945_; 
v___x_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1945_, 0, v_a_1944_);
v___y_1930_ = v___y_1942_;
v___y_1931_ = v___y_1943_;
v_a_1932_ = v___x_1945_;
goto v___jp_1929_;
}
v___jp_1946_:
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v_a_1949_);
v___y_1930_ = v___y_1947_;
v___y_1931_ = v___y_1948_;
v_a_1932_ = v___x_1950_;
goto v___jp_1929_;
}
v___jp_1951_:
{
lean_object* v___x_1952_; lean_object* v_a_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1952_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1820_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1955_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1822_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1816_);
v___x_1957_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
if (lean_obj_tag(v_a_1958_) == 5)
{
lean_object* v_val_1959_; uint8_t v_isRec_1960_; 
v_val_1959_ = lean_ctor_get(v_a_1958_, 0);
lean_inc_ref(v_val_1959_);
lean_dec_ref_known(v_a_1958_, 1);
v_isRec_1960_ = lean_ctor_get_uint8(v_val_1959_, sizeof(void*)*6);
if (v_isRec_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref(v_val_1959_);
lean_dec(v_indName_1816_);
v___x_1961_ = lean_box(0);
v___y_1920_ = v_a_1953_;
v___y_1921_ = v___x_1956_;
v_a_1922_ = v___x_1961_;
goto v___jp_1919_;
}
else
{
lean_object* v_toConstantVal_1962_; lean_object* v_numParams_1963_; lean_object* v_all_1964_; lean_object* v_numNested_1965_; lean_object* v_type_1966_; lean_object* v___x_1967_; 
v_toConstantVal_1962_ = lean_ctor_get(v_val_1959_, 0);
lean_inc_ref(v_toConstantVal_1962_);
v_numParams_1963_ = lean_ctor_get(v_val_1959_, 1);
lean_inc(v_numParams_1963_);
v_all_1964_ = lean_ctor_get(v_val_1959_, 3);
lean_inc(v_all_1964_);
v_numNested_1965_ = lean_ctor_get(v_val_1959_, 5);
lean_inc(v_numNested_1965_);
lean_dec_ref(v_val_1959_);
v_type_1966_ = lean_ctor_get(v_toConstantVal_1962_, 2);
lean_inc_ref(v_type_1966_);
lean_dec_ref(v_toConstantVal_1962_);
v___x_1967_ = l_Lean_Meta_isPropFormerType(v_type_1966_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; uint8_t v___x_1969_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = lean_unbox(v_a_1968_);
lean_dec(v_a_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
lean_inc_n(v_indName_1816_, 2);
v___x_1970_ = l_Lean_mkRecName(v_indName_1816_);
v___x_1971_ = l_Lean_mkBelowName(v_indName_1816_);
lean_inc(v___x_1971_);
lean_inc(v_numParams_1963_);
lean_inc(v___x_1970_);
v___x_1972_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1970_, v_numParams_1963_, v___x_1971_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; uint8_t v___x_1975_; 
lean_dec_ref_known(v___x_1972_, 1);
v___x_1973_ = lean_unsigned_to_nat(0u);
v___x_1974_ = l_List_get_x21Internal___redArg(v___x_1825_, v_all_1964_, v___x_1973_);
lean_dec(v_all_1964_);
v___x_1975_ = lean_name_eq(v___x_1974_, v_indName_1816_);
lean_dec(v_indName_1816_);
lean_dec(v___x_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; 
lean_dec(v___x_1971_);
lean_dec(v___x_1970_);
lean_dec(v_numNested_1965_);
lean_dec(v_numParams_1963_);
v___x_1976_ = lean_box(0);
v___y_1920_ = v_a_1953_;
v___y_1921_ = v___x_1956_;
v_a_1922_ = v___x_1976_;
goto v___jp_1919_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_box(0);
v___x_1978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1965_, v___x_1970_, v___x_1971_, v_numParams_1963_, v___x_1973_, v___x_1977_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_numNested_1965_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_dec_ref_known(v___x_1978_, 1);
v___y_1920_ = v_a_1953_;
v___y_1921_ = v___x_1956_;
v_a_1922_ = v___x_1977_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1979_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref_known(v___x_1978_, 1);
v___y_1925_ = v_a_1953_;
v___y_1926_ = v___x_1956_;
v_a_1927_ = v_a_1979_;
goto v___jp_1924_;
}
}
}
else
{
lean_dec(v___x_1971_);
lean_dec(v___x_1970_);
lean_dec(v_numNested_1965_);
lean_dec(v_all_1964_);
lean_dec(v_numParams_1963_);
lean_dec(v_indName_1816_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1980_; 
v_a_1980_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___x_1972_, 1);
v___y_1920_ = v_a_1953_;
v___y_1921_ = v___x_1956_;
v_a_1922_ = v_a_1980_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1972_, 1);
v___y_1925_ = v_a_1953_;
v___y_1926_ = v___x_1956_;
v_a_1927_ = v_a_1981_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v___x_1982_; 
lean_dec(v_numNested_1965_);
lean_dec(v_all_1964_);
lean_dec(v_numParams_1963_);
lean_dec(v_indName_1816_);
v___x_1982_ = lean_box(0);
v___y_1920_ = v_a_1953_;
v___y_1921_ = v___x_1956_;
v_a_1922_ = v___x_1982_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_a_1983_; 
lean_dec(v_numNested_1965_);
lean_dec(v_all_1964_);
lean_dec(v_numParams_1963_);
lean_dec(v_indName_1816_);
v_a_1983_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1967_, 1);
v___y_1925_ = v_a_1953_;
v___y_1926_ = v___x_1956_;
v_a_1927_ = v_a_1983_;
goto v___jp_1924_;
}
}
}
else
{
lean_object* v___x_1984_; 
lean_dec(v_a_1958_);
lean_dec(v_indName_1816_);
v___x_1984_ = lean_box(0);
v___y_1920_ = v_a_1953_;
v___y_1921_ = v___x_1956_;
v_a_1922_ = v___x_1984_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_a_1985_; 
lean_dec(v_indName_1816_);
v_a_1985_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1957_, 1);
v___y_1925_ = v_a_1953_;
v___y_1926_ = v___x_1956_;
v_a_1927_ = v_a_1985_;
goto v___jp_1924_;
}
}
else
{
lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1986_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1816_);
v___x_1987_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1987_) == 0)
{
lean_object* v_a_1988_; 
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref_known(v___x_1987_, 1);
if (lean_obj_tag(v_a_1988_) == 5)
{
lean_object* v_val_1989_; uint8_t v_isRec_1990_; 
v_val_1989_ = lean_ctor_get(v_a_1988_, 0);
lean_inc_ref(v_val_1989_);
lean_dec_ref_known(v_a_1988_, 1);
v_isRec_1990_ = lean_ctor_get_uint8(v_val_1989_, sizeof(void*)*6);
if (v_isRec_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_dec_ref(v_val_1989_);
lean_dec(v_indName_1816_);
v___x_1991_ = lean_box(0);
v___y_1942_ = v_a_1953_;
v___y_1943_ = v___x_1986_;
v_a_1944_ = v___x_1991_;
goto v___jp_1941_;
}
else
{
lean_object* v_toConstantVal_1992_; lean_object* v_numParams_1993_; lean_object* v_all_1994_; lean_object* v_numNested_1995_; lean_object* v_type_1996_; lean_object* v___x_1997_; 
v_toConstantVal_1992_ = lean_ctor_get(v_val_1989_, 0);
lean_inc_ref(v_toConstantVal_1992_);
v_numParams_1993_ = lean_ctor_get(v_val_1989_, 1);
lean_inc(v_numParams_1993_);
v_all_1994_ = lean_ctor_get(v_val_1989_, 3);
lean_inc(v_all_1994_);
v_numNested_1995_ = lean_ctor_get(v_val_1989_, 5);
lean_inc(v_numNested_1995_);
lean_dec_ref(v_val_1989_);
v_type_1996_ = lean_ctor_get(v_toConstantVal_1992_, 2);
lean_inc_ref(v_type_1996_);
lean_dec_ref(v_toConstantVal_1992_);
v___x_1997_ = l_Lean_Meta_isPropFormerType(v_type_1996_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; uint8_t v___x_1999_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = lean_unbox(v_a_1998_);
lean_dec(v_a_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_inc_n(v_indName_1816_, 2);
v___x_2000_ = l_Lean_mkRecName(v_indName_1816_);
v___x_2001_ = l_Lean_mkBelowName(v_indName_1816_);
lean_inc(v___x_2001_);
lean_inc(v_numParams_1993_);
lean_inc(v___x_2000_);
v___x_2002_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2000_, v_numParams_1993_, v___x_2001_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
lean_dec_ref_known(v___x_2002_, 1);
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = l_List_get_x21Internal___redArg(v___x_1825_, v_all_1994_, v___x_2003_);
lean_dec(v_all_1994_);
v___x_2005_ = lean_name_eq(v___x_2004_, v_indName_1816_);
lean_dec(v_indName_1816_);
lean_dec(v___x_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v___x_2001_);
lean_dec(v___x_2000_);
lean_dec(v_numNested_1995_);
lean_dec(v_numParams_1993_);
v___x_2006_ = lean_box(0);
v___y_1942_ = v_a_1953_;
v___y_1943_ = v___x_1986_;
v_a_1944_ = v___x_2006_;
goto v___jp_1941_;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_box(0);
v___x_2008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1995_, v___x_2000_, v___x_2001_, v_numParams_1993_, v___x_2003_, v___x_2007_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_numNested_1995_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_dec_ref_known(v___x_2008_, 1);
v___y_1942_ = v_a_1953_;
v___y_1943_ = v___x_1986_;
v_a_1944_ = v___x_2007_;
goto v___jp_1941_;
}
else
{
lean_object* v_a_2009_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___y_1947_ = v_a_1953_;
v___y_1948_ = v___x_1986_;
v_a_1949_ = v_a_2009_;
goto v___jp_1946_;
}
}
}
else
{
lean_dec(v___x_2001_);
lean_dec(v___x_2000_);
lean_dec(v_numNested_1995_);
lean_dec(v_all_1994_);
lean_dec(v_numParams_1993_);
lean_dec(v_indName_1816_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2010_; 
v_a_2010_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2002_, 1);
v___y_1942_ = v_a_1953_;
v___y_1943_ = v___x_1986_;
v_a_1944_ = v_a_2010_;
goto v___jp_1941_;
}
else
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2002_, 1);
v___y_1947_ = v_a_1953_;
v___y_1948_ = v___x_1986_;
v_a_1949_ = v_a_2011_;
goto v___jp_1946_;
}
}
}
else
{
lean_object* v___x_2012_; 
lean_dec(v_numNested_1995_);
lean_dec(v_all_1994_);
lean_dec(v_numParams_1993_);
lean_dec(v_indName_1816_);
v___x_2012_ = lean_box(0);
v___y_1942_ = v_a_1953_;
v___y_1943_ = v___x_1986_;
v_a_1944_ = v___x_2012_;
goto v___jp_1941_;
}
}
else
{
lean_object* v_a_2013_; 
lean_dec(v_numNested_1995_);
lean_dec(v_all_1994_);
lean_dec(v_numParams_1993_);
lean_dec(v_indName_1816_);
v_a_2013_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_1997_, 1);
v___y_1947_ = v_a_1953_;
v___y_1948_ = v___x_1986_;
v_a_1949_ = v_a_2013_;
goto v___jp_1946_;
}
}
}
else
{
lean_object* v___x_2014_; 
lean_dec(v_a_1988_);
lean_dec(v_indName_1816_);
v___x_2014_ = lean_box(0);
v___y_1942_ = v_a_1953_;
v___y_1943_ = v___x_1986_;
v_a_1944_ = v___x_2014_;
goto v___jp_1941_;
}
}
else
{
lean_object* v_a_2015_; 
lean_dec(v_indName_1816_);
v_a_2015_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_1987_, 1);
v___y_1947_ = v_a_1953_;
v___y_1948_ = v___x_1986_;
v_a_1949_ = v_a_2015_;
goto v___jp_1946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_){
_start:
{
lean_object* v_res_2097_; 
v_res_2097_ = l_Lean_mkBelow(v_indName_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
lean_dec(v_a_2095_);
lean_dec_ref(v_a_2094_);
lean_dec(v_a_2093_);
lean_dec_ref(v_a_2092_);
return v_res_2097_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2098_, lean_object* v___x_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v_inst_2102_, lean_object* v_R_2103_, lean_object* v_a_2104_, lean_object* v_b_2105_, lean_object* v_c_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2098_, v___x_2099_, v___x_2100_, v___x_2101_, v_a_2104_, v_b_2105_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2113_, lean_object* v___x_2114_, lean_object* v___x_2115_, lean_object* v___x_2116_, lean_object* v_inst_2117_, lean_object* v_R_2118_, lean_object* v_a_2119_, lean_object* v_b_2120_, lean_object* v_c_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2113_, v___x_2114_, v___x_2115_, v___x_2116_, v_inst_2117_, v_R_2118_, v_a_2119_, v_b_2120_, v_c_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
lean_dec(v_upperBound_2113_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2128_, lean_object* v_x_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2129_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_x_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2136_, v_x_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2143_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = l_List_reverse___redArg(v_a_2145_);
return v___x_2146_;
}
else
{
lean_object* v_head_2147_; lean_object* v_tail_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2157_; 
v_head_2147_ = lean_ctor_get(v_a_2144_, 0);
v_tail_2148_ = lean_ctor_get(v_a_2144_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_a_2144_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2150_ = v_a_2144_;
v_isShared_2151_ = v_isSharedCheck_2157_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_tail_2148_);
lean_inc(v_head_2147_);
lean_dec(v_a_2144_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2157_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = l_Lean_MessageData_ofExpr(v_head_2147_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 1, v_a_2145_);
lean_ctor_set(v___x_2150_, 0, v___x_2152_);
v___x_2154_ = v___x_2150_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_a_2145_);
v___x_2154_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
v_a_2144_ = v_tail_2148_;
v_a_2145_ = v___x_2154_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2158_, lean_object* v_v_2159_, lean_object* v_i_2160_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = lean_array_get_size(v_xs_2158_);
v___x_2162_ = lean_nat_dec_lt(v_i_2160_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; 
lean_dec(v_i_2160_);
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
else
{
lean_object* v___x_2164_; uint8_t v___x_2165_; 
v___x_2164_ = lean_array_fget_borrowed(v_xs_2158_, v_i_2160_);
v___x_2165_ = lean_expr_eqv(v___x_2164_, v_v_2159_);
if (v___x_2165_ == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_add(v_i_2160_, v___x_2166_);
lean_dec(v_i_2160_);
v_i_2160_ = v___x_2167_;
goto _start;
}
else
{
lean_object* v___x_2169_; 
v___x_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2169_, 0, v_i_2160_);
return v___x_2169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2170_, lean_object* v_v_2171_, lean_object* v_i_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2170_, v_v_2171_, v_i_2172_);
lean_dec_ref(v_v_2171_);
lean_dec_ref(v_xs_2170_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2174_, lean_object* v_v_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_unsigned_to_nat(0u);
v___x_2177_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2174_, v_v_2175_, v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2178_, lean_object* v_v_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2178_, v_v_2179_);
lean_dec_ref(v_v_2179_);
lean_dec_ref(v_xs_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2181_, lean_object* v_v_2182_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2181_, v_v_2182_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_box(0);
return v___x_2184_;
}
else
{
lean_object* v_val_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
v_val_2185_ = lean_ctor_get(v___x_2183_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2183_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2183_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_val_2185_);
lean_dec(v___x_2183_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_val_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2193_, lean_object* v_v_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2193_, v_v_2194_);
lean_dec_ref(v_v_2194_);
lean_dec_ref(v_xs_2193_);
return v_res_2195_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2197_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
return v___x_2198_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2202_, lean_object* v_prods_2203_, lean_object* v_motives_2204_, lean_object* v_fs_2205_, lean_object* v_minor__type_2206_, lean_object* v_x_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
if (lean_obj_tag(v_x_2207_) == 5)
{
lean_object* v_fn_2215_; lean_object* v_arg_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_fn_2215_ = lean_ctor_get(v_x_2207_, 0);
lean_inc_ref(v_fn_2215_);
v_arg_2216_ = lean_ctor_get(v_x_2207_, 1);
lean_inc_ref(v_arg_2216_);
lean_dec_ref_known(v_x_2207_, 2);
v___x_2217_ = lean_array_set(v_x_2208_, v_x_2209_, v_arg_2216_);
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_sub(v_x_2209_, v___x_2218_);
lean_dec(v_x_2209_);
v_x_2207_ = v_fn_2215_;
v_x_2208_ = v___x_2217_;
v_x_2209_ = v___x_2219_;
goto _start;
}
else
{
lean_object* v___x_2221_; 
lean_dec(v_x_2209_);
v___x_2221_ = l_Lean_Meta_PProdN_mk(v_rlvl_2202_, v_prods_2203_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; lean_object* v___x_2223_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
v___x_2223_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2204_, v_x_2207_);
lean_dec_ref(v_x_2207_);
if (lean_obj_tag(v___x_2223_) == 1)
{
lean_object* v_val_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v_minor__type_2206_);
lean_dec_ref(v_motives_2204_);
v_val_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_val_2224_);
lean_dec_ref_known(v___x_2223_, 1);
v___x_2225_ = l_Lean_instInhabitedExpr;
v___x_2226_ = lean_array_get_borrowed(v___x_2225_, v_fs_2205_, v_val_2224_);
lean_dec(v_val_2224_);
lean_inc(v_a_2222_);
v___x_2227_ = lean_array_push(v_x_2208_, v_a_2222_);
lean_inc(v___x_2226_);
v___x_2228_ = l_Lean_mkAppN(v___x_2226_, v___x_2227_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = l_Lean_Meta_mkPProdMk(v___x_2228_, v_a_2222_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v___x_2223_);
lean_dec(v_a_2222_);
lean_dec_ref(v_x_2208_);
v___x_2230_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2231_ = l_Lean_MessageData_ofExpr(v_minor__type_2206_);
v___x_2232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2230_);
lean_ctor_set(v___x_2232_, 1, v___x_2231_);
v___x_2233_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2232_);
lean_ctor_set(v___x_2234_, 1, v___x_2233_);
v___x_2235_ = lean_array_to_list(v_motives_2204_);
v___x_2236_ = lean_box(0);
v___x_2237_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2235_, v___x_2236_);
v___x_2238_ = l_Lean_MessageData_ofList(v___x_2237_);
v___x_2239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2234_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2239_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
return v___x_2240_;
}
}
else
{
lean_dec_ref(v_x_2208_);
lean_dec_ref(v_x_2207_);
lean_dec_ref(v_minor__type_2206_);
lean_dec_ref(v_motives_2204_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2241_, lean_object* v_prods_2242_, lean_object* v_motives_2243_, lean_object* v_fs_2244_, lean_object* v_minor__type_2245_, lean_object* v_x_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2241_, v_prods_2242_, v_motives_2243_, v_fs_2244_, v_minor__type_2245_, v_x_2246_, v_x_2247_, v_x_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_fs_2244_);
return v_res_2254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2255_; lean_object* v_dummy_2256_; 
v___x_2255_ = lean_box(0);
v_dummy_2256_ = l_Lean_Expr_sort___override(v___x_2255_);
return v_dummy_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2257_, lean_object* v_head_2258_, lean_object* v_belows_2259_, lean_object* v_prods_2260_, lean_object* v_rlvl_2261_, lean_object* v_fs_2262_, lean_object* v_minor__type_2263_, lean_object* v_tail_2264_, lean_object* v_arg__args_2265_, lean_object* v_arg__type_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2257_, v_head_2258_, v_belows_2259_, v_prods_2260_, v_rlvl_2261_, v_fs_2262_, v_minor__type_2263_, v_tail_2264_, v_arg__args_2265_, v_arg__type_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec_ref(v_arg__args_2265_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2273_, lean_object* v_motives_2274_, lean_object* v_belows_2275_, lean_object* v_fs_2276_, lean_object* v_minor__type_2277_, lean_object* v_prods_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_){
_start:
{
if (lean_obj_tag(v_a_2279_) == 0)
{
lean_object* v_dummy_2285_; lean_object* v_nargs_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
lean_dec_ref(v_belows_2275_);
v_dummy_2285_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2286_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2277_);
lean_inc(v_nargs_2286_);
v___x_2287_ = lean_mk_array(v_nargs_2286_, v_dummy_2285_);
v___x_2288_ = lean_unsigned_to_nat(1u);
v___x_2289_ = lean_nat_sub(v_nargs_2286_, v___x_2288_);
lean_dec(v_nargs_2286_);
lean_inc_ref(v_minor__type_2277_);
v___x_2290_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2273_, v_prods_2278_, v_motives_2274_, v_fs_2276_, v_minor__type_2277_, v_minor__type_2277_, v___x_2287_, v___x_2289_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
lean_dec_ref(v_fs_2276_);
return v___x_2290_;
}
else
{
lean_object* v_head_2291_; lean_object* v_tail_2292_; lean_object* v___x_2293_; 
v_head_2291_ = lean_ctor_get(v_a_2279_, 0);
lean_inc_n(v_head_2291_, 2);
v_tail_2292_ = lean_ctor_get(v_a_2279_, 1);
lean_inc(v_tail_2292_);
lean_dec_ref_known(v_a_2279_, 2);
lean_inc(v_a_2283_);
lean_inc_ref(v_a_2282_);
lean_inc(v_a_2281_);
lean_inc_ref(v_a_2280_);
v___x_2293_ = lean_infer_type(v_head_2291_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___f_2295_; uint8_t v___x_2296_; lean_object* v___x_2297_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v___x_2293_, 1);
v___f_2295_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2295_, 0, v_motives_2274_);
lean_closure_set(v___f_2295_, 1, v_head_2291_);
lean_closure_set(v___f_2295_, 2, v_belows_2275_);
lean_closure_set(v___f_2295_, 3, v_prods_2278_);
lean_closure_set(v___f_2295_, 4, v_rlvl_2273_);
lean_closure_set(v___f_2295_, 5, v_fs_2276_);
lean_closure_set(v___f_2295_, 6, v_minor__type_2277_);
lean_closure_set(v___f_2295_, 7, v_tail_2292_);
v___x_2296_ = 0;
v___x_2297_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2294_, v___f_2295_, v___x_2296_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_);
return v___x_2297_;
}
else
{
lean_dec(v_tail_2292_);
lean_dec(v_head_2291_);
lean_dec_ref(v_prods_2278_);
lean_dec_ref(v_minor__type_2277_);
lean_dec_ref(v_fs_2276_);
lean_dec_ref(v_belows_2275_);
lean_dec_ref(v_motives_2274_);
lean_dec(v_rlvl_2273_);
return v___x_2293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2298_, lean_object* v_rlvl_2299_, lean_object* v_motives_2300_, lean_object* v_belows_2301_, lean_object* v_fs_2302_, lean_object* v_minor__type_2303_, lean_object* v_tail_2304_, uint8_t v___x_2305_, uint8_t v___x_2306_, uint8_t v___x_2307_, lean_object* v_arg_x27_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_inc_ref(v_arg_x27_2308_);
v___x_2314_ = lean_array_push(v_prods_2298_, v_arg_x27_2308_);
v___x_2315_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2299_, v_motives_2300_, v_belows_2301_, v_fs_2302_, v_minor__type_2303_, v___x_2314_, v_tail_2304_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_mk_empty_array_with_capacity(v___x_2317_);
v___x_2319_ = lean_array_push(v___x_2318_, v_arg_x27_2308_);
v___x_2320_ = l_Lean_Meta_mkLambdaFVars(v___x_2319_, v_a_2316_, v___x_2305_, v___x_2306_, v___x_2305_, v___x_2306_, v___x_2307_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec_ref(v___x_2319_);
return v___x_2320_;
}
else
{
lean_dec_ref(v_arg_x27_2308_);
return v___x_2315_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2321_, lean_object* v_rlvl_2322_, lean_object* v_motives_2323_, lean_object* v_belows_2324_, lean_object* v_fs_2325_, lean_object* v_minor__type_2326_, lean_object* v_tail_2327_, lean_object* v___x_2328_, lean_object* v___x_2329_, lean_object* v___x_2330_, lean_object* v_arg_x27_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v___x_1743__boxed_2337_; uint8_t v___x_1744__boxed_2338_; uint8_t v___x_1745__boxed_2339_; lean_object* v_res_2340_; 
v___x_1743__boxed_2337_ = lean_unbox(v___x_2328_);
v___x_1744__boxed_2338_ = lean_unbox(v___x_2329_);
v___x_1745__boxed_2339_ = lean_unbox(v___x_2330_);
v_res_2340_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2321_, v_rlvl_2322_, v_motives_2323_, v_belows_2324_, v_fs_2325_, v_minor__type_2326_, v_tail_2327_, v___x_1743__boxed_2337_, v___x_1744__boxed_2338_, v___x_1745__boxed_2339_, v_arg_x27_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2341_, lean_object* v_head_2342_, lean_object* v_belows_2343_, lean_object* v_arg__type_2344_, lean_object* v_prods_2345_, lean_object* v_rlvl_2346_, lean_object* v_fs_2347_, lean_object* v_minor__type_2348_, lean_object* v_tail_2349_, lean_object* v_arg__args_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
if (lean_obj_tag(v_x_2351_) == 5)
{
lean_object* v_fn_2359_; lean_object* v_arg_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_fn_2359_ = lean_ctor_get(v_x_2351_, 0);
lean_inc_ref(v_fn_2359_);
v_arg_2360_ = lean_ctor_get(v_x_2351_, 1);
lean_inc_ref(v_arg_2360_);
lean_dec_ref_known(v_x_2351_, 2);
v___x_2361_ = lean_array_set(v_x_2352_, v_x_2353_, v_arg_2360_);
v___x_2362_ = lean_unsigned_to_nat(1u);
v___x_2363_ = lean_nat_sub(v_x_2353_, v___x_2362_);
lean_dec(v_x_2353_);
v_x_2351_ = v_fn_2359_;
v_x_2352_ = v___x_2361_;
v_x_2353_ = v___x_2363_;
goto _start;
}
else
{
lean_object* v___x_2365_; 
lean_dec(v_x_2353_);
v___x_2365_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2341_, v_x_2351_);
lean_dec_ref(v_x_2351_);
if (lean_obj_tag(v___x_2365_) == 1)
{
lean_object* v_val_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v_val_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_val_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2367_ = l_Lean_Expr_fvarId_x21(v_head_2342_);
lean_dec_ref(v_head_2342_);
v___x_2368_ = l_Lean_FVarId_getUserName___redArg(v___x_2367_, v___y_2354_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref_known(v___x_2368_, 1);
v___x_2370_ = l_Lean_instInhabitedExpr;
v___x_2371_ = lean_array_get_borrowed(v___x_2370_, v_belows_2343_, v_val_2366_);
lean_dec(v_val_2366_);
lean_inc(v___x_2371_);
v___x_2372_ = l_Lean_mkAppN(v___x_2371_, v_x_2352_);
lean_dec_ref(v_x_2352_);
v___x_2373_ = l_Lean_Meta_mkPProd(v_arg__type_2344_, v___x_2372_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; uint8_t v___x_2375_; uint8_t v___x_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2375_ = 0;
v___x_2376_ = 1;
v___x_2377_ = 1;
v___x_2378_ = l_Lean_Meta_mkForallFVars(v_arg__args_2350_, v_a_2374_, v___x_2375_, v___x_2376_, v___x_2376_, v___x_2377_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___f_2383_; lean_object* v___x_2384_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = lean_box(v___x_2375_);
v___x_2381_ = lean_box(v___x_2376_);
v___x_2382_ = lean_box(v___x_2377_);
v___f_2383_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2383_, 0, v_prods_2345_);
lean_closure_set(v___f_2383_, 1, v_rlvl_2346_);
lean_closure_set(v___f_2383_, 2, v_motives_2341_);
lean_closure_set(v___f_2383_, 3, v_belows_2343_);
lean_closure_set(v___f_2383_, 4, v_fs_2347_);
lean_closure_set(v___f_2383_, 5, v_minor__type_2348_);
lean_closure_set(v___f_2383_, 6, v_tail_2349_);
lean_closure_set(v___f_2383_, 7, v___x_2380_);
lean_closure_set(v___f_2383_, 8, v___x_2381_);
lean_closure_set(v___f_2383_, 9, v___x_2382_);
v___x_2384_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2369_, v_a_2379_, v___f_2383_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2384_;
}
else
{
lean_dec(v_a_2369_);
lean_dec(v_tail_2349_);
lean_dec_ref(v_minor__type_2348_);
lean_dec_ref(v_fs_2347_);
lean_dec(v_rlvl_2346_);
lean_dec_ref(v_prods_2345_);
lean_dec_ref(v_belows_2343_);
lean_dec_ref(v_motives_2341_);
return v___x_2378_;
}
}
else
{
lean_dec(v_a_2369_);
lean_dec(v_tail_2349_);
lean_dec_ref(v_minor__type_2348_);
lean_dec_ref(v_fs_2347_);
lean_dec(v_rlvl_2346_);
lean_dec_ref(v_prods_2345_);
lean_dec_ref(v_belows_2343_);
lean_dec_ref(v_motives_2341_);
return v___x_2373_;
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_dec(v_val_2366_);
lean_dec_ref(v_x_2352_);
lean_dec(v_tail_2349_);
lean_dec_ref(v_minor__type_2348_);
lean_dec_ref(v_fs_2347_);
lean_dec(v_rlvl_2346_);
lean_dec_ref(v_prods_2345_);
lean_dec_ref(v_arg__type_2344_);
lean_dec_ref(v_belows_2343_);
lean_dec_ref(v_motives_2341_);
v_a_2385_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2368_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2368_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
else
{
lean_object* v___x_2393_; 
lean_dec(v___x_2365_);
lean_dec_ref(v_x_2352_);
lean_dec_ref(v_arg__type_2344_);
v___x_2393_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2346_, v_motives_2341_, v_belows_2343_, v_fs_2347_, v_minor__type_2348_, v_prods_2345_, v_tail_2349_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; uint8_t v___x_2398_; uint8_t v___x_2399_; uint8_t v___x_2400_; lean_object* v___x_2401_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
v___x_2395_ = lean_unsigned_to_nat(1u);
v___x_2396_ = lean_mk_empty_array_with_capacity(v___x_2395_);
v___x_2397_ = lean_array_push(v___x_2396_, v_head_2342_);
v___x_2398_ = 0;
v___x_2399_ = 1;
v___x_2400_ = 1;
v___x_2401_ = l_Lean_Meta_mkLambdaFVars(v___x_2397_, v_a_2394_, v___x_2398_, v___x_2399_, v___x_2398_, v___x_2399_, v___x_2400_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec_ref(v___x_2397_);
return v___x_2401_;
}
else
{
lean_dec_ref(v_head_2342_);
return v___x_2393_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2402_, lean_object* v_head_2403_, lean_object* v_belows_2404_, lean_object* v_prods_2405_, lean_object* v_rlvl_2406_, lean_object* v_fs_2407_, lean_object* v_minor__type_2408_, lean_object* v_tail_2409_, lean_object* v_arg__args_2410_, lean_object* v_arg__type_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_dummy_2417_; lean_object* v_nargs_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v_dummy_2417_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2418_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2411_);
lean_inc(v_nargs_2418_);
v___x_2419_ = lean_mk_array(v_nargs_2418_, v_dummy_2417_);
v___x_2420_ = lean_unsigned_to_nat(1u);
v___x_2421_ = lean_nat_sub(v_nargs_2418_, v___x_2420_);
lean_dec(v_nargs_2418_);
lean_inc_ref(v_arg__type_2411_);
v___x_2422_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2402_, v_head_2403_, v_belows_2404_, v_arg__type_2411_, v_prods_2405_, v_rlvl_2406_, v_fs_2407_, v_minor__type_2408_, v_tail_2409_, v_arg__args_2410_, v_arg__type_2411_, v___x_2419_, v___x_2421_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2423_, lean_object* v_motives_2424_, lean_object* v_belows_2425_, lean_object* v_fs_2426_, lean_object* v_minor__type_2427_, lean_object* v_prods_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2423_, v_motives_2424_, v_belows_2425_, v_fs_2426_, v_minor__type_2427_, v_prods_2428_, v_a_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2436_ = _args[0];
lean_object* v_head_2437_ = _args[1];
lean_object* v_belows_2438_ = _args[2];
lean_object* v_arg__type_2439_ = _args[3];
lean_object* v_prods_2440_ = _args[4];
lean_object* v_rlvl_2441_ = _args[5];
lean_object* v_fs_2442_ = _args[6];
lean_object* v_minor__type_2443_ = _args[7];
lean_object* v_tail_2444_ = _args[8];
lean_object* v_arg__args_2445_ = _args[9];
lean_object* v_x_2446_ = _args[10];
lean_object* v_x_2447_ = _args[11];
lean_object* v_x_2448_ = _args[12];
lean_object* v___y_2449_ = _args[13];
lean_object* v___y_2450_ = _args[14];
lean_object* v___y_2451_ = _args[15];
lean_object* v___y_2452_ = _args[16];
lean_object* v___y_2453_ = _args[17];
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2436_, v_head_2437_, v_belows_2438_, v_arg__type_2439_, v_prods_2440_, v_rlvl_2441_, v_fs_2442_, v_minor__type_2443_, v_tail_2444_, v_arg__args_2445_, v_x_2446_, v_x_2447_, v_x_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v_arg__args_2445_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2455_, lean_object* v_motives_2456_, lean_object* v_belows_2457_, lean_object* v_fs_2458_, lean_object* v_minor__args_2459_, lean_object* v_minor__type_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2466_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2467_ = lean_array_to_list(v_minor__args_2459_);
v___x_2468_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2455_, v_motives_2456_, v_belows_2457_, v_fs_2458_, v_minor__type_2460_, v___x_2466_, v___x_2467_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2469_, lean_object* v_motives_2470_, lean_object* v_belows_2471_, lean_object* v_fs_2472_, lean_object* v_minor__args_2473_, lean_object* v_minor__type_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2469_, v_motives_2470_, v_belows_2471_, v_fs_2472_, v_minor__args_2473_, v_minor__type_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2481_, lean_object* v_motives_2482_, lean_object* v_belows_2483_, lean_object* v_fs_2484_, lean_object* v_minorType_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v___f_2491_; uint8_t v___x_2492_; lean_object* v___x_2493_; 
v___f_2491_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2491_, 0, v_rlvl_2481_);
lean_closure_set(v___f_2491_, 1, v_motives_2482_);
lean_closure_set(v___f_2491_, 2, v_belows_2483_);
lean_closure_set(v___f_2491_, 3, v_fs_2484_);
v___x_2492_ = 0;
v___x_2493_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2485_, v___f_2491_, v___x_2492_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2494_, lean_object* v_motives_2495_, lean_object* v_belows_2496_, lean_object* v_fs_2497_, lean_object* v_minorType_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2494_, v_motives_2495_, v_belows_2496_, v_fs_2497_, v_minorType_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___f_2511_; lean_object* v___x_27155__overap_2512_; lean_object* v___x_2513_; 
v___f_2511_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27155__overap_2512_ = lean_panic_fn_borrowed(v___f_2511_, v_msg_2505_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
v___x_2513_ = lean_apply_5(v___x_27155__overap_2512_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, lean_box(0));
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2521_, lean_object* v___y_2522_){
_start:
{
uint8_t v___x_2524_; 
v___x_2524_ = l_Lean_Expr_hasMVar(v_e_2521_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; 
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v_e_2521_);
return v___x_2525_;
}
else
{
lean_object* v___x_2526_; lean_object* v_mctx_2527_; lean_object* v___x_2528_; lean_object* v_fst_2529_; lean_object* v_snd_2530_; lean_object* v___x_2531_; lean_object* v_cache_2532_; lean_object* v_zetaDeltaFVarIds_2533_; lean_object* v_postponed_2534_; lean_object* v_diag_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2544_; 
v___x_2526_ = lean_st_ref_get(v___y_2522_);
v_mctx_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc_ref(v_mctx_2527_);
lean_dec(v___x_2526_);
v___x_2528_ = l_Lean_instantiateMVarsCore(v_mctx_2527_, v_e_2521_);
v_fst_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_fst_2529_);
v_snd_2530_ = lean_ctor_get(v___x_2528_, 1);
lean_inc(v_snd_2530_);
lean_dec_ref(v___x_2528_);
v___x_2531_ = lean_st_ref_take(v___y_2522_);
v_cache_2532_ = lean_ctor_get(v___x_2531_, 1);
v_zetaDeltaFVarIds_2533_ = lean_ctor_get(v___x_2531_, 2);
v_postponed_2534_ = lean_ctor_get(v___x_2531_, 3);
v_diag_2535_ = lean_ctor_get(v___x_2531_, 4);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2544_ == 0)
{
lean_object* v_unused_2545_; 
v_unused_2545_ = lean_ctor_get(v___x_2531_, 0);
lean_dec(v_unused_2545_);
v___x_2537_ = v___x_2531_;
v_isShared_2538_ = v_isSharedCheck_2544_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_diag_2535_);
lean_inc(v_postponed_2534_);
lean_inc(v_zetaDeltaFVarIds_2533_);
lean_inc(v_cache_2532_);
lean_dec(v___x_2531_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2544_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v_snd_2530_);
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_snd_2530_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_cache_2532_);
lean_ctor_set(v_reuseFailAlloc_2543_, 2, v_zetaDeltaFVarIds_2533_);
lean_ctor_set(v_reuseFailAlloc_2543_, 3, v_postponed_2534_);
lean_ctor_set(v_reuseFailAlloc_2543_, 4, v_diag_2535_);
v___x_2540_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_st_ref_put(v___y_2522_, v___x_2540_);
v___x_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2542_, 0, v_fst_2529_);
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2546_, v___y_2547_);
lean_dec(v___y_2547_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2550_, v___y_2552_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; lean_object* v_env_2568_; lean_object* v_toConstantVal_2569_; lean_object* v_value_2570_; lean_object* v_all_2571_; uint8_t v___y_2573_; lean_object* v_type_2581_; uint8_t v___x_2582_; 
v___x_2567_ = lean_st_ref_get(v___y_2565_);
v_env_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_ref_n(v_env_2568_, 2);
lean_dec(v___x_2567_);
v_toConstantVal_2569_ = lean_ctor_get(v_thm_2564_, 0);
v_value_2570_ = lean_ctor_get(v_thm_2564_, 1);
v_all_2571_ = lean_ctor_get(v_thm_2564_, 2);
v_type_2581_ = lean_ctor_get(v_toConstantVal_2569_, 2);
v___x_2582_ = l_Lean_Environment_hasUnsafe(v_env_2568_, v_type_2581_);
if (v___x_2582_ == 0)
{
uint8_t v___x_2583_; 
v___x_2583_ = l_Lean_Environment_hasUnsafe(v_env_2568_, v_value_2570_);
v___y_2573_ = v___x_2583_;
goto v___jp_2572_;
}
else
{
lean_dec_ref(v_env_2568_);
v___y_2573_ = v___x_2582_;
goto v___jp_2572_;
}
v___jp_2572_:
{
if (v___y_2573_ == 0)
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2574_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2574_, 0, v_thm_2564_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_inc(v_all_2571_);
lean_inc_ref(v_value_2570_);
lean_inc_ref(v_toConstantVal_2569_);
lean_dec_ref(v_thm_2564_);
v___x_2576_ = lean_box(0);
v___x_2577_ = 0;
v___x_2578_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2578_, 0, v_toConstantVal_2569_);
lean_ctor_set(v___x_2578_, 1, v_value_2570_);
lean_ctor_set(v___x_2578_, 2, v___x_2576_);
lean_ctor_set(v___x_2578_, 3, v_all_2571_);
lean_ctor_set_uint8(v___x_2578_, sizeof(void*)*4, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
return v___x_2580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2584_, v___y_2585_);
lean_dec(v___y_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2588_, v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2603_, lean_object* v___x_2604_, lean_object* v___x_2605_, lean_object* v_all_2606_, lean_object* v___x_2607_, lean_object* v___x_2608_, lean_object* v___x_2609_, lean_object* v_x_2610_){
_start:
{
lean_object* v___y_2612_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v___x_2616_ = lean_array_get_size(v_all_2606_);
v___x_2617_ = lean_nat_dec_lt(v_x_2610_, v___x_2616_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2618_ = lean_array_get_borrowed(v___x_2607_, v_all_2606_, v___x_2608_);
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2620_ = lean_nat_sub(v_x_2610_, v___x_2616_);
v___x_2621_ = lean_nat_add(v___x_2620_, v___x_2609_);
lean_dec(v___x_2620_);
v___x_2622_ = l_Nat_reprFast(v___x_2621_);
v___x_2623_ = lean_string_append(v___x_2619_, v___x_2622_);
lean_dec_ref(v___x_2622_);
lean_inc(v___x_2618_);
v___x_2624_ = l_Lean_Name_str___override(v___x_2618_, v___x_2623_);
v___y_2612_ = v___x_2624_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2625_ = lean_array_fget_borrowed(v_all_2606_, v_x_2610_);
lean_inc(v___x_2625_);
v___x_2626_ = l_Lean_mkBelowName(v___x_2625_);
v___y_2612_ = v___x_2626_;
goto v___jp_2611_;
}
v___jp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = l_Lean_Expr_const___override(v___y_2612_, v___x_2603_);
v___x_2614_ = l_Array_append___redArg(v___x_2604_, v___x_2605_);
v___x_2615_ = l_Lean_mkAppN(v___x_2613_, v___x_2614_);
lean_dec_ref(v___x_2614_);
return v___x_2615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2627_, lean_object* v___x_2628_, lean_object* v___x_2629_, lean_object* v_all_2630_, lean_object* v___x_2631_, lean_object* v___x_2632_, lean_object* v___x_2633_, lean_object* v_x_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2627_, v___x_2628_, v___x_2629_, v_all_2630_, v___x_2631_, v___x_2632_, v___x_2633_, v_x_2634_);
lean_dec(v_x_2634_);
lean_dec(v___x_2633_);
lean_dec(v___x_2632_);
lean_dec(v___x_2631_);
lean_dec_ref(v_all_2630_);
lean_dec_ref(v___x_2629_);
return v_res_2635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2636_, lean_object* v___x_2637_, uint8_t v___x_2638_, lean_object* v_targs_2639_, lean_object* v_x_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2646_ = l_Lean_mkAppN(v_a_2636_, v_targs_2639_);
v___x_2647_ = l_Lean_mkAppN(v___x_2637_, v_targs_2639_);
v___x_2648_ = l_Lean_Meta_mkPProd(v___x_2646_, v___x_2647_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; uint8_t v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; 
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v___x_2650_ = 0;
v___x_2651_ = 1;
v___x_2652_ = l_Lean_Meta_mkLambdaFVars(v_targs_2639_, v_a_2649_, v___x_2650_, v___x_2638_, v___x_2650_, v___x_2638_, v___x_2651_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2652_;
}
else
{
return v___x_2648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2653_, lean_object* v___x_2654_, lean_object* v___x_2655_, lean_object* v_targs_2656_, lean_object* v_x_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v___x_30350__boxed_2663_; lean_object* v_res_2664_; 
v___x_30350__boxed_2663_ = lean_unbox(v___x_2655_);
v_res_2664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2653_, v___x_2654_, v___x_30350__boxed_2663_, v_targs_2656_, v_x_2657_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec_ref(v_x_2657_);
lean_dec_ref(v_targs_2656_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2665_, lean_object* v___x_2666_, lean_object* v_as_2667_, size_t v_sz_2668_, size_t v_i_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = lean_usize_dec_lt(v_i_2669_, v_sz_2668_);
if (v___x_2676_ == 0)
{
lean_object* v___x_2677_; 
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_b_2670_);
return v___x_2677_;
}
else
{
lean_object* v_snd_2678_; lean_object* v_fst_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2736_; 
v_snd_2678_ = lean_ctor_get(v_b_2670_, 1);
v_fst_2679_ = lean_ctor_get(v_b_2670_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v_b_2670_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2681_ = v_b_2670_;
v_isShared_2682_ = v_isSharedCheck_2736_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_snd_2678_);
lean_inc(v_fst_2679_);
lean_dec(v_b_2670_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2736_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v_array_2683_; lean_object* v_start_2684_; lean_object* v_stop_2685_; uint8_t v___x_2686_; 
v_array_2683_ = lean_ctor_get(v_snd_2678_, 0);
v_start_2684_ = lean_ctor_get(v_snd_2678_, 1);
v_stop_2685_ = lean_ctor_get(v_snd_2678_, 2);
v___x_2686_ = lean_nat_dec_lt(v_start_2684_, v_stop_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2688_; 
if (v_isShared_2682_ == 0)
{
v___x_2688_ = v___x_2681_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_fst_2679_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_snd_2678_);
v___x_2688_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
lean_object* v___x_2689_; 
v___x_2689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
}
else
{
lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2732_; 
lean_inc(v_stop_2685_);
lean_inc(v_start_2684_);
lean_inc_ref(v_array_2683_);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_snd_2678_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; lean_object* v_unused_2734_; lean_object* v_unused_2735_; 
v_unused_2733_ = lean_ctor_get(v_snd_2678_, 2);
lean_dec(v_unused_2733_);
v_unused_2734_ = lean_ctor_get(v_snd_2678_, 1);
lean_dec(v_unused_2734_);
v_unused_2735_ = lean_ctor_get(v_snd_2678_, 0);
lean_dec(v_unused_2735_);
v___x_2692_ = v_snd_2678_;
v_isShared_2693_ = v_isSharedCheck_2732_;
goto v_resetjp_2691_;
}
else
{
lean_dec(v_snd_2678_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2732_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
v_a_2694_ = lean_array_uget_borrowed(v_as_2667_, v_i_2669_);
lean_inc(v___y_2674_);
lean_inc_ref(v___y_2673_);
lean_inc(v___y_2672_);
lean_inc_ref(v___y_2671_);
lean_inc(v_a_2694_);
v___x_2695_ = lean_infer_type(v_a_2694_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; uint8_t v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___f_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
v___x_2698_ = lean_array_fget_borrowed(v_array_2683_, v_start_2684_);
v___x_2699_ = lean_box(v___x_2697_);
lean_inc(v___x_2698_);
lean_inc(v_a_2694_);
v___f_2700_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2700_, 0, v_a_2694_);
lean_closure_set(v___f_2700_, 1, v___x_2698_);
lean_closure_set(v___f_2700_, 2, v___x_2699_);
v___x_2701_ = 0;
v___x_2702_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2696_, v___f_2700_, v___x_2701_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2707_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = lean_nat_add(v_start_2684_, v___x_2704_);
lean_dec(v_start_2684_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 1, v___x_2705_);
v___x_2707_ = v___x_2692_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_array_2683_);
lean_ctor_set(v_reuseFailAlloc_2715_, 1, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2715_, 2, v_stop_2685_);
v___x_2707_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
lean_object* v___x_2708_; lean_object* v___x_2710_; 
v___x_2708_ = l_Lean_Expr_app___override(v_fst_2679_, v_a_2703_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 1, v___x_2707_);
lean_ctor_set(v___x_2681_, 0, v___x_2708_);
v___x_2710_ = v___x_2681_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2708_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2707_);
v___x_2710_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
size_t v___x_2711_; size_t v___x_2712_; 
v___x_2711_ = ((size_t)1ULL);
v___x_2712_ = lean_usize_add(v_i_2669_, v___x_2711_);
v_i_2669_ = v___x_2712_;
v_b_2670_ = v___x_2710_;
goto _start;
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_del_object(v___x_2692_);
lean_dec(v_stop_2685_);
lean_dec(v_start_2684_);
lean_dec_ref(v_array_2683_);
lean_del_object(v___x_2681_);
lean_dec(v_fst_2679_);
v_a_2716_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2702_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2702_);
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
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_del_object(v___x_2692_);
lean_dec(v_stop_2685_);
lean_dec(v_start_2684_);
lean_dec_ref(v_array_2683_);
lean_del_object(v___x_2681_);
lean_dec(v_fst_2679_);
v_a_2724_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2695_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2695_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2737_, lean_object* v___x_2738_, lean_object* v_as_2739_, lean_object* v_sz_2740_, lean_object* v_i_2741_, lean_object* v_b_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
size_t v_sz_boxed_2748_; size_t v_i_boxed_2749_; lean_object* v_res_2750_; 
v_sz_boxed_2748_ = lean_unbox_usize(v_sz_2740_);
lean_dec(v_sz_2740_);
v_i_boxed_2749_ = lean_unbox_usize(v_i_2741_);
lean_dec(v_i_2741_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2737_, v___x_2738_, v_as_2739_, v_sz_boxed_2748_, v_i_boxed_2749_, v_b_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec_ref(v_as_2739_);
lean_dec(v___x_2738_);
lean_dec(v___x_2737_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2751_, size_t v_sz_2752_, size_t v_i_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = lean_usize_dec_lt(v_i_2753_, v_sz_2752_);
if (v___x_2760_ == 0)
{
lean_object* v___x_2761_; 
v___x_2761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_b_2754_);
return v___x_2761_;
}
else
{
lean_object* v_a_2762_; lean_object* v_toInductionSubgoal_2763_; lean_object* v_mvarId_2764_; uint8_t v___x_2765_; lean_object* v___x_2766_; 
v_a_2762_ = lean_array_uget_borrowed(v_as_2751_, v_i_2753_);
v_toInductionSubgoal_2763_ = lean_ctor_get(v_a_2762_, 0);
v_mvarId_2764_ = lean_ctor_get(v_toInductionSubgoal_2763_, 0);
v___x_2765_ = 0;
lean_inc(v_mvarId_2764_);
v___x_2766_ = l_Lean_MVarId_refl(v_mvarId_2764_, v___x_2765_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v___x_2767_; size_t v___x_2768_; size_t v___x_2769_; 
lean_dec_ref_known(v___x_2766_, 1);
v___x_2767_ = lean_box(0);
v___x_2768_ = ((size_t)1ULL);
v___x_2769_ = lean_usize_add(v_i_2753_, v___x_2768_);
v_i_2753_ = v___x_2769_;
v_b_2754_ = v___x_2767_;
goto _start;
}
else
{
return v___x_2766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2771_, lean_object* v_sz_2772_, lean_object* v_i_2773_, lean_object* v_b_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
size_t v_sz_boxed_2780_; size_t v_i_boxed_2781_; lean_object* v_res_2782_; 
v_sz_boxed_2780_ = lean_unbox_usize(v_sz_2772_);
lean_dec(v_sz_2772_);
v_i_boxed_2781_ = lean_unbox_usize(v_i_2773_);
lean_dec(v_i_2773_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2771_, v_sz_boxed_2780_, v_i_boxed_2781_, v_b_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec_ref(v_as_2771_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2783_, lean_object* v___x_2784_, lean_object* v___x_2785_, lean_object* v_fs_2786_, lean_object* v_as_2787_, size_t v_sz_2788_, size_t v_i_2789_, lean_object* v_b_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
uint8_t v___x_2796_; 
v___x_2796_ = lean_usize_dec_lt(v_i_2789_, v_sz_2788_);
if (v___x_2796_ == 0)
{
lean_object* v___x_2797_; 
lean_dec_ref(v_fs_2786_);
lean_dec_ref(v___x_2785_);
lean_dec_ref(v___x_2784_);
lean_dec(v___x_2783_);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_b_2790_);
return v___x_2797_;
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2799_; 
v_a_2798_ = lean_array_uget_borrowed(v_as_2787_, v_i_2789_);
lean_inc(v___y_2794_);
lean_inc_ref(v___y_2793_);
lean_inc(v___y_2792_);
lean_inc_ref(v___y_2791_);
lean_inc(v_a_2798_);
v___x_2799_ = lean_infer_type(v_a_2798_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
lean_inc_ref(v_fs_2786_);
lean_inc_ref(v___x_2785_);
lean_inc_ref(v___x_2784_);
lean_inc(v___x_2783_);
v___x_2801_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2783_, v___x_2784_, v___x_2785_, v_fs_2786_, v_a_2800_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v___x_2803_; size_t v___x_2804_; size_t v___x_2805_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___x_2803_ = l_Lean_Expr_app___override(v_b_2790_, v_a_2802_);
v___x_2804_ = ((size_t)1ULL);
v___x_2805_ = lean_usize_add(v_i_2789_, v___x_2804_);
v_i_2789_ = v___x_2805_;
v_b_2790_ = v___x_2803_;
goto _start;
}
else
{
lean_dec_ref(v_b_2790_);
lean_dec_ref(v_fs_2786_);
lean_dec_ref(v___x_2785_);
lean_dec_ref(v___x_2784_);
lean_dec(v___x_2783_);
return v___x_2801_;
}
}
else
{
lean_dec_ref(v_b_2790_);
lean_dec_ref(v_fs_2786_);
lean_dec_ref(v___x_2785_);
lean_dec_ref(v___x_2784_);
lean_dec(v___x_2783_);
return v___x_2799_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_fs_2810_, lean_object* v_as_2811_, lean_object* v_sz_2812_, lean_object* v_i_2813_, lean_object* v_b_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
size_t v_sz_boxed_2820_; size_t v_i_boxed_2821_; lean_object* v_res_2822_; 
v_sz_boxed_2820_ = lean_unbox_usize(v_sz_2812_);
lean_dec(v_sz_2812_);
v_i_boxed_2821_ = lean_unbox_usize(v_i_2813_);
lean_dec(v_i_2813_);
v_res_2822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2807_, v___x_2808_, v___x_2809_, v_fs_2810_, v_as_2811_, v_sz_boxed_2820_, v_i_boxed_2821_, v_b_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec_ref(v_as_2811_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2823_, lean_object* v_tail_2824_, lean_object* v_recName_2825_, lean_object* v___x_2826_, lean_object* v___x_2827_, lean_object* v___x_2828_, lean_object* v___x_2829_, lean_object* v___x_2830_, size_t v_sz_2831_, size_t v___x_2832_, lean_object* v___x_2833_, lean_object* v___x_2834_, lean_object* v___x_2835_, lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v_val_2839_, uint8_t v___x_2840_, lean_object* v_brecOnGoName_2841_, lean_object* v_levelParams_2842_, lean_object* v___x_2843_, lean_object* v_brecOnName_2844_, lean_object* v___x_2845_, lean_object* v_brecOnEqName_2846_, lean_object* v_fs_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_inc(v___x_2823_);
v___x_2853_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2823_);
lean_ctor_set(v___x_2853_, 1, v_tail_2824_);
v___x_2854_ = l_Lean_Expr_const___override(v_recName_2825_, v___x_2853_);
v___x_2855_ = l_Lean_mkAppN(v___x_2854_, v___x_2826_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2827_);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2828_, v___x_2829_, v___x_2830_, v_sz_2831_, v___x_2832_, v___x_2856_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v_fst_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_3220_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v_fst_2859_ = lean_ctor_get(v_a_2858_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v_a_2858_);
if (v_isSharedCheck_3220_ == 0)
{
lean_object* v_unused_3221_; 
v_unused_3221_ = lean_ctor_get(v_a_2858_, 1);
lean_dec(v_unused_3221_);
v___x_2861_ = v_a_2858_;
v_isShared_2862_ = v_isSharedCheck_3220_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_fst_2859_);
lean_dec(v_a_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_3220_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
size_t v_sz_2863_; lean_object* v___x_2864_; 
v_sz_2863_ = lean_array_size(v___x_2833_);
lean_inc_ref(v_fs_2847_);
lean_inc_ref(v___x_2834_);
lean_inc_ref(v___x_2830_);
v___x_2864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2823_, v___x_2830_, v___x_2834_, v_fs_2847_, v___x_2833_, v_sz_2863_, v___x_2832_, v_fst_2859_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = l_Lean_mkAppN(v_a_2865_, v___x_2835_);
lean_inc_ref_n(v___x_2836_, 3);
v___x_2867_ = l_Lean_Expr_app___override(v___x_2866_, v___x_2836_);
v___x_2868_ = l_Array_append___redArg(v___x_2826_, v___x_2830_);
v___x_2869_ = l_Array_append___redArg(v___x_2868_, v___x_2835_);
v___x_2870_ = lean_mk_empty_array_with_capacity(v___x_2837_);
v___x_2871_ = lean_array_push(v___x_2870_, v___x_2836_);
v___x_2872_ = lean_array_get(v___x_2838_, v___x_2830_, v_val_2839_);
lean_dec_ref(v___x_2830_);
v___x_2873_ = lean_array_push(v___x_2835_, v___x_2836_);
v___x_2874_ = l_Lean_mkAppN(v___x_2872_, v___x_2873_);
v___x_2875_ = lean_array_get(v___x_2838_, v___x_2834_, v_val_2839_);
lean_dec_ref(v___x_2834_);
v___x_2876_ = l_Lean_mkAppN(v___x_2875_, v___x_2873_);
lean_inc_ref(v___x_2874_);
v___x_2877_ = l_Lean_Meta_mkPProd(v___x_2874_, v___x_2876_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; uint8_t v___x_2881_; uint8_t v___x_2882_; lean_object* v___x_2883_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = l_Array_append___redArg(v___x_2869_, v___x_2871_);
lean_dec_ref(v___x_2871_);
v___x_2880_ = l_Array_append___redArg(v___x_2879_, v_fs_2847_);
v___x_2881_ = 0;
v___x_2882_ = 1;
v___x_2883_ = l_Lean_Meta_mkForallFVars(v___x_2880_, v_a_2878_, v___x_2881_, v___x_2840_, v___x_2840_, v___x_2882_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2883_) == 0)
{
lean_object* v_a_2884_; lean_object* v___x_2885_; 
v_a_2884_ = lean_ctor_get(v___x_2883_, 0);
lean_inc(v_a_2884_);
lean_dec_ref_known(v___x_2883_, 1);
v___x_2885_ = l_Lean_Meta_mkLambdaFVars(v___x_2880_, v___x_2867_, v___x_2881_, v___x_2840_, v___x_2881_, v___x_2840_, v___x_2882_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_3187_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = lean_box(1);
lean_inc(v_levelParams_2842_);
lean_inc(v_brecOnGoName_2841_);
v___x_2888_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2841_, v_levelParams_2842_, v_a_2884_, v_a_2886_, v___x_2887_, v___y_2851_);
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_3187_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_3187_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
lean_inc(v_a_2889_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set_tag(v___x_2891_, 1);
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_3186_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_addDecl(v___x_2894_, v___x_2881_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_toConstantVal_2896_; lean_object* v_name_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref_known(v___x_2895_, 1);
v_toConstantVal_2896_ = lean_ctor_get(v_a_2889_, 0);
lean_inc_ref(v_toConstantVal_2896_);
lean_dec(v_a_2889_);
v_name_2897_ = lean_ctor_get(v_toConstantVal_2896_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_toConstantVal_2896_);
if (v_isSharedCheck_3183_ == 0)
{
lean_object* v_unused_3184_; lean_object* v_unused_3185_; 
v_unused_3184_ = lean_ctor_get(v_toConstantVal_2896_, 2);
lean_dec(v_unused_3184_);
v_unused_3185_ = lean_ctor_get(v_toConstantVal_2896_, 1);
lean_dec(v_unused_3185_);
v___x_2899_ = v_toConstantVal_2896_;
v_isShared_2900_ = v_isSharedCheck_3183_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_name_2897_);
lean_dec(v_toConstantVal_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_3183_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_env_2903_; lean_object* v_nextMacroScope_2904_; lean_object* v_ngen_2905_; lean_object* v_auxDeclNGen_2906_; lean_object* v_traceState_2907_; lean_object* v_messages_2908_; lean_object* v_infoState_2909_; lean_object* v_snapshotTasks_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_3181_; 
lean_inc(v_name_2897_);
v___x_2901_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2897_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec_ref(v___x_2901_);
v___x_2902_ = lean_st_ref_take(v___y_2851_);
v_env_2903_ = lean_ctor_get(v___x_2902_, 0);
v_nextMacroScope_2904_ = lean_ctor_get(v___x_2902_, 1);
v_ngen_2905_ = lean_ctor_get(v___x_2902_, 2);
v_auxDeclNGen_2906_ = lean_ctor_get(v___x_2902_, 3);
v_traceState_2907_ = lean_ctor_get(v___x_2902_, 4);
v_messages_2908_ = lean_ctor_get(v___x_2902_, 6);
v_infoState_2909_ = lean_ctor_get(v___x_2902_, 7);
v_snapshotTasks_2910_ = lean_ctor_get(v___x_2902_, 8);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; 
v_unused_3182_ = lean_ctor_get(v___x_2902_, 5);
lean_dec(v_unused_3182_);
v___x_2912_ = v___x_2902_;
v_isShared_2913_ = v_isSharedCheck_3181_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_snapshotTasks_2910_);
lean_inc(v_infoState_2909_);
lean_inc(v_messages_2908_);
lean_inc(v_traceState_2907_);
lean_inc(v_auxDeclNGen_2906_);
lean_inc(v_ngen_2905_);
lean_inc(v_nextMacroScope_2904_);
lean_inc(v_env_2903_);
lean_dec(v___x_2902_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_3181_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2917_; 
v___x_2914_ = l_Lean_addProtected(v_env_2903_, v_name_2897_);
v___x_2915_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 5, v___x_2915_);
lean_ctor_set(v___x_2912_, 0, v___x_2914_);
v___x_2917_ = v___x_2912_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_2914_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_nextMacroScope_2904_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v_ngen_2905_);
lean_ctor_set(v_reuseFailAlloc_3180_, 3, v_auxDeclNGen_2906_);
lean_ctor_set(v_reuseFailAlloc_3180_, 4, v_traceState_2907_);
lean_ctor_set(v_reuseFailAlloc_3180_, 5, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3180_, 6, v_messages_2908_);
lean_ctor_set(v_reuseFailAlloc_3180_, 7, v_infoState_2909_);
lean_ctor_set(v_reuseFailAlloc_3180_, 8, v_snapshotTasks_2910_);
v___x_2917_ = v_reuseFailAlloc_3180_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v_mctx_2920_; lean_object* v_zetaDeltaFVarIds_2921_; lean_object* v_postponed_2922_; lean_object* v_diag_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_3178_; 
v___x_2918_ = lean_st_ref_put(v___y_2851_, v___x_2917_);
v___x_2919_ = lean_st_ref_take(v___y_2849_);
v_mctx_2920_ = lean_ctor_get(v___x_2919_, 0);
v_zetaDeltaFVarIds_2921_ = lean_ctor_get(v___x_2919_, 2);
v_postponed_2922_ = lean_ctor_get(v___x_2919_, 3);
v_diag_2923_ = lean_ctor_get(v___x_2919_, 4);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3178_ == 0)
{
lean_object* v_unused_3179_; 
v_unused_3179_ = lean_ctor_get(v___x_2919_, 1);
lean_dec(v_unused_3179_);
v___x_2925_ = v___x_2919_;
v_isShared_2926_ = v_isSharedCheck_3178_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_diag_2923_);
lean_inc(v_postponed_2922_);
lean_inc(v_zetaDeltaFVarIds_2921_);
lean_inc(v_mctx_2920_);
lean_dec(v___x_2919_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_3178_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2927_; lean_object* v___x_2929_; 
v___x_2927_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2927_);
v___x_2929_ = v___x_2925_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_mctx_2920_);
lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_zetaDeltaFVarIds_2921_);
lean_ctor_set(v_reuseFailAlloc_3177_, 3, v_postponed_2922_);
lean_ctor_set(v_reuseFailAlloc_3177_, 4, v_diag_2923_);
v___x_2929_ = v_reuseFailAlloc_3177_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2930_ = lean_st_ref_put(v___y_2849_, v___x_2929_);
lean_inc(v___x_2843_);
v___x_2931_ = l_Lean_Expr_const___override(v_brecOnGoName_2841_, v___x_2843_);
v___x_2932_ = l_Lean_mkAppN(v___x_2931_, v___x_2880_);
lean_inc_ref(v___x_2932_);
v___x_2933_ = l_Lean_Meta_mkPProdFstM(v___x_2932_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2935_ = l_Lean_Meta_mkLambdaFVars(v___x_2880_, v_a_2934_, v___x_2881_, v___x_2840_, v___x_2881_, v___x_2840_, v___x_2882_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = l_Lean_Meta_mkForallFVars(v___x_2880_, v___x_2874_, v___x_2881_, v___x_2840_, v___x_2840_, v___x_2882_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_3152_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
lean_inc(v_levelParams_2842_);
v___x_2939_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2844_, v_levelParams_2842_, v_a_2938_, v_a_2936_, v___x_2887_, v___y_2851_);
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_2942_ = v___x_2939_;
v_isShared_2943_ = v_isSharedCheck_3152_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2939_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_3152_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
lean_inc(v_a_2940_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set_tag(v___x_2942_, 1);
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_3151_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_Lean_addDecl(v___x_2945_, v___x_2881_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_2946_) == 0)
{
lean_object* v_toConstantVal_2947_; lean_object* v_name_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref_known(v___x_2946_, 1);
v_toConstantVal_2947_ = lean_ctor_get(v_a_2940_, 0);
lean_inc_ref(v_toConstantVal_2947_);
lean_dec(v_a_2940_);
v_name_2948_ = lean_ctor_get(v_toConstantVal_2947_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_toConstantVal_2947_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3149_ = lean_ctor_get(v_toConstantVal_2947_, 2);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_toConstantVal_2947_, 1);
lean_dec(v_unused_3150_);
v___x_2950_ = v_toConstantVal_2947_;
v_isShared_2951_ = v_isSharedCheck_3148_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_name_2948_);
lean_dec(v_toConstantVal_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_3148_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_env_2954_; lean_object* v_nextMacroScope_2955_; lean_object* v_ngen_2956_; lean_object* v_auxDeclNGen_2957_; lean_object* v_traceState_2958_; lean_object* v_messages_2959_; lean_object* v_infoState_2960_; lean_object* v_snapshotTasks_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3146_; 
lean_inc(v_name_2948_);
v___x_2952_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2948_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec_ref(v___x_2952_);
v___x_2953_ = lean_st_ref_take(v___y_2851_);
v_env_2954_ = lean_ctor_get(v___x_2953_, 0);
v_nextMacroScope_2955_ = lean_ctor_get(v___x_2953_, 1);
v_ngen_2956_ = lean_ctor_get(v___x_2953_, 2);
v_auxDeclNGen_2957_ = lean_ctor_get(v___x_2953_, 3);
v_traceState_2958_ = lean_ctor_get(v___x_2953_, 4);
v_messages_2959_ = lean_ctor_get(v___x_2953_, 6);
v_infoState_2960_ = lean_ctor_get(v___x_2953_, 7);
v_snapshotTasks_2961_ = lean_ctor_get(v___x_2953_, 8);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v___x_2953_, 5);
lean_dec(v_unused_3147_);
v___x_2963_ = v___x_2953_;
v_isShared_2964_ = v_isSharedCheck_3146_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snapshotTasks_2961_);
lean_inc(v_infoState_2960_);
lean_inc(v_messages_2959_);
lean_inc(v_traceState_2958_);
lean_inc(v_auxDeclNGen_2957_);
lean_inc(v_ngen_2956_);
lean_inc(v_nextMacroScope_2955_);
lean_inc(v_env_2954_);
lean_dec(v___x_2953_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3146_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2967_; 
lean_inc(v_name_2948_);
v___x_2965_ = l_Lean_markAuxRecursor(v_env_2954_, v_name_2948_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 5, v___x_2915_);
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2967_ = v___x_2963_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_nextMacroScope_2955_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_ngen_2956_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_auxDeclNGen_2957_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_traceState_2958_);
lean_ctor_set(v_reuseFailAlloc_3145_, 5, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3145_, 6, v_messages_2959_);
lean_ctor_set(v_reuseFailAlloc_3145_, 7, v_infoState_2960_);
lean_ctor_set(v_reuseFailAlloc_3145_, 8, v_snapshotTasks_2961_);
v___x_2967_ = v_reuseFailAlloc_3145_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v_mctx_2970_; lean_object* v_zetaDeltaFVarIds_2971_; lean_object* v_postponed_2972_; lean_object* v_diag_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3143_; 
v___x_2968_ = lean_st_ref_put(v___y_2851_, v___x_2967_);
v___x_2969_ = lean_st_ref_take(v___y_2849_);
v_mctx_2970_ = lean_ctor_get(v___x_2969_, 0);
v_zetaDeltaFVarIds_2971_ = lean_ctor_get(v___x_2969_, 2);
v_postponed_2972_ = lean_ctor_get(v___x_2969_, 3);
v_diag_2973_ = lean_ctor_get(v___x_2969_, 4);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; 
v_unused_3144_ = lean_ctor_get(v___x_2969_, 1);
lean_dec(v_unused_3144_);
v___x_2975_ = v___x_2969_;
v_isShared_2976_ = v_isSharedCheck_3143_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_diag_2973_);
lean_inc(v_postponed_2972_);
lean_inc(v_zetaDeltaFVarIds_2971_);
lean_inc(v_mctx_2970_);
lean_dec(v___x_2969_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3143_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 1, v___x_2927_);
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_mctx_2970_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_zetaDeltaFVarIds_2971_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_postponed_2972_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v_diag_2973_);
v___x_2978_ = v_reuseFailAlloc_3142_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_env_2981_; lean_object* v_nextMacroScope_2982_; lean_object* v_ngen_2983_; lean_object* v_auxDeclNGen_2984_; lean_object* v_traceState_2985_; lean_object* v_messages_2986_; lean_object* v_infoState_2987_; lean_object* v_snapshotTasks_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3140_; 
v___x_2979_ = lean_st_ref_put(v___y_2849_, v___x_2978_);
v___x_2980_ = lean_st_ref_take(v___y_2851_);
v_env_2981_ = lean_ctor_get(v___x_2980_, 0);
v_nextMacroScope_2982_ = lean_ctor_get(v___x_2980_, 1);
v_ngen_2983_ = lean_ctor_get(v___x_2980_, 2);
v_auxDeclNGen_2984_ = lean_ctor_get(v___x_2980_, 3);
v_traceState_2985_ = lean_ctor_get(v___x_2980_, 4);
v_messages_2986_ = lean_ctor_get(v___x_2980_, 6);
v_infoState_2987_ = lean_ctor_get(v___x_2980_, 7);
v_snapshotTasks_2988_ = lean_ctor_get(v___x_2980_, 8);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_2980_, 5);
lean_dec(v_unused_3141_);
v___x_2990_ = v___x_2980_;
v_isShared_2991_ = v_isSharedCheck_3140_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_snapshotTasks_2988_);
lean_inc(v_infoState_2987_);
lean_inc(v_messages_2986_);
lean_inc(v_traceState_2985_);
lean_inc(v_auxDeclNGen_2984_);
lean_inc(v_ngen_2983_);
lean_inc(v_nextMacroScope_2982_);
lean_inc(v_env_2981_);
lean_dec(v___x_2980_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3140_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_inc(v_name_2948_);
v___x_2992_ = l_Lean_addProtected(v_env_2981_, v_name_2948_);
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 5, v___x_2915_);
lean_ctor_set(v___x_2990_, 0, v___x_2992_);
v___x_2994_ = v___x_2990_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v_nextMacroScope_2982_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_ngen_2983_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_auxDeclNGen_2984_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_traceState_2985_);
lean_ctor_set(v_reuseFailAlloc_3139_, 5, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3139_, 6, v_messages_2986_);
lean_ctor_set(v_reuseFailAlloc_3139_, 7, v_infoState_2987_);
lean_ctor_set(v_reuseFailAlloc_3139_, 8, v_snapshotTasks_2988_);
v___x_2994_ = v_reuseFailAlloc_3139_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_mctx_2997_; lean_object* v_zetaDeltaFVarIds_2998_; lean_object* v_postponed_2999_; lean_object* v_diag_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3137_; 
v___x_2995_ = lean_st_ref_put(v___y_2851_, v___x_2994_);
v___x_2996_ = lean_st_ref_take(v___y_2849_);
v_mctx_2997_ = lean_ctor_get(v___x_2996_, 0);
v_zetaDeltaFVarIds_2998_ = lean_ctor_get(v___x_2996_, 2);
v_postponed_2999_ = lean_ctor_get(v___x_2996_, 3);
v_diag_3000_ = lean_ctor_get(v___x_2996_, 4);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_2996_, 1);
lean_dec(v_unused_3138_);
v___x_3002_ = v___x_2996_;
v_isShared_3003_ = v_isSharedCheck_3137_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_diag_3000_);
lean_inc(v_postponed_2999_);
lean_inc(v_zetaDeltaFVarIds_2998_);
lean_inc(v_mctx_2997_);
lean_dec(v___x_2996_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3137_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set(v___x_3002_, 1, v___x_2927_);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_mctx_2997_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_zetaDeltaFVarIds_2998_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_postponed_2999_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_diag_3000_);
v___x_3005_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_st_ref_put(v___y_2849_, v___x_3005_);
v___x_3007_ = l_Lean_Meta_mkPProdSndM(v___x_2932_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
v___x_3009_ = l_Lean_Expr_const___override(v_name_2948_, v___x_2843_);
v___x_3010_ = l_Lean_mkAppN(v___x_3009_, v___x_2880_);
v___x_3011_ = lean_array_get(v___x_2838_, v_fs_2847_, v_val_2839_);
lean_dec_ref(v_fs_2847_);
v___x_3012_ = l_Lean_mkAppN(v___x_3011_, v___x_2873_);
lean_dec_ref(v___x_2873_);
v___x_3013_ = l_Lean_Expr_app___override(v___x_3012_, v_a_3008_);
v___x_3014_ = l_Lean_Meta_mkEq(v___x_3010_, v___x_3013_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc_n(v_a_3015_, 2);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_box(0);
v___x_3017_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3015_, v___x_3016_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_Expr_mvarId_x21(v_a_3018_);
v___x_3020_ = l_Lean_Expr_fvarId_x21(v___x_2836_);
lean_dec_ref(v___x_2836_);
v___x_3021_ = lean_mk_empty_array_with_capacity(v___x_2845_);
v___x_3022_ = lean_box(0);
v___x_3023_ = l_Lean_MVarId_cases(v___x_3019_, v___x_3020_, v___x_3021_, v___x_2881_, v___x_3022_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3025_; size_t v_sz_3026_; lean_object* v___x_3027_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
v___x_3025_ = lean_box(0);
v_sz_3026_ = lean_array_size(v_a_3024_);
v___x_3027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3024_, v_sz_3026_, v___x_2832_, v___x_3025_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec(v_a_3024_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v___x_3028_; lean_object* v_a_3029_; lean_object* v___x_3030_; 
lean_dec_ref_known(v___x_3027_, 1);
v___x_3028_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_3018_, v___y_2849_);
v_a_3029_ = lean_ctor_get(v___x_3028_, 0);
lean_inc(v_a_3029_);
lean_dec_ref(v___x_3028_);
v___x_3030_ = l_Lean_Meta_mkForallFVars(v___x_2880_, v_a_3015_, v___x_2881_, v___x_2840_, v___x_2840_, v___x_2882_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v___x_3032_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v___x_3032_ = l_Lean_Meta_mkLambdaFVars(v___x_2880_, v_a_3029_, v___x_2881_, v___x_2840_, v___x_2881_, v___x_2840_, v___x_2882_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
lean_dec_ref(v___x_2880_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
lean_inc(v_brecOnEqName_2846_);
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 2, v_a_3031_);
lean_ctor_set(v___x_2950_, 1, v_levelParams_2842_);
lean_ctor_set(v___x_2950_, 0, v_brecOnEqName_2846_);
v___x_3035_ = v___x_2950_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_brecOnEqName_2846_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_levelParams_2842_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_a_3031_);
v___x_3035_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3036_ = lean_box(0);
lean_inc(v_brecOnEqName_2846_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set_tag(v___x_2861_, 1);
lean_ctor_set(v___x_2861_, 1, v___x_3036_);
lean_ctor_set(v___x_2861_, 0, v_brecOnEqName_2846_);
v___x_3038_ = v___x_2861_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_brecOnEqName_2846_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3040_; 
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 2, v___x_3038_);
lean_ctor_set(v___x_2899_, 1, v_a_3033_);
lean_ctor_set(v___x_2899_, 0, v___x_3035_);
v___x_3040_ = v___x_2899_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v_a_3033_);
lean_ctor_set(v_reuseFailAlloc_3085_, 2, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_object* v___x_3041_; lean_object* v_a_3042_; lean_object* v___x_3043_; 
v___x_3041_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3040_, v___y_2851_);
v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
lean_inc(v_a_3042_);
lean_dec_ref(v___x_3041_);
v___x_3043_ = l_Lean_addDecl(v_a_3042_, v___x_2881_, v___y_2850_, v___y_2851_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3083_; 
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; 
v_unused_3084_ = lean_ctor_get(v___x_3043_, 0);
lean_dec(v_unused_3084_);
v___x_3045_ = v___x_3043_;
v_isShared_3046_ = v_isSharedCheck_3083_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3043_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3083_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3047_; lean_object* v_env_3048_; lean_object* v_nextMacroScope_3049_; lean_object* v_ngen_3050_; lean_object* v_auxDeclNGen_3051_; lean_object* v_traceState_3052_; lean_object* v_messages_3053_; lean_object* v_infoState_3054_; lean_object* v_snapshotTasks_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3081_; 
v___x_3047_ = lean_st_ref_take(v___y_2851_);
v_env_3048_ = lean_ctor_get(v___x_3047_, 0);
v_nextMacroScope_3049_ = lean_ctor_get(v___x_3047_, 1);
v_ngen_3050_ = lean_ctor_get(v___x_3047_, 2);
v_auxDeclNGen_3051_ = lean_ctor_get(v___x_3047_, 3);
v_traceState_3052_ = lean_ctor_get(v___x_3047_, 4);
v_messages_3053_ = lean_ctor_get(v___x_3047_, 6);
v_infoState_3054_ = lean_ctor_get(v___x_3047_, 7);
v_snapshotTasks_3055_ = lean_ctor_get(v___x_3047_, 8);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3047_, 5);
lean_dec(v_unused_3082_);
v___x_3057_ = v___x_3047_;
v_isShared_3058_ = v_isSharedCheck_3081_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_snapshotTasks_3055_);
lean_inc(v_infoState_3054_);
lean_inc(v_messages_3053_);
lean_inc(v_traceState_3052_);
lean_inc(v_auxDeclNGen_3051_);
lean_inc(v_ngen_3050_);
lean_inc(v_nextMacroScope_3049_);
lean_inc(v_env_3048_);
lean_dec(v___x_3047_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3081_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3059_ = l_Lean_addProtected(v_env_3048_, v_brecOnEqName_2846_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 5, v___x_2915_);
lean_ctor_set(v___x_3057_, 0, v___x_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3059_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v_nextMacroScope_3049_);
lean_ctor_set(v_reuseFailAlloc_3080_, 2, v_ngen_3050_);
lean_ctor_set(v_reuseFailAlloc_3080_, 3, v_auxDeclNGen_3051_);
lean_ctor_set(v_reuseFailAlloc_3080_, 4, v_traceState_3052_);
lean_ctor_set(v_reuseFailAlloc_3080_, 5, v___x_2915_);
lean_ctor_set(v_reuseFailAlloc_3080_, 6, v_messages_3053_);
lean_ctor_set(v_reuseFailAlloc_3080_, 7, v_infoState_3054_);
lean_ctor_set(v_reuseFailAlloc_3080_, 8, v_snapshotTasks_3055_);
v___x_3061_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v_mctx_3064_; lean_object* v_zetaDeltaFVarIds_3065_; lean_object* v_postponed_3066_; lean_object* v_diag_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3078_; 
v___x_3062_ = lean_st_ref_put(v___y_2851_, v___x_3061_);
v___x_3063_ = lean_st_ref_take(v___y_2849_);
v_mctx_3064_ = lean_ctor_get(v___x_3063_, 0);
v_zetaDeltaFVarIds_3065_ = lean_ctor_get(v___x_3063_, 2);
v_postponed_3066_ = lean_ctor_get(v___x_3063_, 3);
v_diag_3067_ = lean_ctor_get(v___x_3063_, 4);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; 
v_unused_3079_ = lean_ctor_get(v___x_3063_, 1);
lean_dec(v_unused_3079_);
v___x_3069_ = v___x_3063_;
v_isShared_3070_ = v_isSharedCheck_3078_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_diag_3067_);
lean_inc(v_postponed_3066_);
lean_inc(v_zetaDeltaFVarIds_3065_);
lean_inc(v_mctx_3064_);
lean_dec(v___x_3063_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3078_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v___x_2927_);
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_mctx_3064_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_3077_, 2, v_zetaDeltaFVarIds_3065_);
lean_ctor_set(v_reuseFailAlloc_3077_, 3, v_postponed_3066_);
lean_ctor_set(v_reuseFailAlloc_3077_, 4, v_diag_3067_);
v___x_3072_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
v___x_3073_ = lean_st_ref_put(v___y_2849_, v___x_3072_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3025_);
v___x_3075_ = v___x_3045_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3025_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2846_);
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v_a_3031_);
lean_del_object(v___x_2950_);
lean_del_object(v___x_2899_);
lean_del_object(v___x_2861_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_levelParams_2842_);
v_a_3088_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3032_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3032_);
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
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3029_);
lean_del_object(v___x_2950_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_del_object(v___x_2861_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_levelParams_2842_);
v_a_3096_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3030_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3030_);
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
lean_dec(v_a_3018_);
lean_dec(v_a_3015_);
lean_del_object(v___x_2950_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_del_object(v___x_2861_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_levelParams_2842_);
return v___x_3027_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_3018_);
lean_dec(v_a_3015_);
lean_del_object(v___x_2950_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_del_object(v___x_2861_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_levelParams_2842_);
v_a_3104_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3023_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3023_);
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
lean_dec(v_a_3015_);
lean_del_object(v___x_2950_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_del_object(v___x_2861_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_levelParams_2842_);
lean_dec_ref(v___x_2836_);
v_a_3112_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3017_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3017_);
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
lean_del_object(v___x_2950_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_del_object(v___x_2861_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_levelParams_2842_);
lean_dec_ref(v___x_2836_);
v_a_3120_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3014_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3014_);
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
lean_del_object(v___x_2950_);
lean_dec(v_name_2948_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec_ref(v___x_2836_);
v_a_3128_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3007_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3007_);
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
lean_dec(v_a_2940_);
lean_dec_ref(v___x_2932_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec_ref(v___x_2836_);
return v___x_2946_;
}
}
}
}
else
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v_a_2936_);
lean_dec_ref(v___x_2932_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec_ref(v___x_2836_);
v_a_3153_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3155_ = v___x_2937_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_2937_);
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
lean_dec_ref(v___x_2932_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec_ref(v___x_2836_);
v_a_3161_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_2935_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_2935_);
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
lean_dec_ref(v___x_2932_);
lean_del_object(v___x_2899_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec_ref(v___x_2836_);
v_a_3169_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_2933_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_2933_);
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
}
}
}
}
}
else
{
lean_dec(v_a_2889_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec(v_brecOnGoName_2841_);
lean_dec_ref(v___x_2836_);
return v___x_2895_;
}
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v_a_2884_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec(v_brecOnGoName_2841_);
lean_dec_ref(v___x_2836_);
v_a_3188_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_2885_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_2885_);
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
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2867_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec(v_brecOnGoName_2841_);
lean_dec_ref(v___x_2836_);
v_a_3196_ = lean_ctor_get(v___x_2883_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_2883_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_2883_);
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
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2873_);
lean_dec_ref(v___x_2871_);
lean_dec_ref(v___x_2869_);
lean_dec_ref(v___x_2867_);
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec(v_brecOnGoName_2841_);
lean_dec_ref(v___x_2836_);
v_a_3204_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_2877_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_2877_);
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
lean_del_object(v___x_2861_);
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec(v_brecOnGoName_2841_);
lean_dec_ref(v___x_2836_);
lean_dec_ref(v___x_2835_);
lean_dec_ref(v___x_2834_);
lean_dec_ref(v___x_2830_);
lean_dec_ref(v___x_2826_);
v_a_3212_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_2864_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_2864_);
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
else
{
lean_object* v_a_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3229_; 
lean_dec_ref(v_fs_2847_);
lean_dec(v_brecOnEqName_2846_);
lean_dec(v_brecOnName_2844_);
lean_dec(v___x_2843_);
lean_dec(v_levelParams_2842_);
lean_dec(v_brecOnGoName_2841_);
lean_dec_ref(v___x_2836_);
lean_dec_ref(v___x_2835_);
lean_dec_ref(v___x_2834_);
lean_dec_ref(v___x_2830_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2823_);
v_a_3222_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_2857_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_2857_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3230_ = _args[0];
lean_object* v_tail_3231_ = _args[1];
lean_object* v_recName_3232_ = _args[2];
lean_object* v___x_3233_ = _args[3];
lean_object* v___x_3234_ = _args[4];
lean_object* v___x_3235_ = _args[5];
lean_object* v___x_3236_ = _args[6];
lean_object* v___x_3237_ = _args[7];
lean_object* v_sz_3238_ = _args[8];
lean_object* v___x_3239_ = _args[9];
lean_object* v___x_3240_ = _args[10];
lean_object* v___x_3241_ = _args[11];
lean_object* v___x_3242_ = _args[12];
lean_object* v___x_3243_ = _args[13];
lean_object* v___x_3244_ = _args[14];
lean_object* v___x_3245_ = _args[15];
lean_object* v_val_3246_ = _args[16];
lean_object* v___x_3247_ = _args[17];
lean_object* v_brecOnGoName_3248_ = _args[18];
lean_object* v_levelParams_3249_ = _args[19];
lean_object* v___x_3250_ = _args[20];
lean_object* v_brecOnName_3251_ = _args[21];
lean_object* v___x_3252_ = _args[22];
lean_object* v_brecOnEqName_3253_ = _args[23];
lean_object* v_fs_3254_ = _args[24];
lean_object* v___y_3255_ = _args[25];
lean_object* v___y_3256_ = _args[26];
lean_object* v___y_3257_ = _args[27];
lean_object* v___y_3258_ = _args[28];
lean_object* v___y_3259_ = _args[29];
_start:
{
size_t v_sz_boxed_3260_; size_t v___x_30618__boxed_3261_; uint8_t v___x_30626__boxed_3262_; lean_object* v_res_3263_; 
v_sz_boxed_3260_ = lean_unbox_usize(v_sz_3238_);
lean_dec(v_sz_3238_);
v___x_30618__boxed_3261_ = lean_unbox_usize(v___x_3239_);
lean_dec(v___x_3239_);
v___x_30626__boxed_3262_ = lean_unbox(v___x_3247_);
v_res_3263_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3230_, v_tail_3231_, v_recName_3232_, v___x_3233_, v___x_3234_, v___x_3235_, v___x_3236_, v___x_3237_, v_sz_boxed_3260_, v___x_30618__boxed_3261_, v___x_3240_, v___x_3241_, v___x_3242_, v___x_3243_, v___x_3244_, v___x_3245_, v_val_3246_, v___x_30626__boxed_3262_, v_brecOnGoName_3248_, v_levelParams_3249_, v___x_3250_, v_brecOnName_3251_, v___x_3252_, v_brecOnEqName_3253_, v_fs_3254_, v___y_3255_, v___y_3256_, v___y_3257_, v___y_3258_);
lean_dec(v___y_3258_);
lean_dec_ref(v___y_3257_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___x_3252_);
lean_dec(v_val_3246_);
lean_dec_ref(v___x_3245_);
lean_dec(v___x_3244_);
lean_dec_ref(v___x_3240_);
lean_dec(v___x_3236_);
lean_dec(v___x_3235_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3264_, lean_object* v_a_3265_, uint8_t v___x_3266_, lean_object* v_f_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; uint8_t v___x_3276_; lean_object* v___x_3277_; 
lean_inc_ref(v_targs_3264_);
v___x_3273_ = lean_array_push(v_targs_3264_, v_f_3267_);
v___x_3274_ = l_Lean_mkAppN(v_a_3265_, v_targs_3264_);
lean_dec_ref(v_targs_3264_);
v___x_3275_ = 0;
v___x_3276_ = 1;
v___x_3277_ = l_Lean_Meta_mkForallFVars(v___x_3273_, v___x_3274_, v___x_3275_, v___x_3266_, v___x_3266_, v___x_3276_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec_ref(v___x_3273_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3278_, lean_object* v_a_3279_, lean_object* v___x_3280_, lean_object* v_f_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v___x_31340__boxed_3287_; lean_object* v_res_3288_; 
v___x_31340__boxed_3287_ = lean_unbox(v___x_3280_);
v_res_3288_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3278_, v_a_3279_, v___x_31340__boxed_3287_, v_f_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3292_, uint8_t v___x_3293_, lean_object* v___x_3294_, lean_object* v_targs_3295_, lean_object* v_x_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_){
_start:
{
lean_object* v___x_3302_; lean_object* v___f_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3302_ = lean_box(v___x_3293_);
lean_inc_ref(v_targs_3295_);
v___f_3303_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3303_, 0, v_targs_3295_);
lean_closure_set(v___f_3303_, 1, v_a_3292_);
lean_closure_set(v___f_3303_, 2, v___x_3302_);
v___x_3304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3305_ = l_Lean_mkAppN(v___x_3294_, v_targs_3295_);
lean_dec_ref(v_targs_3295_);
v___x_3306_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3304_, v___x_3305_, v___f_3303_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3307_, lean_object* v___x_3308_, lean_object* v___x_3309_, lean_object* v_targs_3310_, lean_object* v_x_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
uint8_t v___x_31374__boxed_3317_; lean_object* v_res_3318_; 
v___x_31374__boxed_3317_ = lean_unbox(v___x_3308_);
v_res_3318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3307_, v___x_31374__boxed_3317_, v___x_3309_, v_targs_3310_, v_x_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec_ref(v_x_3311_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3319_, lean_object* v_x_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_a_3319_);
return v___x_3326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3327_, lean_object* v_x_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3327_, v_x_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec_ref(v_x_3328_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_3336_, lean_object* v___x_3337_, lean_object* v_as_3338_, size_t v_sz_3339_, size_t v_i_3340_, lean_object* v_b_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v___x_3347_; 
v___x_3347_ = lean_usize_dec_lt(v_i_3340_, v_sz_3339_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; 
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v_b_3341_);
return v___x_3348_;
}
else
{
lean_object* v_snd_3349_; lean_object* v_fst_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3447_; 
v_snd_3349_ = lean_ctor_get(v_b_3341_, 1);
v_fst_3350_ = lean_ctor_get(v_b_3341_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_b_3341_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3352_ = v_b_3341_;
v_isShared_3353_ = v_isSharedCheck_3447_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snd_3349_);
lean_inc(v_fst_3350_);
lean_dec(v_b_3341_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3447_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v_fst_3354_; lean_object* v_snd_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3446_; 
v_fst_3354_ = lean_ctor_get(v_snd_3349_, 0);
v_snd_3355_ = lean_ctor_get(v_snd_3349_, 1);
v_isSharedCheck_3446_ = !lean_is_exclusive(v_snd_3349_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3357_ = v_snd_3349_;
v_isShared_3358_ = v_isSharedCheck_3446_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_snd_3355_);
lean_inc(v_fst_3354_);
lean_dec(v_snd_3349_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3446_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v_next_3367_; 
v_next_3367_ = lean_ctor_get(v_snd_3355_, 0);
lean_inc(v_next_3367_);
if (lean_obj_tag(v_next_3367_) == 0)
{
goto v___jp_3359_;
}
else
{
lean_object* v_upperBound_3368_; lean_object* v_val_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3445_; 
v_upperBound_3368_ = lean_ctor_get(v_snd_3355_, 1);
v_val_3369_ = lean_ctor_get(v_next_3367_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_next_3367_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3371_ = v_next_3367_;
v_isShared_3372_ = v_isSharedCheck_3445_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_val_3369_);
lean_dec(v_next_3367_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3445_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_nat_dec_lt(v_val_3369_, v_upperBound_3368_);
if (v___x_3373_ == 0)
{
lean_del_object(v___x_3371_);
lean_dec(v_val_3369_);
goto v___jp_3359_;
}
else
{
lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3442_; 
lean_inc(v_upperBound_3368_);
lean_del_object(v___x_3357_);
lean_del_object(v___x_3352_);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_snd_3355_);
if (v_isSharedCheck_3442_ == 0)
{
lean_object* v_unused_3443_; lean_object* v_unused_3444_; 
v_unused_3443_ = lean_ctor_get(v_snd_3355_, 1);
lean_dec(v_unused_3443_);
v_unused_3444_ = lean_ctor_get(v_snd_3355_, 0);
lean_dec(v_unused_3444_);
v___x_3375_ = v_snd_3355_;
v_isShared_3376_ = v_isSharedCheck_3442_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v_snd_3355_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3442_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v_array_3377_; lean_object* v_start_3378_; lean_object* v_stop_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v_array_3377_ = lean_ctor_get(v_fst_3354_, 0);
v_start_3378_ = lean_ctor_get(v_fst_3354_, 1);
v_stop_3379_ = lean_ctor_get(v_fst_3354_, 2);
v___x_3380_ = lean_unsigned_to_nat(1u);
v___x_3381_ = lean_nat_add(v_val_3369_, v___x_3380_);
lean_dec(v_val_3369_);
lean_inc(v___x_3381_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3381_);
v___x_3383_ = v___x_3371_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 0, v___x_3383_);
v___x_3385_ = v___x_3375_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3440_, 1, v_upperBound_3368_);
v___x_3385_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
uint8_t v___x_3386_; 
v___x_3386_ = lean_nat_dec_lt(v_start_3378_, v_stop_3379_);
if (v___x_3386_ == 0)
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
lean_dec(v___x_3381_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_fst_3354_);
lean_ctor_set(v___x_3387_, 1, v___x_3385_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_fst_3350_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
return v___x_3389_;
}
else
{
lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3436_; 
lean_inc(v_stop_3379_);
lean_inc(v_start_3378_);
lean_inc_ref(v_array_3377_);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_fst_3354_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; lean_object* v_unused_3438_; lean_object* v_unused_3439_; 
v_unused_3437_ = lean_ctor_get(v_fst_3354_, 2);
lean_dec(v_unused_3437_);
v_unused_3438_ = lean_ctor_get(v_fst_3354_, 1);
lean_dec(v_unused_3438_);
v_unused_3439_ = lean_ctor_get(v_fst_3354_, 0);
lean_dec(v_unused_3439_);
v___x_3391_ = v_fst_3354_;
v_isShared_3392_ = v_isSharedCheck_3436_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v_fst_3354_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3436_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v_a_3393_; lean_object* v___x_3394_; 
v_a_3393_ = lean_array_uget_borrowed(v_as_3338_, v_i_3340_);
lean_inc(v___y_3345_);
lean_inc_ref(v___y_3344_);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3342_);
lean_inc(v_a_3393_);
v___x_3394_ = lean_infer_type(v_a_3393_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3394_) == 0)
{
lean_object* v_a_3395_; uint8_t v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___f_3399_; uint8_t v___x_3400_; lean_object* v___x_3401_; 
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_a_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___x_3396_ = lean_nat_dec_lt(v___x_3336_, v___x_3337_);
v___x_3397_ = lean_array_fget_borrowed(v_array_3377_, v_start_3378_);
v___x_3398_ = lean_box(v___x_3396_);
lean_inc(v___x_3397_);
lean_inc(v_a_3393_);
v___f_3399_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3399_, 0, v_a_3393_);
lean_closure_set(v___f_3399_, 1, v___x_3398_);
lean_closure_set(v___f_3399_, 2, v___x_3397_);
v___x_3400_ = 0;
v___x_3401_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3395_, v___f_3399_, v___x_3400_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v_a_3402_; lean_object* v___f_3403_; lean_object* v___x_3404_; lean_object* v___x_3406_; 
v_a_3402_ = lean_ctor_get(v___x_3401_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3401_, 1);
v___f_3403_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3403_, 0, v_a_3402_);
v___x_3404_ = lean_nat_add(v_start_3378_, v___x_3380_);
lean_dec(v_start_3378_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 1, v___x_3404_);
v___x_3406_ = v___x_3391_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_array_3377_);
lean_ctor_set(v_reuseFailAlloc_3419_, 1, v___x_3404_);
lean_ctor_set(v_reuseFailAlloc_3419_, 2, v_stop_3379_);
v___x_3406_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; size_t v___x_3416_; size_t v___x_3417_; 
v___x_3407_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3408_ = l_Nat_reprFast(v___x_3381_);
v___x_3409_ = lean_string_append(v___x_3407_, v___x_3408_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = lean_box(0);
v___x_3411_ = l_Lean_Name_str___override(v___x_3410_, v___x_3409_);
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3411_);
lean_ctor_set(v___x_3412_, 1, v___f_3403_);
v___x_3413_ = lean_array_push(v_fst_3350_, v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3406_);
lean_ctor_set(v___x_3414_, 1, v___x_3385_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3413_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = ((size_t)1ULL);
v___x_3417_ = lean_usize_add(v_i_3340_, v___x_3416_);
v_i_3340_ = v___x_3417_;
v_b_3341_ = v___x_3415_;
goto _start;
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_del_object(v___x_3391_);
lean_dec_ref(v___x_3385_);
lean_dec(v___x_3381_);
lean_dec(v_stop_3379_);
lean_dec(v_start_3378_);
lean_dec_ref(v_array_3377_);
lean_dec(v_fst_3350_);
v_a_3420_ = lean_ctor_get(v___x_3401_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3401_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3401_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3401_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_del_object(v___x_3391_);
lean_dec_ref(v___x_3385_);
lean_dec(v___x_3381_);
lean_dec(v_stop_3379_);
lean_dec(v_start_3378_);
lean_dec_ref(v_array_3377_);
lean_dec(v_fst_3350_);
v_a_3428_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3394_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3394_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
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
v___jp_3359_:
{
lean_object* v___x_3361_; 
if (v_isShared_3358_ == 0)
{
v___x_3361_ = v___x_3357_;
goto v_reusejp_3360_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_fst_3354_);
lean_ctor_set(v_reuseFailAlloc_3366_, 1, v_snd_3355_);
v___x_3361_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3360_;
}
v_reusejp_3360_:
{
lean_object* v___x_3363_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 1, v___x_3361_);
v___x_3363_ = v___x_3352_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_fst_3350_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
return v___x_3364_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_3448_, lean_object* v___x_3449_, lean_object* v_as_3450_, lean_object* v_sz_3451_, lean_object* v_i_3452_, lean_object* v_b_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
size_t v_sz_boxed_3459_; size_t v_i_boxed_3460_; lean_object* v_res_3461_; 
v_sz_boxed_3459_ = lean_unbox_usize(v_sz_3451_);
lean_dec(v_sz_3451_);
v_i_boxed_3460_ = lean_unbox_usize(v_i_3452_);
lean_dec(v_i_3452_);
v_res_3461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3448_, v___x_3449_, v_as_3450_, v_sz_boxed_3459_, v_i_boxed_3460_, v_b_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v___y_3455_);
lean_dec_ref(v___y_3454_);
lean_dec_ref(v_as_3450_);
lean_dec(v___x_3449_);
lean_dec(v___x_3448_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3462_, size_t v_i_3463_, lean_object* v_bs_3464_){
_start:
{
uint8_t v___x_3465_; 
v___x_3465_ = lean_usize_dec_lt(v_i_3463_, v_sz_3462_);
if (v___x_3465_ == 0)
{
return v_bs_3464_;
}
else
{
lean_object* v_v_3466_; lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3484_; 
v_v_3466_ = lean_array_uget(v_bs_3464_, v_i_3463_);
v_fst_3467_ = lean_ctor_get(v_v_3466_, 0);
v_snd_3468_ = lean_ctor_get(v_v_3466_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_v_3466_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3470_ = v_v_3466_;
v_isShared_3471_ = v_isSharedCheck_3484_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snd_3468_);
lean_inc(v_fst_3467_);
lean_dec(v_v_3466_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3484_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v_bs_x27_3473_; uint8_t v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3477_; 
v___x_3472_ = lean_unsigned_to_nat(0u);
v_bs_x27_3473_ = lean_array_uset(v_bs_3464_, v_i_3463_, v___x_3472_);
v___x_3474_ = 0;
v___x_3475_ = lean_box(v___x_3474_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 0, v___x_3475_);
v___x_3477_ = v___x_3470_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3475_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_snd_3468_);
v___x_3477_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
lean_object* v___x_3478_; size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; 
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_fst_3467_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3463_, v___x_3479_);
v___x_3481_ = lean_array_uset(v_bs_x27_3473_, v_i_3463_, v___x_3478_);
v_i_3463_ = v___x_3480_;
v_bs_3464_ = v___x_3481_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3485_, lean_object* v_i_3486_, lean_object* v_bs_3487_){
_start:
{
size_t v_sz_boxed_3488_; size_t v_i_boxed_3489_; lean_object* v_res_3490_; 
v_sz_boxed_3488_ = lean_unbox_usize(v_sz_3485_);
lean_dec(v_sz_3485_);
v_i_boxed_3489_ = lean_unbox_usize(v_i_3486_);
lean_dec(v_i_3486_);
v_res_3490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3488_, v_i_boxed_3489_, v_bs_3487_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3491_, lean_object* v___x_3492_, lean_object* v_a_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_30168__overap_3499_; lean_object* v___x_3500_; 
v___x_30168__overap_3499_ = l_instInhabitedOfMonad___redArg(v___x_3491_, v___x_3492_);
lean_inc(v___y_3497_);
lean_inc_ref(v___y_3496_);
lean_inc(v___y_3495_);
lean_inc_ref(v___y_3494_);
v___x_3500_ = lean_apply_5(v___x_30168__overap_3499_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, lean_box(0));
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3501_, lean_object* v___x_3502_, lean_object* v_a_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v_res_3509_; 
v_res_3509_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3501_, v___x_3502_, v_a_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_a_3503_);
return v_res_3509_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3510_; 
v___x_3510_ = l_instMonadEIO(lean_box(0));
return v___x_3510_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3512_ = l_StateRefT_x27_instMonad___redArg(v___x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3517_, lean_object* v_declInfos_3518_, lean_object* v_k_3519_, lean_object* v_kind_3520_, lean_object* v_b_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
uint8_t v_kind_boxed_3527_; lean_object* v_res_3528_; 
v_kind_boxed_3527_ = lean_unbox(v_kind_3520_);
v_res_3528_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3517_, v_declInfos_3518_, v_k_3519_, v_kind_boxed_3527_, v_b_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
return v_res_3528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3529_, lean_object* v_declInfos_3530_, lean_object* v_k_3531_, uint8_t v_kind_3532_, lean_object* v_name_3533_, uint8_t v_bi_3534_, lean_object* v_type_3535_, uint8_t v_kind_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; lean_object* v___f_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_box(v_kind_3532_);
v___f_3543_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3543_, 0, v_acc_3529_);
lean_closure_set(v___f_3543_, 1, v_declInfos_3530_);
lean_closure_set(v___f_3543_, 2, v_k_3531_);
lean_closure_set(v___f_3543_, 3, v___x_3542_);
v___x_3544_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3533_, v_bi_3534_, v_type_3535_, v___f_3543_, v_kind_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_a_3553_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3544_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3544_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3561_, lean_object* v_k_3562_, uint8_t v_kind_3563_, lean_object* v_acc_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v___x_3570_; lean_object* v_toApplicative_3571_; lean_object* v_toFunctor_3572_; lean_object* v_toSeq_3573_; lean_object* v_toSeqLeft_3574_; lean_object* v_toSeqRight_3575_; lean_object* v___f_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; lean_object* v___f_3579_; lean_object* v___x_3580_; lean_object* v___f_3581_; lean_object* v___f_3582_; lean_object* v___f_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v_toApplicative_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3643_; 
v___x_3570_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3571_ = lean_ctor_get(v___x_3570_, 0);
v_toFunctor_3572_ = lean_ctor_get(v_toApplicative_3571_, 0);
v_toSeq_3573_ = lean_ctor_get(v_toApplicative_3571_, 2);
v_toSeqLeft_3574_ = lean_ctor_get(v_toApplicative_3571_, 3);
v_toSeqRight_3575_ = lean_ctor_get(v_toApplicative_3571_, 4);
v___f_3576_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3577_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3572_, 2);
v___f_3578_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3578_, 0, v_toFunctor_3572_);
v___f_3579_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3579_, 0, v_toFunctor_3572_);
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___f_3578_);
lean_ctor_set(v___x_3580_, 1, v___f_3579_);
lean_inc(v_toSeqRight_3575_);
v___f_3581_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3581_, 0, v_toSeqRight_3575_);
lean_inc(v_toSeqLeft_3574_);
v___f_3582_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3582_, 0, v_toSeqLeft_3574_);
lean_inc(v_toSeq_3573_);
v___f_3583_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3583_, 0, v_toSeq_3573_);
v___x_3584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3580_);
lean_ctor_set(v___x_3584_, 1, v___f_3576_);
lean_ctor_set(v___x_3584_, 2, v___f_3583_);
lean_ctor_set(v___x_3584_, 3, v___f_3582_);
lean_ctor_set(v___x_3584_, 4, v___f_3581_);
v___x_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___x_3584_);
lean_ctor_set(v___x_3585_, 1, v___f_3577_);
v___x_3586_ = l_StateRefT_x27_instMonad___redArg(v___x_3585_);
v_toApplicative_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3643_ == 0)
{
lean_object* v_unused_3644_; 
v_unused_3644_ = lean_ctor_get(v___x_3586_, 1);
lean_dec(v_unused_3644_);
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3643_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_toApplicative_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3643_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v_toFunctor_3591_; lean_object* v_toSeq_3592_; lean_object* v_toSeqLeft_3593_; lean_object* v_toSeqRight_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3641_; 
v_toFunctor_3591_ = lean_ctor_get(v_toApplicative_3587_, 0);
v_toSeq_3592_ = lean_ctor_get(v_toApplicative_3587_, 2);
v_toSeqLeft_3593_ = lean_ctor_get(v_toApplicative_3587_, 3);
v_toSeqRight_3594_ = lean_ctor_get(v_toApplicative_3587_, 4);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_toApplicative_3587_);
if (v_isSharedCheck_3641_ == 0)
{
lean_object* v_unused_3642_; 
v_unused_3642_ = lean_ctor_get(v_toApplicative_3587_, 1);
lean_dec(v_unused_3642_);
v___x_3596_ = v_toApplicative_3587_;
v_isShared_3597_ = v_isSharedCheck_3641_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_toSeqRight_3594_);
lean_inc(v_toSeqLeft_3593_);
lean_inc(v_toSeq_3592_);
lean_inc(v_toFunctor_3591_);
lean_dec(v_toApplicative_3587_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3641_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___f_3598_; lean_object* v___f_3599_; lean_object* v___f_3600_; lean_object* v___f_3601_; lean_object* v___x_3602_; lean_object* v___f_3603_; lean_object* v___f_3604_; lean_object* v___f_3605_; lean_object* v___x_3607_; 
v___f_3598_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3599_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3591_);
v___f_3600_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3600_, 0, v_toFunctor_3591_);
v___f_3601_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3601_, 0, v_toFunctor_3591_);
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___f_3600_);
lean_ctor_set(v___x_3602_, 1, v___f_3601_);
v___f_3603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3603_, 0, v_toSeqRight_3594_);
v___f_3604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3604_, 0, v_toSeqLeft_3593_);
v___f_3605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3605_, 0, v_toSeq_3592_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 4, v___f_3603_);
lean_ctor_set(v___x_3596_, 3, v___f_3604_);
lean_ctor_set(v___x_3596_, 2, v___f_3605_);
lean_ctor_set(v___x_3596_, 1, v___f_3598_);
lean_ctor_set(v___x_3596_, 0, v___x_3602_);
v___x_3607_ = v___x_3596_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v___f_3598_);
lean_ctor_set(v_reuseFailAlloc_3640_, 2, v___f_3605_);
lean_ctor_set(v_reuseFailAlloc_3640_, 3, v___f_3604_);
lean_ctor_set(v_reuseFailAlloc_3640_, 4, v___f_3603_);
v___x_3607_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
lean_object* v___x_3609_; 
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v___f_3599_);
lean_ctor_set(v___x_3589_, 0, v___x_3607_);
v___x_3609_ = v___x_3589_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v___f_3599_);
v___x_3609_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3610_ = lean_array_get_size(v_acc_3564_);
v___x_3611_ = lean_array_get_size(v_declInfos_3561_);
v___x_3612_ = lean_nat_dec_lt(v___x_3610_, v___x_3611_);
if (v___x_3612_ == 0)
{
lean_object* v___x_3613_; 
lean_dec_ref(v___x_3609_);
lean_dec_ref(v_declInfos_3561_);
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3566_);
lean_inc_ref(v___y_3565_);
v___x_3613_ = lean_apply_6(v_k_3562_, v_acc_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, lean_box(0));
return v___x_3613_;
}
else
{
lean_object* v___x_3614_; uint8_t v___x_3615_; lean_object* v___x_3616_; lean_object* v___f_3617_; lean_object* v___f_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v_snd_3623_; lean_object* v_fst_3624_; lean_object* v_fst_3625_; lean_object* v_snd_3626_; lean_object* v___x_3627_; 
v___x_3614_ = lean_box(0);
v___x_3615_ = 0;
v___x_3616_ = l_Lean_instInhabitedExpr;
v___f_3617_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3617_, 0, v___x_3609_);
lean_closure_set(v___f_3617_, 1, v___x_3616_);
v___f_3618_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3618_, 0, v___f_3617_);
v___x_3619_ = lean_box(v___x_3615_);
v___x_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___f_3618_);
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3614_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = lean_array_get(v___x_3621_, v_declInfos_3561_, v___x_3610_);
lean_dec_ref_known(v___x_3621_, 2);
v_snd_3623_ = lean_ctor_get(v___x_3622_, 1);
lean_inc(v_snd_3623_);
v_fst_3624_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_fst_3624_);
lean_dec(v___x_3622_);
v_fst_3625_ = lean_ctor_get(v_snd_3623_, 0);
lean_inc(v_fst_3625_);
v_snd_3626_ = lean_ctor_get(v_snd_3623_, 1);
lean_inc(v_snd_3626_);
lean_dec(v_snd_3623_);
lean_inc(v___y_3568_);
lean_inc_ref(v___y_3567_);
lean_inc(v___y_3566_);
lean_inc_ref(v___y_3565_);
lean_inc_ref(v_acc_3564_);
v___x_3627_ = lean_apply_6(v_snd_3626_, v_acc_3564_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_, lean_box(0));
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_object* v_a_3628_; uint8_t v___x_3629_; lean_object* v___x_3630_; 
v_a_3628_ = lean_ctor_get(v___x_3627_, 0);
lean_inc(v_a_3628_);
lean_dec_ref_known(v___x_3627_, 1);
v___x_3629_ = lean_unbox(v_fst_3625_);
lean_dec(v_fst_3625_);
v___x_3630_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3564_, v_declInfos_3561_, v_k_3562_, v_kind_3563_, v_fst_3624_, v___x_3629_, v_a_3628_, v_kind_3563_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
return v___x_3630_;
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v_fst_3625_);
lean_dec(v_fst_3624_);
lean_dec_ref(v_acc_3564_);
lean_dec_ref(v_k_3562_);
lean_dec_ref(v_declInfos_3561_);
v_a_3631_ = lean_ctor_get(v___x_3627_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3627_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3627_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3627_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3645_, lean_object* v_declInfos_3646_, lean_object* v_k_3647_, uint8_t v_kind_3648_, lean_object* v_b_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_array_push(v_acc_3645_, v_b_3649_);
v___x_3656_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3646_, v_k_3647_, v_kind_3648_, v___x_3655_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3657_, lean_object* v_declInfos_3658_, lean_object* v_k_3659_, lean_object* v_kind_3660_, lean_object* v_name_3661_, lean_object* v_bi_3662_, lean_object* v_type_3663_, lean_object* v_kind_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
uint8_t v_kind_boxed_3670_; uint8_t v_bi_boxed_3671_; uint8_t v_kind_boxed_3672_; lean_object* v_res_3673_; 
v_kind_boxed_3670_ = lean_unbox(v_kind_3660_);
v_bi_boxed_3671_ = lean_unbox(v_bi_3662_);
v_kind_boxed_3672_ = lean_unbox(v_kind_3664_);
v_res_3673_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3657_, v_declInfos_3658_, v_k_3659_, v_kind_boxed_3670_, v_name_3661_, v_bi_boxed_3671_, v_type_3663_, v_kind_boxed_3672_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3674_, lean_object* v_k_3675_, lean_object* v_kind_3676_, lean_object* v_acc_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
uint8_t v_kind_boxed_3683_; lean_object* v_res_3684_; 
v_kind_boxed_3683_ = lean_unbox(v_kind_3676_);
v_res_3684_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3674_, v_k_3675_, v_kind_boxed_3683_, v_acc_3677_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3685_, lean_object* v_k_3686_, uint8_t v_kind_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3694_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3685_, v_k_3686_, v_kind_3687_, v___x_3693_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3695_, lean_object* v_k_3696_, lean_object* v_kind_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
uint8_t v_kind_boxed_3703_; lean_object* v_res_3704_; 
v_kind_boxed_3703_ = lean_unbox(v_kind_3697_);
v_res_3704_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3695_, v_k_3696_, v_kind_boxed_3703_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3705_, lean_object* v_k_3706_, uint8_t v_kind_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
size_t v_sz_3713_; size_t v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_sz_3713_ = lean_array_size(v_declInfos_3705_);
v___x_3714_ = ((size_t)0ULL);
v___x_3715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3713_, v___x_3714_, v_declInfos_3705_);
v___x_3716_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3715_, v_k_3706_, v_kind_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3717_, lean_object* v_k_3718_, lean_object* v_kind_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
uint8_t v_kind_boxed_3725_; lean_object* v_res_3726_; 
v_kind_boxed_3725_ = lean_unbox(v_kind_3719_);
v_res_3726_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3717_, v_k_3718_, v_kind_boxed_3725_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
return v_res_3726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3728_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3729_ = lean_unsigned_to_nat(4u);
v___x_3730_ = lean_unsigned_to_nat(202u);
v___x_3731_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3732_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3733_ = l_mkPanicMessageWithDecl(v___x_3732_, v___x_3731_, v___x_3730_, v___x_3729_, v___x_3728_);
return v___x_3733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3740_ = l_Lean_stringToMessageData(v___x_3739_);
return v___x_3740_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3743_ = l_Lean_stringToMessageData(v___x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3746_, lean_object* v_numMotives_3747_, lean_object* v_numMinors_3748_, lean_object* v___x_3749_, lean_object* v___x_3750_, lean_object* v_all_3751_, lean_object* v___x_3752_, lean_object* v_head_3753_, lean_object* v_tail_3754_, lean_object* v_recName_3755_, lean_object* v_brecOnGoName_3756_, lean_object* v_levelParams_3757_, lean_object* v_brecOnName_3758_, lean_object* v_brecOnEqName_3759_, lean_object* v_type_3760_, lean_object* v_refArgs_3761_, lean_object* v_refBody_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_){
_start:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v___x_3768_ = lean_nat_add(v_nParams_3746_, v_numMotives_3747_);
v___x_3769_ = lean_nat_add(v___x_3768_, v_numMinors_3748_);
v___x_3770_ = lean_array_get_size(v_refArgs_3761_);
v___x_3771_ = lean_nat_dec_lt(v___x_3769_, v___x_3770_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
lean_dec(v___x_3769_);
lean_dec(v___x_3768_);
lean_dec_ref(v_refArgs_3761_);
lean_dec_ref(v_type_3760_);
lean_dec(v_brecOnEqName_3759_);
lean_dec(v_brecOnName_3758_);
lean_dec(v_levelParams_3757_);
lean_dec(v_brecOnGoName_3756_);
lean_dec(v_recName_3755_);
lean_dec(v_tail_3754_);
lean_dec(v_head_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_all_3751_);
lean_dec(v___x_3750_);
lean_dec_ref(v___x_3749_);
lean_dec(v_nParams_3746_);
v___x_3772_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3773_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3772_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v___x_3773_;
}
else
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3774_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3746_);
lean_inc_ref_n(v_refArgs_3761_, 2);
v___x_3775_ = l_Array_toSubarray___redArg(v_refArgs_3761_, v___x_3774_, v_nParams_3746_);
lean_inc(v___x_3768_);
v___x_3776_ = l_Array_toSubarray___redArg(v_refArgs_3761_, v_nParams_3746_, v___x_3768_);
v___x_3777_ = l_Subarray_copy___redArg(v___x_3776_);
v___x_3778_ = l_Lean_Expr_getAppFn(v_refBody_3762_);
v___x_3779_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3777_, v___x_3778_);
lean_dec_ref(v___x_3778_);
if (lean_obj_tag(v___x_3779_) == 1)
{
lean_object* v_val_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec_ref(v_type_3760_);
v_val_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_val_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = lean_unsigned_to_nat(1u);
v___x_3782_ = lean_nat_sub(v___x_3770_, v___x_3781_);
v___x_3783_ = lean_array_get(v___x_3749_, v_refArgs_3761_, v___x_3782_);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3765_);
lean_inc(v___y_3764_);
lean_inc_ref(v___y_3763_);
lean_inc(v___x_3783_);
v___x_3784_ = lean_infer_type(v___x_3783_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3765_);
lean_inc(v___y_3764_);
lean_inc_ref(v___y_3763_);
v___x_3786_ = lean_infer_type(v_a_3785_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3786_, 1);
v___x_3788_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3787_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
if (lean_obj_tag(v_a_3789_) == 1)
{
lean_object* v_val_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___f_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; size_t v_sz_3803_; size_t v___x_3804_; lean_object* v___x_3805_; 
v_val_3790_ = lean_ctor_get(v_a_3789_, 0);
lean_inc(v_val_3790_);
lean_dec_ref_known(v_a_3789_, 1);
lean_inc(v___x_3769_);
lean_inc_ref(v_refArgs_3761_);
v___x_3791_ = l_Array_toSubarray___redArg(v_refArgs_3761_, v___x_3768_, v___x_3769_);
v___x_3792_ = l_Subarray_copy___redArg(v___x_3775_);
lean_inc_ref(v___x_3777_);
lean_inc_ref(v___x_3792_);
lean_inc(v___x_3750_);
v___f_3793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3793_, 0, v___x_3750_);
lean_closure_set(v___f_3793_, 1, v___x_3792_);
lean_closure_set(v___f_3793_, 2, v___x_3777_);
lean_closure_set(v___f_3793_, 3, v_all_3751_);
lean_closure_set(v___f_3793_, 4, v___x_3752_);
lean_closure_set(v___f_3793_, 5, v___x_3774_);
lean_closure_set(v___f_3793_, 6, v___x_3781_);
v___x_3794_ = lean_array_get_size(v___x_3777_);
v___x_3795_ = l_Array_ofFn___redArg(v___x_3794_, v___f_3793_);
v___x_3796_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3797_ = lean_array_get_size(v___x_3795_);
lean_inc_ref(v___x_3795_);
v___x_3798_ = l_Array_toSubarray___redArg(v___x_3795_, v___x_3774_, v___x_3797_);
v___x_3799_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3799_);
lean_ctor_set(v___x_3800_, 1, v___x_3794_);
lean_inc_ref(v___x_3798_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3798_);
lean_ctor_set(v___x_3801_, 1, v___x_3800_);
v___x_3802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3802_, 0, v___x_3796_);
lean_ctor_set(v___x_3802_, 1, v___x_3801_);
v_sz_3803_ = lean_array_size(v___x_3777_);
v___x_3804_ = ((size_t)0ULL);
v___x_3805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3769_, v___x_3770_, v___x_3777_, v_sz_3803_, v___x_3804_, v___x_3802_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v_fst_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___f_3815_; uint8_t v___x_3816_; lean_object* v___x_3817_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3805_, 1);
v_fst_3807_ = lean_ctor_get(v_a_3806_, 0);
lean_inc(v_fst_3807_);
lean_dec(v_a_3806_);
v___x_3808_ = l_Subarray_copy___redArg(v___x_3791_);
lean_inc(v___x_3769_);
v___x_3809_ = l_Array_toSubarray___redArg(v_refArgs_3761_, v___x_3769_, v___x_3782_);
v___x_3810_ = l_Subarray_copy___redArg(v___x_3809_);
v___x_3811_ = l_Lean_mkLevelMax(v_val_3790_, v_head_3753_);
v___x_3812_ = lean_box_usize(v_sz_3803_);
v___x_3813_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3814_ = lean_box(v___x_3771_);
v___f_3815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 30, 24);
lean_closure_set(v___f_3815_, 0, v___x_3811_);
lean_closure_set(v___f_3815_, 1, v_tail_3754_);
lean_closure_set(v___f_3815_, 2, v_recName_3755_);
lean_closure_set(v___f_3815_, 3, v___x_3792_);
lean_closure_set(v___f_3815_, 4, v___x_3798_);
lean_closure_set(v___f_3815_, 5, v___x_3769_);
lean_closure_set(v___f_3815_, 6, v___x_3770_);
lean_closure_set(v___f_3815_, 7, v___x_3777_);
lean_closure_set(v___f_3815_, 8, v___x_3812_);
lean_closure_set(v___f_3815_, 9, v___x_3813_);
lean_closure_set(v___f_3815_, 10, v___x_3808_);
lean_closure_set(v___f_3815_, 11, v___x_3795_);
lean_closure_set(v___f_3815_, 12, v___x_3810_);
lean_closure_set(v___f_3815_, 13, v___x_3783_);
lean_closure_set(v___f_3815_, 14, v___x_3781_);
lean_closure_set(v___f_3815_, 15, v___x_3749_);
lean_closure_set(v___f_3815_, 16, v_val_3780_);
lean_closure_set(v___f_3815_, 17, v___x_3814_);
lean_closure_set(v___f_3815_, 18, v_brecOnGoName_3756_);
lean_closure_set(v___f_3815_, 19, v_levelParams_3757_);
lean_closure_set(v___f_3815_, 20, v___x_3750_);
lean_closure_set(v___f_3815_, 21, v_brecOnName_3758_);
lean_closure_set(v___f_3815_, 22, v___x_3774_);
lean_closure_set(v___f_3815_, 23, v_brecOnEqName_3759_);
v___x_3816_ = 0;
v___x_3817_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3807_, v___f_3815_, v___x_3816_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v___x_3817_;
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v___x_3798_);
lean_dec_ref(v___x_3795_);
lean_dec_ref(v___x_3792_);
lean_dec_ref(v___x_3791_);
lean_dec(v_val_3790_);
lean_dec(v___x_3783_);
lean_dec(v___x_3782_);
lean_dec(v_val_3780_);
lean_dec_ref(v___x_3777_);
lean_dec(v___x_3769_);
lean_dec_ref(v_refArgs_3761_);
lean_dec(v_brecOnEqName_3759_);
lean_dec(v_brecOnName_3758_);
lean_dec(v_levelParams_3757_);
lean_dec(v_brecOnGoName_3756_);
lean_dec(v_recName_3755_);
lean_dec(v_tail_3754_);
lean_dec(v_head_3753_);
lean_dec(v___x_3750_);
lean_dec_ref(v___x_3749_);
v_a_3818_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3805_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3805_);
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
lean_dec(v_a_3789_);
lean_dec(v___x_3782_);
lean_dec(v_val_3780_);
lean_dec_ref(v___x_3777_);
lean_dec_ref(v___x_3775_);
lean_dec(v___x_3769_);
lean_dec(v___x_3768_);
lean_dec_ref(v_refArgs_3761_);
lean_dec(v_brecOnEqName_3759_);
lean_dec(v_brecOnName_3758_);
lean_dec(v_levelParams_3757_);
lean_dec(v_brecOnGoName_3756_);
lean_dec(v_recName_3755_);
lean_dec(v_tail_3754_);
lean_dec(v_head_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_all_3751_);
lean_dec(v___x_3750_);
lean_dec_ref(v___x_3749_);
v___x_3826_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3827_ = l_Lean_MessageData_ofExpr(v___x_3783_);
v___x_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3828_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3830_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
return v___x_3831_;
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v___x_3783_);
lean_dec(v___x_3782_);
lean_dec(v_val_3780_);
lean_dec_ref(v___x_3777_);
lean_dec_ref(v___x_3775_);
lean_dec(v___x_3769_);
lean_dec(v___x_3768_);
lean_dec_ref(v_refArgs_3761_);
lean_dec(v_brecOnEqName_3759_);
lean_dec(v_brecOnName_3758_);
lean_dec(v_levelParams_3757_);
lean_dec(v_brecOnGoName_3756_);
lean_dec(v_recName_3755_);
lean_dec(v_tail_3754_);
lean_dec(v_head_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_all_3751_);
lean_dec(v___x_3750_);
lean_dec_ref(v___x_3749_);
v_a_3832_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3788_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3788_);
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
lean_dec(v___x_3783_);
lean_dec(v___x_3782_);
lean_dec(v_val_3780_);
lean_dec_ref(v___x_3777_);
lean_dec_ref(v___x_3775_);
lean_dec(v___x_3769_);
lean_dec(v___x_3768_);
lean_dec_ref(v_refArgs_3761_);
lean_dec(v_brecOnEqName_3759_);
lean_dec(v_brecOnName_3758_);
lean_dec(v_levelParams_3757_);
lean_dec(v_brecOnGoName_3756_);
lean_dec(v_recName_3755_);
lean_dec(v_tail_3754_);
lean_dec(v_head_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_all_3751_);
lean_dec(v___x_3750_);
lean_dec_ref(v___x_3749_);
v_a_3840_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3786_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3786_);
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
lean_dec(v___x_3783_);
lean_dec(v___x_3782_);
lean_dec(v_val_3780_);
lean_dec_ref(v___x_3777_);
lean_dec_ref(v___x_3775_);
lean_dec(v___x_3769_);
lean_dec(v___x_3768_);
lean_dec_ref(v_refArgs_3761_);
lean_dec(v_brecOnEqName_3759_);
lean_dec(v_brecOnName_3758_);
lean_dec(v_levelParams_3757_);
lean_dec(v_brecOnGoName_3756_);
lean_dec(v_recName_3755_);
lean_dec(v_tail_3754_);
lean_dec(v_head_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_all_3751_);
lean_dec(v___x_3750_);
lean_dec_ref(v___x_3749_);
v_a_3848_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3784_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3784_);
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
lean_dec(v___x_3779_);
lean_dec_ref(v___x_3775_);
lean_dec(v___x_3769_);
lean_dec(v___x_3768_);
lean_dec_ref(v_refArgs_3761_);
lean_dec(v_brecOnEqName_3759_);
lean_dec(v_brecOnName_3758_);
lean_dec(v_levelParams_3757_);
lean_dec(v_brecOnGoName_3756_);
lean_dec(v_recName_3755_);
lean_dec(v_tail_3754_);
lean_dec(v_head_3753_);
lean_dec(v___x_3752_);
lean_dec_ref(v_all_3751_);
lean_dec(v___x_3750_);
lean_dec_ref(v___x_3749_);
v___x_3856_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3857_ = l_Lean_MessageData_ofExpr(v_type_3760_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
v___x_3861_ = lean_array_to_list(v___x_3777_);
v___x_3862_ = lean_box(0);
v___x_3863_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3861_, v___x_3862_);
v___x_3864_ = l_Lean_MessageData_ofList(v___x_3863_);
v___x_3865_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3860_);
lean_ctor_set(v___x_3865_, 1, v___x_3864_);
v___x_3866_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3865_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
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
lean_object* v___x_3871_ = _args[4];
lean_object* v_all_3872_ = _args[5];
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
v_res_3889_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3867_, v_numMotives_3868_, v_numMinors_3869_, v___x_3870_, v___x_3871_, v_all_3872_, v___x_3873_, v_head_3874_, v_tail_3875_, v_recName_3876_, v_brecOnGoName_3877_, v_levelParams_3878_, v_brecOnName_3879_, v_brecOnEqName_3880_, v_type_3881_, v_refArgs_3882_, v_refBody_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
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
lean_object* v___x_3901_; 
lean_inc(v_recName_3892_);
v___x_3901_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3892_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3935_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3935_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3935_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
if (lean_obj_tag(v_a_3902_) == 7)
{
lean_object* v_val_3906_; lean_object* v_toConstantVal_3907_; lean_object* v_numMotives_3908_; lean_object* v_numMinors_3909_; lean_object* v_levelParams_3910_; lean_object* v_type_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
lean_del_object(v___x_3904_);
v_val_3906_ = lean_ctor_get(v_a_3902_, 0);
lean_inc_ref(v_val_3906_);
lean_dec_ref_known(v_a_3902_, 1);
v_toConstantVal_3907_ = lean_ctor_get(v_val_3906_, 0);
lean_inc_ref(v_toConstantVal_3907_);
v_numMotives_3908_ = lean_ctor_get(v_val_3906_, 4);
lean_inc(v_numMotives_3908_);
v_numMinors_3909_ = lean_ctor_get(v_val_3906_, 5);
lean_inc(v_numMinors_3909_);
lean_dec_ref(v_val_3906_);
v_levelParams_3910_ = lean_ctor_get(v_toConstantVal_3907_, 1);
lean_inc_n(v_levelParams_3910_, 2);
v_type_3911_ = lean_ctor_get(v_toConstantVal_3907_, 2);
lean_inc_ref(v_type_3911_);
lean_dec_ref(v_toConstantVal_3907_);
v___x_3912_ = lean_box(0);
v___x_3913_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3910_, v___x_3912_);
if (lean_obj_tag(v___x_3913_) == 1)
{
lean_object* v_head_3914_; lean_object* v_tail_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v_brecOnGoName_3919_; lean_object* v___x_3920_; lean_object* v_brecOnEqName_3921_; lean_object* v___f_3922_; uint8_t v___x_3923_; lean_object* v___x_3924_; 
v_head_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_head_3914_);
v_tail_3915_ = lean_ctor_get(v___x_3913_, 1);
lean_inc(v_tail_3915_);
v___x_3916_ = l_Lean_instInhabitedExpr;
v___x_3917_ = lean_box(0);
v___x_3918_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3895_, 2);
v_brecOnGoName_3919_ = l_Lean_Name_str___override(v_brecOnName_3895_, v___x_3918_);
v___x_3920_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3921_ = l_Lean_Name_str___override(v_brecOnName_3895_, v___x_3920_);
lean_inc_ref(v_type_3911_);
v___f_3922_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3922_, 0, v_nParams_3893_);
lean_closure_set(v___f_3922_, 1, v_numMotives_3908_);
lean_closure_set(v___f_3922_, 2, v_numMinors_3909_);
lean_closure_set(v___f_3922_, 3, v___x_3916_);
lean_closure_set(v___f_3922_, 4, v___x_3913_);
lean_closure_set(v___f_3922_, 5, v_all_3894_);
lean_closure_set(v___f_3922_, 6, v___x_3917_);
lean_closure_set(v___f_3922_, 7, v_head_3914_);
lean_closure_set(v___f_3922_, 8, v_tail_3915_);
lean_closure_set(v___f_3922_, 9, v_recName_3892_);
lean_closure_set(v___f_3922_, 10, v_brecOnGoName_3919_);
lean_closure_set(v___f_3922_, 11, v_levelParams_3910_);
lean_closure_set(v___f_3922_, 12, v_brecOnName_3895_);
lean_closure_set(v___f_3922_, 13, v_brecOnEqName_3921_);
lean_closure_set(v___f_3922_, 14, v_type_3911_);
v___x_3923_ = 0;
v___x_3924_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3911_, v___f_3922_, v___x_3923_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_);
return v___x_3924_;
}
else
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_dec(v___x_3913_);
lean_dec_ref(v_type_3911_);
lean_dec(v_levelParams_3910_);
lean_dec(v_numMinors_3909_);
lean_dec(v_numMotives_3908_);
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
lean_dec(v_a_3902_);
lean_dec(v_brecOnName_3895_);
lean_dec_ref(v_all_3894_);
lean_dec(v_nParams_3893_);
lean_dec(v_recName_3892_);
v___x_3931_ = lean_box(0);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3931_);
v___x_3933_ = v___x_3904_;
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
lean_dec(v_brecOnName_3895_);
lean_dec_ref(v_all_3894_);
lean_dec(v_nParams_3893_);
lean_dec(v_recName_3892_);
v_a_3936_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3938_ = v___x_3901_;
v_isShared_3939_ = v_isSharedCheck_3943_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3901_);
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
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3968_ = lean_unsigned_to_nat(1u);
v___x_3969_ = lean_nat_add(v_a_3959_, v___x_3968_);
lean_dec(v_a_3959_);
lean_inc_n(v___x_3969_, 2);
lean_inc(v___x_3955_);
v___x_3970_ = lean_name_append_index_after(v___x_3955_, v___x_3969_);
lean_inc(v___x_3956_);
v___x_3971_ = lean_name_append_index_after(v___x_3956_, v___x_3969_);
lean_inc_ref(v___x_3958_);
lean_inc(v___x_3957_);
v___x_3972_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3970_, v___x_3957_, v___x_3958_, v___x_3971_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v___x_3973_; 
lean_dec_ref_known(v___x_3972_, 1);
v___x_3973_ = lean_box(0);
v_a_3959_ = v___x_3969_;
v_b_3960_ = v___x_3973_;
goto _start;
}
else
{
lean_dec(v___x_3969_);
lean_dec_ref(v___x_3958_);
lean_dec(v___x_3957_);
lean_dec(v___x_3956_);
lean_dec(v___x_3955_);
return v___x_3972_;
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
lean_object* v_options_4001_; lean_object* v_inheritedTraceOptions_4002_; uint8_t v_hasTrace_4003_; lean_object* v___x_4004_; 
v_options_4001_ = lean_ctor_get(v_a_3998_, 2);
v_inheritedTraceOptions_4002_ = lean_ctor_get(v_a_3998_, 13);
v_hasTrace_4003_ = lean_ctor_get_uint8(v_options_4001_, sizeof(void*)*1);
v___x_4004_ = lean_box(0);
if (v_hasTrace_4003_ == 0)
{
lean_object* v___x_4005_; 
lean_inc(v_indName_3995_);
v___x_4005_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4070_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4008_ = v___x_4005_;
v_isShared_4009_ = v_isSharedCheck_4070_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4070_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
if (lean_obj_tag(v_a_4006_) == 5)
{
lean_object* v_val_4010_; uint8_t v_isRec_4011_; 
v_val_4010_ = lean_ctor_get(v_a_4006_, 0);
lean_inc_ref(v_val_4010_);
lean_dec_ref_known(v_a_4006_, 1);
v_isRec_4011_ = lean_ctor_get_uint8(v_val_4010_, sizeof(void*)*6);
if (v_isRec_4011_ == 0)
{
lean_object* v___x_4012_; lean_object* v___x_4014_; 
lean_dec_ref(v_val_4010_);
lean_dec(v_indName_3995_);
v___x_4012_ = lean_box(0);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4012_);
v___x_4014_ = v___x_4008_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v___x_4012_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
else
{
lean_object* v_toConstantVal_4016_; lean_object* v_numParams_4017_; lean_object* v_all_4018_; lean_object* v_numNested_4019_; lean_object* v_type_4020_; lean_object* v___x_4021_; 
lean_del_object(v___x_4008_);
v_toConstantVal_4016_ = lean_ctor_get(v_val_4010_, 0);
lean_inc_ref(v_toConstantVal_4016_);
v_numParams_4017_ = lean_ctor_get(v_val_4010_, 1);
lean_inc(v_numParams_4017_);
v_all_4018_ = lean_ctor_get(v_val_4010_, 3);
lean_inc(v_all_4018_);
v_numNested_4019_ = lean_ctor_get(v_val_4010_, 5);
lean_inc(v_numNested_4019_);
lean_dec_ref(v_val_4010_);
v_type_4020_ = lean_ctor_get(v_toConstantVal_4016_, 2);
lean_inc_ref(v_type_4020_);
lean_dec_ref(v_toConstantVal_4016_);
v___x_4021_ = l_Lean_Meta_isPropFormerType(v_type_4020_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4024_; uint8_t v_isShared_4025_; uint8_t v_isSharedCheck_4057_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4024_ = v___x_4021_;
v_isShared_4025_ = v_isSharedCheck_4057_;
goto v_resetjp_4023_;
}
else
{
lean_inc(v_a_4022_);
lean_dec(v___x_4021_);
v___x_4024_ = lean_box(0);
v_isShared_4025_ = v_isSharedCheck_4057_;
goto v_resetjp_4023_;
}
v_resetjp_4023_:
{
uint8_t v___x_4026_; 
v___x_4026_ = lean_unbox(v_a_4022_);
lean_dec(v_a_4022_);
if (v___x_4026_ == 0)
{
lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
lean_del_object(v___x_4024_);
lean_inc_n(v_indName_3995_, 2);
v___x_4027_ = l_Lean_mkRecName(v_indName_3995_);
v___x_4028_ = l_Lean_mkBRecOnName(v_indName_3995_);
lean_inc(v_all_4018_);
v___x_4029_ = lean_array_mk(v_all_4018_);
lean_inc(v___x_4028_);
lean_inc_ref(v___x_4029_);
lean_inc(v_numParams_4017_);
lean_inc(v___x_4027_);
v___x_4030_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4027_, v_numParams_4017_, v___x_4029_, v___x_4028_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4051_; 
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4051_ == 0)
{
lean_object* v_unused_4052_; 
v_unused_4052_ = lean_ctor_get(v___x_4030_, 0);
lean_dec(v_unused_4052_);
v___x_4032_ = v___x_4030_;
v_isShared_4033_ = v_isSharedCheck_4051_;
goto v_resetjp_4031_;
}
else
{
lean_dec(v___x_4030_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4051_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; uint8_t v___x_4036_; 
v___x_4034_ = lean_unsigned_to_nat(0u);
v___x_4035_ = l_List_get_x21Internal___redArg(v___x_4004_, v_all_4018_, v___x_4034_);
lean_dec(v_all_4018_);
v___x_4036_ = lean_name_eq(v___x_4035_, v_indName_3995_);
lean_dec(v_indName_3995_);
lean_dec(v___x_4035_);
if (v___x_4036_ == 0)
{
lean_object* v___x_4037_; lean_object* v___x_4039_; 
lean_dec_ref(v___x_4029_);
lean_dec(v___x_4028_);
lean_dec(v___x_4027_);
lean_dec(v_numNested_4019_);
lean_dec(v_numParams_4017_);
v___x_4037_ = lean_box(0);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v___x_4037_);
v___x_4039_ = v___x_4032_;
goto v_reusejp_4038_;
}
else
{
lean_object* v_reuseFailAlloc_4040_; 
v_reuseFailAlloc_4040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4040_, 0, v___x_4037_);
v___x_4039_ = v_reuseFailAlloc_4040_;
goto v_reusejp_4038_;
}
v_reusejp_4038_:
{
return v___x_4039_;
}
}
else
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
lean_del_object(v___x_4032_);
v___x_4041_ = lean_box(0);
v___x_4042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4019_, v___x_4027_, v___x_4028_, v_numParams_4017_, v___x_4029_, v___x_4034_, v___x_4041_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_numNested_4019_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4049_ == 0)
{
lean_object* v_unused_4050_; 
v_unused_4050_ = lean_ctor_get(v___x_4042_, 0);
lean_dec(v_unused_4050_);
v___x_4044_ = v___x_4042_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_dec(v___x_4042_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v___x_4041_);
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v___x_4041_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
else
{
return v___x_4042_;
}
}
}
}
else
{
lean_dec_ref(v___x_4029_);
lean_dec(v___x_4028_);
lean_dec(v___x_4027_);
lean_dec(v_numNested_4019_);
lean_dec(v_all_4018_);
lean_dec(v_numParams_4017_);
lean_dec(v_indName_3995_);
return v___x_4030_;
}
}
else
{
lean_object* v___x_4053_; lean_object* v___x_4055_; 
lean_dec(v_numNested_4019_);
lean_dec(v_all_4018_);
lean_dec(v_numParams_4017_);
lean_dec(v_indName_3995_);
v___x_4053_ = lean_box(0);
if (v_isShared_4025_ == 0)
{
lean_ctor_set(v___x_4024_, 0, v___x_4053_);
v___x_4055_ = v___x_4024_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_dec(v_numNested_4019_);
lean_dec(v_all_4018_);
lean_dec(v_numParams_4017_);
lean_dec(v_indName_3995_);
v_a_4058_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4021_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4021_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
else
{
lean_object* v___x_4066_; lean_object* v___x_4068_; 
lean_dec(v_a_4006_);
lean_dec(v_indName_3995_);
v___x_4066_ = lean_box(0);
if (v_isShared_4009_ == 0)
{
lean_ctor_set(v___x_4008_, 0, v___x_4066_);
v___x_4068_ = v___x_4008_;
goto v_reusejp_4067_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4066_);
v___x_4068_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4067_;
}
v_reusejp_4067_:
{
return v___x_4068_;
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_indName_3995_);
v_a_4071_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4005_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4005_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
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
lean_object* v___f_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v_a_4087_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v_a_4102_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v_a_4107_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v_a_4112_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v_a_4124_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v_a_4129_; 
lean_inc(v_indName_3995_);
v___f_4079_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4079_, 0, v_indName_3995_);
v___x_4080_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4081_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4082_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4083_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4002_, v_options_4001_, v___x_4082_);
if (v___x_4083_ == 0)
{
lean_object* v___x_4198_; uint8_t v___x_4199_; 
v___x_4198_ = l_Lean_trace_profiler;
v___x_4199_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4001_, v___x_4198_);
if (v___x_4199_ == 0)
{
lean_object* v___x_4200_; 
lean_dec_ref(v___f_4079_);
lean_inc(v_indName_3995_);
v___x_4200_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4265_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4265_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4265_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4265_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
if (lean_obj_tag(v_a_4201_) == 5)
{
lean_object* v_val_4205_; uint8_t v_isRec_4206_; 
v_val_4205_ = lean_ctor_get(v_a_4201_, 0);
lean_inc_ref(v_val_4205_);
lean_dec_ref_known(v_a_4201_, 1);
v_isRec_4206_ = lean_ctor_get_uint8(v_val_4205_, sizeof(void*)*6);
if (v_isRec_4206_ == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4209_; 
lean_dec_ref(v_val_4205_);
lean_dec(v_indName_3995_);
v___x_4207_ = lean_box(0);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4207_);
v___x_4209_ = v___x_4203_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v___x_4207_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
else
{
lean_object* v_toConstantVal_4211_; lean_object* v_numParams_4212_; lean_object* v_all_4213_; lean_object* v_numNested_4214_; lean_object* v_type_4215_; lean_object* v___x_4216_; 
lean_del_object(v___x_4203_);
v_toConstantVal_4211_ = lean_ctor_get(v_val_4205_, 0);
lean_inc_ref(v_toConstantVal_4211_);
v_numParams_4212_ = lean_ctor_get(v_val_4205_, 1);
lean_inc(v_numParams_4212_);
v_all_4213_ = lean_ctor_get(v_val_4205_, 3);
lean_inc(v_all_4213_);
v_numNested_4214_ = lean_ctor_get(v_val_4205_, 5);
lean_inc(v_numNested_4214_);
lean_dec_ref(v_val_4205_);
v_type_4215_ = lean_ctor_get(v_toConstantVal_4211_, 2);
lean_inc_ref(v_type_4215_);
lean_dec_ref(v_toConstantVal_4211_);
v___x_4216_ = l_Lean_Meta_isPropFormerType(v_type_4215_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4252_; 
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4252_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4252_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4252_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4252_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
uint8_t v___x_4221_; 
v___x_4221_ = lean_unbox(v_a_4217_);
lean_dec(v_a_4217_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
lean_del_object(v___x_4219_);
lean_inc_n(v_indName_3995_, 2);
v___x_4222_ = l_Lean_mkRecName(v_indName_3995_);
v___x_4223_ = l_Lean_mkBRecOnName(v_indName_3995_);
lean_inc(v_all_4213_);
v___x_4224_ = lean_array_mk(v_all_4213_);
lean_inc(v___x_4223_);
lean_inc_ref(v___x_4224_);
lean_inc(v_numParams_4212_);
lean_inc(v___x_4222_);
v___x_4225_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4222_, v_numParams_4212_, v___x_4224_, v___x_4223_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4246_; 
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4246_ == 0)
{
lean_object* v_unused_4247_; 
v_unused_4247_ = lean_ctor_get(v___x_4225_, 0);
lean_dec(v_unused_4247_);
v___x_4227_ = v___x_4225_;
v_isShared_4228_ = v_isSharedCheck_4246_;
goto v_resetjp_4226_;
}
else
{
lean_dec(v___x_4225_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4246_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; uint8_t v___x_4231_; 
v___x_4229_ = lean_unsigned_to_nat(0u);
v___x_4230_ = l_List_get_x21Internal___redArg(v___x_4004_, v_all_4213_, v___x_4229_);
lean_dec(v_all_4213_);
v___x_4231_ = lean_name_eq(v___x_4230_, v_indName_3995_);
lean_dec(v_indName_3995_);
lean_dec(v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4234_; 
lean_dec_ref(v___x_4224_);
lean_dec(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec(v_numNested_4214_);
lean_dec(v_numParams_4212_);
v___x_4232_ = lean_box(0);
if (v_isShared_4228_ == 0)
{
lean_ctor_set(v___x_4227_, 0, v___x_4232_);
v___x_4234_ = v___x_4227_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v___x_4232_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_del_object(v___x_4227_);
v___x_4236_ = lean_box(0);
v___x_4237_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4214_, v___x_4222_, v___x_4223_, v_numParams_4212_, v___x_4224_, v___x_4229_, v___x_4236_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_numNested_4214_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4244_ == 0)
{
lean_object* v_unused_4245_; 
v_unused_4245_ = lean_ctor_get(v___x_4237_, 0);
lean_dec(v_unused_4245_);
v___x_4239_ = v___x_4237_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_dec(v___x_4237_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
lean_ctor_set(v___x_4239_, 0, v___x_4236_);
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v___x_4236_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
else
{
return v___x_4237_;
}
}
}
}
else
{
lean_dec_ref(v___x_4224_);
lean_dec(v___x_4223_);
lean_dec(v___x_4222_);
lean_dec(v_numNested_4214_);
lean_dec(v_all_4213_);
lean_dec(v_numParams_4212_);
lean_dec(v_indName_3995_);
return v___x_4225_;
}
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
lean_dec(v_numNested_4214_);
lean_dec(v_all_4213_);
lean_dec(v_numParams_4212_);
lean_dec(v_indName_3995_);
v___x_4248_ = lean_box(0);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4248_);
v___x_4250_ = v___x_4219_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
return v___x_4250_;
}
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec(v_numNested_4214_);
lean_dec(v_all_4213_);
lean_dec(v_numParams_4212_);
lean_dec(v_indName_3995_);
v_a_4253_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4216_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4216_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
else
{
lean_object* v___x_4261_; lean_object* v___x_4263_; 
lean_dec(v_a_4201_);
lean_dec(v_indName_3995_);
v___x_4261_ = lean_box(0);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4261_);
v___x_4263_ = v___x_4203_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
lean_object* v_a_4266_; lean_object* v___x_4268_; uint8_t v_isShared_4269_; uint8_t v_isSharedCheck_4273_; 
lean_dec(v_indName_3995_);
v_a_4266_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4268_ = v___x_4200_;
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
else
{
lean_inc(v_a_4266_);
lean_dec(v___x_4200_);
v___x_4268_ = lean_box(0);
v_isShared_4269_ = v_isSharedCheck_4273_;
goto v_resetjp_4267_;
}
v_resetjp_4267_:
{
lean_object* v___x_4271_; 
if (v_isShared_4269_ == 0)
{
v___x_4271_ = v___x_4268_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
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
goto v___jp_4131_;
}
}
else
{
goto v___jp_4131_;
}
v___jp_4084_:
{
lean_object* v___x_4088_; double v___x_4089_; double v___x_4090_; double v___x_4091_; double v___x_4092_; double v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4088_ = lean_io_mono_nanos_now();
v___x_4089_ = lean_float_of_nat(v___y_4085_);
v___x_4090_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4091_ = lean_float_div(v___x_4089_, v___x_4090_);
v___x_4092_ = lean_float_of_nat(v___x_4088_);
v___x_4093_ = lean_float_div(v___x_4092_, v___x_4090_);
v___x_4094_ = lean_box_float(v___x_4091_);
v___x_4095_ = lean_box_float(v___x_4093_);
v___x_4096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4094_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4097_, 0, v_a_4087_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4080_, v_hasTrace_4003_, v___x_4081_, v_options_4001_, v___x_4083_, v___y_4086_, v___f_4079_, v___x_4097_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
return v___x_4098_;
}
v___jp_4099_:
{
lean_object* v___x_4103_; 
v___x_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4103_, 0, v_a_4102_);
v___y_4085_ = v___y_4100_;
v___y_4086_ = v___y_4101_;
v_a_4087_ = v___x_4103_;
goto v___jp_4084_;
}
v___jp_4104_:
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_a_4107_);
v___y_4085_ = v___y_4105_;
v___y_4086_ = v___y_4106_;
v_a_4087_ = v___x_4108_;
goto v___jp_4084_;
}
v___jp_4109_:
{
lean_object* v___x_4113_; double v___x_4114_; double v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4113_ = lean_io_get_num_heartbeats();
v___x_4114_ = lean_float_of_nat(v___y_4110_);
v___x_4115_ = lean_float_of_nat(v___x_4113_);
v___x_4116_ = lean_box_float(v___x_4114_);
v___x_4117_ = lean_box_float(v___x_4115_);
v___x_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4116_);
lean_ctor_set(v___x_4118_, 1, v___x_4117_);
v___x_4119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4119_, 0, v_a_4112_);
lean_ctor_set(v___x_4119_, 1, v___x_4118_);
v___x_4120_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4080_, v_hasTrace_4003_, v___x_4081_, v_options_4001_, v___x_4083_, v___y_4111_, v___f_4079_, v___x_4119_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
return v___x_4120_;
}
v___jp_4121_:
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_a_4124_);
v___y_4110_ = v___y_4122_;
v___y_4111_ = v___y_4123_;
v_a_4112_ = v___x_4125_;
goto v___jp_4109_;
}
v___jp_4126_:
{
lean_object* v___x_4130_; 
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v_a_4129_);
v___y_4110_ = v___y_4127_;
v___y_4111_ = v___y_4128_;
v_a_4112_ = v___x_4130_;
goto v___jp_4109_;
}
v___jp_4131_:
{
lean_object* v___x_4132_; lean_object* v_a_4133_; lean_object* v___x_4134_; uint8_t v___x_4135_; 
v___x_4132_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3999_);
v_a_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_a_4133_);
lean_dec_ref(v___x_4132_);
v___x_4134_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4135_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4001_, v___x_4134_);
if (v___x_4135_ == 0)
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3995_);
v___x_4137_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
if (lean_obj_tag(v_a_4138_) == 5)
{
lean_object* v_val_4139_; uint8_t v_isRec_4140_; 
v_val_4139_ = lean_ctor_get(v_a_4138_, 0);
lean_inc_ref(v_val_4139_);
lean_dec_ref_known(v_a_4138_, 1);
v_isRec_4140_ = lean_ctor_get_uint8(v_val_4139_, sizeof(void*)*6);
if (v_isRec_4140_ == 0)
{
lean_object* v___x_4141_; 
lean_dec_ref(v_val_4139_);
lean_dec(v_indName_3995_);
v___x_4141_ = lean_box(0);
v___y_4100_ = v___x_4136_;
v___y_4101_ = v_a_4133_;
v_a_4102_ = v___x_4141_;
goto v___jp_4099_;
}
else
{
lean_object* v_toConstantVal_4142_; lean_object* v_numParams_4143_; lean_object* v_all_4144_; lean_object* v_numNested_4145_; lean_object* v_type_4146_; lean_object* v___x_4147_; 
v_toConstantVal_4142_ = lean_ctor_get(v_val_4139_, 0);
lean_inc_ref(v_toConstantVal_4142_);
v_numParams_4143_ = lean_ctor_get(v_val_4139_, 1);
lean_inc(v_numParams_4143_);
v_all_4144_ = lean_ctor_get(v_val_4139_, 3);
lean_inc(v_all_4144_);
v_numNested_4145_ = lean_ctor_get(v_val_4139_, 5);
lean_inc(v_numNested_4145_);
lean_dec_ref(v_val_4139_);
v_type_4146_ = lean_ctor_get(v_toConstantVal_4142_, 2);
lean_inc_ref(v_type_4146_);
lean_dec_ref(v_toConstantVal_4142_);
v___x_4147_ = l_Lean_Meta_isPropFormerType(v_type_4146_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; uint8_t v___x_4149_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v___x_4149_ = lean_unbox(v_a_4148_);
lean_dec(v_a_4148_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; 
lean_inc_n(v_indName_3995_, 2);
v___x_4150_ = l_Lean_mkRecName(v_indName_3995_);
v___x_4151_ = l_Lean_mkBRecOnName(v_indName_3995_);
lean_inc(v_all_4144_);
v___x_4152_ = lean_array_mk(v_all_4144_);
lean_inc(v___x_4151_);
lean_inc_ref(v___x_4152_);
lean_inc(v_numParams_4143_);
lean_inc(v___x_4150_);
v___x_4153_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4150_, v_numParams_4143_, v___x_4152_, v___x_4151_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; uint8_t v___x_4156_; 
lean_dec_ref_known(v___x_4153_, 1);
v___x_4154_ = lean_unsigned_to_nat(0u);
v___x_4155_ = l_List_get_x21Internal___redArg(v___x_4004_, v_all_4144_, v___x_4154_);
lean_dec(v_all_4144_);
v___x_4156_ = lean_name_eq(v___x_4155_, v_indName_3995_);
lean_dec(v_indName_3995_);
lean_dec(v___x_4155_);
if (v___x_4156_ == 0)
{
lean_object* v___x_4157_; 
lean_dec_ref(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v_numNested_4145_);
lean_dec(v_numParams_4143_);
v___x_4157_ = lean_box(0);
v___y_4100_ = v___x_4136_;
v___y_4101_ = v_a_4133_;
v_a_4102_ = v___x_4157_;
goto v___jp_4099_;
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_box(0);
v___x_4159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4145_, v___x_4150_, v___x_4151_, v_numParams_4143_, v___x_4152_, v___x_4154_, v___x_4158_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_numNested_4145_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_dec_ref_known(v___x_4159_, 1);
v___y_4100_ = v___x_4136_;
v___y_4101_ = v_a_4133_;
v_a_4102_ = v___x_4158_;
goto v___jp_4099_;
}
else
{
lean_object* v_a_4160_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___y_4105_ = v___x_4136_;
v___y_4106_ = v_a_4133_;
v_a_4107_ = v_a_4160_;
goto v___jp_4104_;
}
}
}
else
{
lean_dec_ref(v___x_4152_);
lean_dec(v___x_4151_);
lean_dec(v___x_4150_);
lean_dec(v_numNested_4145_);
lean_dec(v_all_4144_);
lean_dec(v_numParams_4143_);
lean_dec(v_indName_3995_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4161_; 
v_a_4161_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4153_, 1);
v___y_4100_ = v___x_4136_;
v___y_4101_ = v_a_4133_;
v_a_4102_ = v_a_4161_;
goto v___jp_4099_;
}
else
{
lean_object* v_a_4162_; 
v_a_4162_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4153_, 1);
v___y_4105_ = v___x_4136_;
v___y_4106_ = v_a_4133_;
v_a_4107_ = v_a_4162_;
goto v___jp_4104_;
}
}
}
else
{
lean_object* v___x_4163_; 
lean_dec(v_numNested_4145_);
lean_dec(v_all_4144_);
lean_dec(v_numParams_4143_);
lean_dec(v_indName_3995_);
v___x_4163_ = lean_box(0);
v___y_4100_ = v___x_4136_;
v___y_4101_ = v_a_4133_;
v_a_4102_ = v___x_4163_;
goto v___jp_4099_;
}
}
else
{
lean_object* v_a_4164_; 
lean_dec(v_numNested_4145_);
lean_dec(v_all_4144_);
lean_dec(v_numParams_4143_);
lean_dec(v_indName_3995_);
v_a_4164_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4147_, 1);
v___y_4105_ = v___x_4136_;
v___y_4106_ = v_a_4133_;
v_a_4107_ = v_a_4164_;
goto v___jp_4104_;
}
}
}
else
{
lean_object* v___x_4165_; 
lean_dec(v_a_4138_);
lean_dec(v_indName_3995_);
v___x_4165_ = lean_box(0);
v___y_4100_ = v___x_4136_;
v___y_4101_ = v_a_4133_;
v_a_4102_ = v___x_4165_;
goto v___jp_4099_;
}
}
else
{
lean_object* v_a_4166_; 
lean_dec(v_indName_3995_);
v_a_4166_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4166_);
lean_dec_ref_known(v___x_4137_, 1);
v___y_4105_ = v___x_4136_;
v___y_4106_ = v_a_4133_;
v_a_4107_ = v_a_4166_;
goto v___jp_4104_;
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
v___y_4122_ = v___x_4167_;
v___y_4123_ = v_a_4133_;
v_a_4124_ = v___x_4172_;
goto v___jp_4121_;
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
v___x_4186_ = l_List_get_x21Internal___redArg(v___x_4004_, v_all_4175_, v___x_4185_);
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
v___y_4122_ = v___x_4167_;
v___y_4123_ = v_a_4133_;
v_a_4124_ = v___x_4188_;
goto v___jp_4121_;
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
v___y_4122_ = v___x_4167_;
v___y_4123_ = v_a_4133_;
v_a_4124_ = v___x_4189_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4191_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v___x_4190_, 1);
v___y_4127_ = v___x_4167_;
v___y_4128_ = v_a_4133_;
v_a_4129_ = v_a_4191_;
goto v___jp_4126_;
}
}
}
else
{
lean_dec_ref(v___x_4183_);
lean_dec(v___x_4182_);
lean_dec(v___x_4181_);
lean_dec(v_numNested_4176_);
lean_dec(v_all_4175_);
lean_dec(v_numParams_4174_);
lean_dec(v_indName_3995_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v_a_4192_; 
v_a_4192_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4192_);
lean_dec_ref_known(v___x_4184_, 1);
v___y_4122_ = v___x_4167_;
v___y_4123_ = v_a_4133_;
v_a_4124_ = v_a_4192_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4193_; 
v_a_4193_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4193_);
lean_dec_ref_known(v___x_4184_, 1);
v___y_4127_ = v___x_4167_;
v___y_4128_ = v_a_4133_;
v_a_4129_ = v_a_4193_;
goto v___jp_4126_;
}
}
}
else
{
lean_object* v___x_4194_; 
lean_dec(v_numNested_4176_);
lean_dec(v_all_4175_);
lean_dec(v_numParams_4174_);
lean_dec(v_indName_3995_);
v___x_4194_ = lean_box(0);
v___y_4122_ = v___x_4167_;
v___y_4123_ = v_a_4133_;
v_a_4124_ = v___x_4194_;
goto v___jp_4121_;
}
}
else
{
lean_object* v_a_4195_; 
lean_dec(v_numNested_4176_);
lean_dec(v_all_4175_);
lean_dec(v_numParams_4174_);
lean_dec(v_indName_3995_);
v_a_4195_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4178_, 1);
v___y_4127_ = v___x_4167_;
v___y_4128_ = v_a_4133_;
v_a_4129_ = v_a_4195_;
goto v___jp_4126_;
}
}
}
else
{
lean_object* v___x_4196_; 
lean_dec(v_a_4169_);
lean_dec(v_indName_3995_);
v___x_4196_ = lean_box(0);
v___y_4122_ = v___x_4167_;
v___y_4123_ = v_a_4133_;
v_a_4124_ = v___x_4196_;
goto v___jp_4121_;
}
}
else
{
lean_object* v_a_4197_; 
lean_dec(v_indName_3995_);
v_a_4197_ = lean_ctor_get(v___x_4168_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4168_, 1);
v___y_4127_ = v___x_4167_;
v___y_4128_ = v_a_4133_;
v_a_4129_ = v_a_4197_;
goto v___jp_4126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_){
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_mkBRecOn(v_indName_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_);
lean_dec(v_a_4278_);
lean_dec_ref(v_a_4277_);
lean_dec(v_a_4276_);
lean_dec_ref(v_a_4275_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4281_, lean_object* v___x_4282_, lean_object* v___x_4283_, lean_object* v___x_4284_, lean_object* v___x_4285_, lean_object* v_inst_4286_, lean_object* v_R_4287_, lean_object* v_a_4288_, lean_object* v_b_4289_, lean_object* v_c_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v___x_4296_; 
v___x_4296_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4281_, v___x_4282_, v___x_4283_, v___x_4284_, v___x_4285_, v_a_4288_, v_b_4289_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4297_, lean_object* v___x_4298_, lean_object* v___x_4299_, lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v_inst_4302_, lean_object* v_R_4303_, lean_object* v_a_4304_, lean_object* v_b_4305_, lean_object* v_c_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v_res_4312_; 
v_res_4312_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4297_, v___x_4298_, v___x_4299_, v___x_4300_, v___x_4301_, v_inst_4302_, v_R_4303_, v_a_4304_, v_b_4305_, v_c_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v_upperBound_4297_);
return v_res_4312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4358_ = lean_unsigned_to_nat(2304625798u);
v___x_4359_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4360_ = l_Lean_Name_num___override(v___x_4359_, v___x_4358_);
return v___x_4360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4362_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4363_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4364_ = l_Lean_Name_str___override(v___x_4363_, v___x_4362_);
return v___x_4364_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4367_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4368_ = l_Lean_Name_str___override(v___x_4367_, v___x_4366_);
return v___x_4368_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = lean_unsigned_to_nat(2u);
v___x_4370_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4371_ = l_Lean_Name_num___override(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4373_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4374_ = 0;
v___x_4375_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4376_ = l_Lean_registerTraceClass(v___x_4373_, v___x_4374_, v___x_4375_);
return v___x_4376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4378_;
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
