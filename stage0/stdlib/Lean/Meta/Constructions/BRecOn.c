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
uint8_t v___x_8930__boxed_555_; lean_object* v_res_556_; 
v___x_8930__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_8930__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_683_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_661_);
lean_inc_ref(v_refArgs_670_);
v___x_684_ = l_Array_toSubarray___redArg(v_refArgs_670_, v___x_683_, v_nParams_661_);
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_sub(v___x_679_, v___x_685_);
v___x_687_ = lean_array_get(v___x_664_, v_refArgs_670_, v___x_686_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___x_687_);
v___x_688_ = lean_infer_type(v___x_687_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v___x_690_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
v___x_690_ = lean_infer_type(v_a_689_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_692_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = l_Lean_Meta_typeFormerTypeLevel(v_a_691_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
if (lean_obj_tag(v_a_693_) == 1)
{
lean_object* v_val_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; size_t v_sz_704_; size_t v___x_705_; lean_object* v___x_706_; 
v_val_694_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v_a_693_, 1);
lean_inc(v___x_677_);
lean_inc_ref_n(v_refArgs_670_, 2);
v___x_695_ = l_Array_toSubarray___redArg(v_refArgs_670_, v_nParams_661_, v___x_677_);
lean_inc(v___x_678_);
v___x_696_ = l_Array_toSubarray___redArg(v_refArgs_670_, v___x_677_, v___x_678_);
v___x_697_ = l_Subarray_copy___redArg(v___x_684_);
v___x_698_ = l_Subarray_copy___redArg(v___x_695_);
v___x_699_ = l_Lean_mkLevelMax(v_val_694_, v_head_665_);
lean_inc_n(v___x_699_, 2);
v___x_700_ = l_Lean_Level_succ___override(v___x_699_);
v___x_701_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
lean_ctor_set(v___x_701_, 1, v_tail_666_);
v___x_702_ = l_Lean_Expr_const___override(v_recName_667_, v___x_701_);
v___x_703_ = l_Lean_mkAppN(v___x_702_, v___x_697_);
v_sz_704_ = lean_array_size(v___x_698_);
v___x_705_ = ((size_t)0ULL);
v___x_706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_699_, v___x_678_, v___x_679_, v___x_698_, v_sz_704_, v___x_705_, v___x_703_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; size_t v_sz_709_; lean_object* v___x_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Subarray_copy___redArg(v___x_696_);
v_sz_709_ = lean_array_size(v___x_708_);
lean_inc_ref(v___x_698_);
lean_inc(v___x_699_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_699_, v___x_698_, v___x_708_, v_sz_709_, v___x_705_, v_a_707_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec_ref(v___x_708_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; uint8_t v___x_723_; lean_object* v___x_724_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v___x_712_ = l_Array_toSubarray___redArg(v_refArgs_670_, v___x_678_, v___x_686_);
v___x_713_ = l_Subarray_copy___redArg(v___x_712_);
v___x_714_ = l_Lean_mkAppN(v_a_711_, v___x_713_);
lean_inc(v___x_687_);
v___x_715_ = l_Lean_Expr_app___override(v___x_714_, v___x_687_);
v___x_716_ = l_Array_append___redArg(v___x_697_, v___x_698_);
lean_dec_ref(v___x_698_);
v___x_717_ = l_Array_append___redArg(v___x_716_, v___x_713_);
lean_dec_ref(v___x_713_);
v___x_718_ = lean_mk_empty_array_with_capacity(v___x_685_);
v___x_719_ = lean_array_push(v___x_718_, v___x_687_);
v___x_720_ = l_Array_append___redArg(v___x_717_, v___x_719_);
lean_dec_ref(v___x_719_);
v___x_721_ = l_Lean_Expr_sort___override(v___x_699_);
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
lean_dec(v___x_699_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec(v___x_687_);
lean_dec(v___x_686_);
lean_dec(v___x_678_);
lean_dec_ref(v_refArgs_670_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
v_a_746_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_710_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_710_);
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
lean_dec(v___x_699_);
lean_dec_ref(v___x_698_);
lean_dec_ref(v___x_697_);
lean_dec_ref(v___x_696_);
lean_dec(v___x_687_);
lean_dec(v___x_686_);
lean_dec(v___x_678_);
lean_dec_ref(v_refArgs_670_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
v_a_754_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_706_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_706_);
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
lean_dec(v_a_693_);
lean_dec(v___x_686_);
lean_dec_ref(v___x_684_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec_ref(v_refArgs_670_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
lean_dec(v_nParams_661_);
v___x_762_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_763_ = l_Lean_MessageData_ofExpr(v___x_687_);
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
lean_dec(v___x_687_);
lean_dec(v___x_686_);
lean_dec_ref(v___x_684_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec_ref(v_refArgs_670_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
lean_dec(v_nParams_661_);
v_a_768_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_692_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_692_);
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
lean_dec(v___x_687_);
lean_dec(v___x_686_);
lean_dec_ref(v___x_684_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec_ref(v_refArgs_670_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
lean_dec(v_nParams_661_);
v_a_776_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_690_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_690_);
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
lean_dec(v___x_687_);
lean_dec(v___x_686_);
lean_dec_ref(v___x_684_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec_ref(v_refArgs_670_);
lean_dec(v_levelParams_669_);
lean_dec(v_belowName_668_);
lean_dec(v_recName_667_);
lean_dec(v_tail_666_);
lean_dec(v_head_665_);
lean_dec(v_nParams_661_);
v_a_784_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_688_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_688_);
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
v___x_823_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_mctx_855_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_868_, 2, v_zetaDeltaFVarIds_856_);
lean_ctor_set(v_reuseFailAlloc_868_, 3, v_postponed_857_);
lean_ctor_set(v_reuseFailAlloc_868_, 4, v_diag_858_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_865_ = lean_st_ref_put(v___y_832_, v___x_864_);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
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
lean_object* v___x_919_; 
v___x_919_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_919_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
lean_ctor_set(v___x_924_, 2, v___x_923_);
lean_ctor_set(v___x_924_, 3, v___x_923_);
lean_ctor_set(v___x_924_, 4, v___x_922_);
lean_ctor_set(v___x_924_, 5, v___x_922_);
lean_ctor_set(v___x_924_, 6, v___x_922_);
lean_ctor_set(v___x_924_, 7, v___x_922_);
lean_ctor_set(v___x_924_, 8, v___x_922_);
lean_ctor_set(v___x_924_, 9, v___x_922_);
lean_ctor_set(v___x_924_, 10, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_unsigned_to_nat(32u);
v___x_926_ = lean_mk_empty_array_with_capacity(v___x_925_);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_928_ = ((size_t)5ULL);
v___x_929_ = lean_unsigned_to_nat(0u);
v___x_930_ = lean_unsigned_to_nat(32u);
v___x_931_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___x_932_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_933_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_931_);
lean_ctor_set(v___x_933_, 2, v___x_929_);
lean_ctor_set(v___x_933_, 3, v___x_929_);
lean_ctor_set_usize(v___x_933_, 4, v___x_928_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_934_ = lean_box(1);
v___x_935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
lean_ctor_set(v___x_937_, 2, v___x_934_);
return v___x_937_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_955_ = l_Lean_stringToMessageData(v___x_954_);
return v___x_955_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_959_, lean_object* v_declHint_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v_env_964_; uint8_t v___x_965_; 
v___x_963_ = lean_st_ref_get(v___y_961_);
v_env_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_963_);
v___x_965_ = l_Lean_Name_isAnonymous(v_declHint_960_);
if (v___x_965_ == 0)
{
uint8_t v_isExporting_966_; 
v_isExporting_966_ = lean_ctor_get_uint8(v_env_964_, sizeof(void*)*8);
if (v_isExporting_966_ == 0)
{
lean_object* v___x_967_; 
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_960_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v_msg_959_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; uint8_t v___x_969_; 
lean_inc_ref(v_env_964_);
v___x_968_ = l_Lean_Environment_setExporting(v_env_964_, v___x_965_);
lean_inc(v_declHint_960_);
lean_inc_ref(v___x_968_);
v___x_969_ = l_Lean_Environment_contains(v___x_968_, v_declHint_960_, v_isExporting_966_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; 
lean_dec_ref(v___x_968_);
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_960_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v_msg_959_);
return v___x_970_;
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v_c_976_; lean_object* v___x_977_; 
v___x_971_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_973_ = l_Lean_Options_empty;
v___x_974_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_974_, 0, v___x_968_);
lean_ctor_set(v___x_974_, 1, v___x_971_);
lean_ctor_set(v___x_974_, 2, v___x_972_);
lean_ctor_set(v___x_974_, 3, v___x_973_);
lean_inc(v_declHint_960_);
v___x_975_ = l_Lean_MessageData_ofConstName(v_declHint_960_, v___x_965_);
v_c_976_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_976_, 0, v___x_974_);
lean_ctor_set(v_c_976_, 1, v___x_975_);
v___x_977_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_964_, v_declHint_960_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_960_);
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
lean_ctor_set(v___x_979_, 1, v_c_976_);
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_979_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_MessageData_note(v___x_981_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v_msg_959_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v_val_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1020_; 
v_val_985_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_987_ = v___x_977_;
v_isShared_988_ = v_isSharedCheck_1020_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_val_985_);
lean_dec(v___x_977_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1020_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_mod_992_; uint8_t v___x_993_; 
v___x_989_ = lean_box(0);
v___x_990_ = l_Lean_Environment_header(v_env_964_);
lean_dec_ref(v_env_964_);
v___x_991_ = l_Lean_EnvironmentHeader_moduleNames(v___x_990_);
v_mod_992_ = lean_array_get(v___x_989_, v___x_991_, v_val_985_);
lean_dec(v_val_985_);
lean_dec_ref(v___x_991_);
v___x_993_ = l_Lean_isPrivateName(v_declHint_960_);
lean_dec(v_declHint_960_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_c_976_);
v___x_996_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_MessageData_ofName(v_mod_992_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_MessageData_note(v___x_1001_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v_msg_959_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 0, v___x_1003_);
v___x_1005_ = v___x_987_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
else
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1007_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_c_976_);
v___x_1009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_MessageData_ofName(v_mod_992_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1012_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = l_Lean_MessageData_note(v___x_1014_);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v_msg_959_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 0);
lean_ctor_set(v___x_987_, 0, v___x_1016_);
v___x_1018_ = v___x_987_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v___x_1016_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1021_; 
lean_dec_ref(v_env_964_);
lean_dec(v_declHint_960_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v_msg_959_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1022_, lean_object* v_declHint_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1022_, v_declHint_1023_, v___y_1024_);
lean_dec(v___y_1024_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1027_, lean_object* v_declHint_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1044_; 
v___x_1034_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1027_, v_declHint_1028_, v___y_1032_);
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1034_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1037_ = v___x_1034_;
v_isShared_1038_ = v_isSharedCheck_1044_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1034_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1044_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1039_ = l_Lean_unknownIdentifierMessageTag;
v___x_1040_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
lean_ctor_set(v___x_1040_, 1, v_a_1035_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1040_);
v___x_1042_ = v___x_1037_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1045_, lean_object* v_declHint_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1045_, v_declHint_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1053_, lean_object* v_msg_1054_, lean_object* v_declHint_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; lean_object* v_a_1062_; lean_object* v___x_1063_; 
v___x_1061_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1054_, v_declHint_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
v_a_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_a_1062_);
lean_dec_ref(v___x_1061_);
v___x_1063_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1053_, v_a_1062_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1064_, lean_object* v_msg_1065_, lean_object* v_declHint_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1064_, v_msg_1065_, v_declHint_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v_ref_1064_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1075_ = l_Lean_stringToMessageData(v___x_1074_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1079_, lean_object* v_constName_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1086_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1087_ = 0;
lean_inc(v_constName_1080_);
v___x_1088_ = l_Lean_MessageData_ofConstName(v_constName_1080_, v___x_1087_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1086_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1079_, v___x_1091_, v_constName_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1093_, lean_object* v_constName_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1093_, v_constName_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v_ref_1093_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v_ref_1107_; lean_object* v___x_1108_; 
v_ref_1107_ = lean_ctor_get(v___y_1104_, 2);
v___x_1108_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1107_, v_constName_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v_env_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1122_ = lean_st_ref_get(v___y_1120_);
v_env_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc_ref(v_env_1123_);
lean_dec(v___x_1122_);
v___x_1124_ = 0;
lean_inc(v_constName_1116_);
v___x_1125_ = l_Lean_Environment_find_x3f(v_env_1123_, v_constName_1116_, v___x_1124_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1126_;
}
else
{
lean_object* v_val_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_constName_1116_);
v_val_1127_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1125_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_val_1127_);
lean_dec(v___x_1125_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
lean_ctor_set_tag(v___x_1129_, 0);
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_val_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1141_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1147_ = l_Lean_stringToMessageData(v___x_1146_);
return v___x_1147_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1150_ = l_Lean_stringToMessageData(v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1151_, lean_object* v_nParams_1152_, lean_object* v_belowName_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v___x_1159_; 
lean_inc(v_recName_1151_);
v___x_1159_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1151_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
if (lean_obj_tag(v_a_1160_) == 7)
{
lean_object* v_val_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1277_; 
v_val_1161_ = lean_ctor_get(v_a_1160_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_a_1160_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1163_ = v_a_1160_;
v_isShared_1164_ = v_isSharedCheck_1277_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_val_1161_);
lean_dec(v_a_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1277_;
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
lean_object* v_head_1172_; lean_object* v_tail_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; 
v_head_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_head_1172_);
v_tail_1173_ = lean_ctor_get(v___x_1171_, 1);
lean_inc(v_tail_1173_);
lean_dec_ref_known(v___x_1171_, 2);
v___x_1174_ = l_Lean_instInhabitedExpr;
v___f_1175_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 16, 9);
lean_closure_set(v___f_1175_, 0, v_nParams_1152_);
lean_closure_set(v___f_1175_, 1, v_numMotives_1166_);
lean_closure_set(v___f_1175_, 2, v_numMinors_1167_);
lean_closure_set(v___f_1175_, 3, v___x_1174_);
lean_closure_set(v___f_1175_, 4, v_head_1172_);
lean_closure_set(v___f_1175_, 5, v_tail_1173_);
lean_closure_set(v___f_1175_, 6, v_recName_1151_);
lean_closure_set(v___f_1175_, 7, v_belowName_1153_);
lean_closure_set(v___f_1175_, 8, v_levelParams_1168_);
v___x_1176_ = 0;
v___x_1177_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1169_, v___f_1175_, v___x_1176_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1180_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc_n(v_a_1178_, 2);
lean_dec_ref_known(v___x_1177_, 1);
if (v_isShared_1164_ == 0)
{
lean_ctor_set_tag(v___x_1163_, 1);
lean_ctor_set(v___x_1163_, 0, v_a_1178_);
v___x_1180_ = v___x_1163_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1178_);
v___x_1180_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; 
v___x_1181_ = l_Lean_addDecl(v___x_1180_, v___x_1176_, v_a_1156_, v_a_1157_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_toConstantVal_1182_; lean_object* v_name_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1260_; 
lean_dec_ref_known(v___x_1181_, 1);
v_toConstantVal_1182_ = lean_ctor_get(v_a_1178_, 0);
lean_inc_ref(v_toConstantVal_1182_);
lean_dec(v_a_1178_);
v_name_1183_ = lean_ctor_get(v_toConstantVal_1182_, 0);
lean_inc_n(v_name_1183_, 2);
lean_dec_ref(v_toConstantVal_1182_);
v___x_1184_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1183_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v___x_1184_, 0);
lean_dec(v_unused_1261_);
v___x_1186_ = v___x_1184_;
v_isShared_1187_ = v_isSharedCheck_1260_;
goto v_resetjp_1185_;
}
else
{
lean_dec(v___x_1184_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1260_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v_env_1189_; lean_object* v_nextMacroScope_1190_; lean_object* v_ngen_1191_; lean_object* v_auxDeclNGen_1192_; lean_object* v_traceState_1193_; lean_object* v_messages_1194_; lean_object* v_infoState_1195_; lean_object* v_snapshotTasks_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1258_; 
v___x_1188_ = lean_st_ref_take(v_a_1157_);
v_env_1189_ = lean_ctor_get(v___x_1188_, 0);
v_nextMacroScope_1190_ = lean_ctor_get(v___x_1188_, 1);
v_ngen_1191_ = lean_ctor_get(v___x_1188_, 2);
v_auxDeclNGen_1192_ = lean_ctor_get(v___x_1188_, 3);
v_traceState_1193_ = lean_ctor_get(v___x_1188_, 4);
v_messages_1194_ = lean_ctor_get(v___x_1188_, 6);
v_infoState_1195_ = lean_ctor_get(v___x_1188_, 7);
v_snapshotTasks_1196_ = lean_ctor_get(v___x_1188_, 8);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1188_, 5);
lean_dec(v_unused_1259_);
v___x_1198_ = v___x_1188_;
v_isShared_1199_ = v_isSharedCheck_1258_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_snapshotTasks_1196_);
lean_inc(v_infoState_1195_);
lean_inc(v_messages_1194_);
lean_inc(v_traceState_1193_);
lean_inc(v_auxDeclNGen_1192_);
lean_inc(v_ngen_1191_);
lean_inc(v_nextMacroScope_1190_);
lean_inc(v_env_1189_);
lean_dec(v___x_1188_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1258_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_inc(v_name_1183_);
v___x_1200_ = l_Lean_markAuxRecursor(v_env_1189_, v_name_1183_);
v___x_1201_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 5, v___x_1201_);
lean_ctor_set(v___x_1198_, 0, v___x_1200_);
v___x_1203_ = v___x_1198_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_nextMacroScope_1190_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_ngen_1191_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_auxDeclNGen_1192_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_traceState_1193_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_messages_1194_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v_infoState_1195_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_snapshotTasks_1196_);
v___x_1203_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v_mctx_1206_; lean_object* v_zetaDeltaFVarIds_1207_; lean_object* v_postponed_1208_; lean_object* v_diag_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1255_; 
v___x_1204_ = lean_st_ref_put(v_a_1157_, v___x_1203_);
v___x_1205_ = lean_st_ref_take(v_a_1155_);
v_mctx_1206_ = lean_ctor_get(v___x_1205_, 0);
v_zetaDeltaFVarIds_1207_ = lean_ctor_get(v___x_1205_, 2);
v_postponed_1208_ = lean_ctor_get(v___x_1205_, 3);
v_diag_1209_ = lean_ctor_get(v___x_1205_, 4);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1205_, 1);
lean_dec(v_unused_1256_);
v___x_1211_ = v___x_1205_;
v_isShared_1212_ = v_isSharedCheck_1255_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_diag_1209_);
lean_inc(v_postponed_1208_);
lean_inc(v_zetaDeltaFVarIds_1207_);
lean_inc(v_mctx_1206_);
lean_dec(v___x_1205_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1255_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_mctx_1206_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_zetaDeltaFVarIds_1207_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_postponed_1208_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_diag_1209_);
v___x_1215_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_env_1218_; lean_object* v_nextMacroScope_1219_; lean_object* v_ngen_1220_; lean_object* v_auxDeclNGen_1221_; lean_object* v_traceState_1222_; lean_object* v_messages_1223_; lean_object* v_infoState_1224_; lean_object* v_snapshotTasks_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1252_; 
v___x_1216_ = lean_st_ref_put(v_a_1155_, v___x_1215_);
v___x_1217_ = lean_st_ref_take(v_a_1157_);
v_env_1218_ = lean_ctor_get(v___x_1217_, 0);
v_nextMacroScope_1219_ = lean_ctor_get(v___x_1217_, 1);
v_ngen_1220_ = lean_ctor_get(v___x_1217_, 2);
v_auxDeclNGen_1221_ = lean_ctor_get(v___x_1217_, 3);
v_traceState_1222_ = lean_ctor_get(v___x_1217_, 4);
v_messages_1223_ = lean_ctor_get(v___x_1217_, 6);
v_infoState_1224_ = lean_ctor_get(v___x_1217_, 7);
v_snapshotTasks_1225_ = lean_ctor_get(v___x_1217_, 8);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1217_, 5);
lean_dec(v_unused_1253_);
v___x_1227_ = v___x_1217_;
v_isShared_1228_ = v_isSharedCheck_1252_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_snapshotTasks_1225_);
lean_inc(v_infoState_1224_);
lean_inc(v_messages_1223_);
lean_inc(v_traceState_1222_);
lean_inc(v_auxDeclNGen_1221_);
lean_inc(v_ngen_1220_);
lean_inc(v_nextMacroScope_1219_);
lean_inc(v_env_1218_);
lean_dec(v___x_1217_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1252_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
v___x_1229_ = l_Lean_addProtected(v_env_1218_, v_name_1183_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 5, v___x_1201_);
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v_nextMacroScope_1219_);
lean_ctor_set(v_reuseFailAlloc_1251_, 2, v_ngen_1220_);
lean_ctor_set(v_reuseFailAlloc_1251_, 3, v_auxDeclNGen_1221_);
lean_ctor_set(v_reuseFailAlloc_1251_, 4, v_traceState_1222_);
lean_ctor_set(v_reuseFailAlloc_1251_, 5, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1251_, 6, v_messages_1223_);
lean_ctor_set(v_reuseFailAlloc_1251_, 7, v_infoState_1224_);
lean_ctor_set(v_reuseFailAlloc_1251_, 8, v_snapshotTasks_1225_);
v___x_1231_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_mctx_1234_; lean_object* v_zetaDeltaFVarIds_1235_; lean_object* v_postponed_1236_; lean_object* v_diag_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1249_; 
v___x_1232_ = lean_st_ref_put(v_a_1157_, v___x_1231_);
v___x_1233_ = lean_st_ref_take(v_a_1155_);
v_mctx_1234_ = lean_ctor_get(v___x_1233_, 0);
v_zetaDeltaFVarIds_1235_ = lean_ctor_get(v___x_1233_, 2);
v_postponed_1236_ = lean_ctor_get(v___x_1233_, 3);
v_diag_1237_ = lean_ctor_get(v___x_1233_, 4);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1233_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1233_, 1);
lean_dec(v_unused_1250_);
v___x_1239_ = v___x_1233_;
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_diag_1237_);
lean_inc(v_postponed_1236_);
lean_inc(v_zetaDeltaFVarIds_1235_);
lean_inc(v_mctx_1234_);
lean_dec(v___x_1233_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1249_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1213_);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_mctx_1234_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_zetaDeltaFVarIds_1235_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_postponed_1236_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_diag_1237_);
v___x_1242_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
v___x_1243_ = lean_st_ref_put(v_a_1155_, v___x_1242_);
v___x_1244_ = lean_box(0);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1244_);
v___x_1246_ = v___x_1186_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
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
lean_dec(v_a_1178_);
return v___x_1181_;
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_del_object(v___x_1163_);
v_a_1263_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1177_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1177_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
else
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec(v___x_1171_);
lean_dec_ref(v_type_1169_);
lean_dec(v_levelParams_1168_);
lean_dec(v_numMinors_1167_);
lean_dec(v_numMotives_1166_);
lean_del_object(v___x_1163_);
lean_dec(v_belowName_1153_);
lean_dec(v_nParams_1152_);
v___x_1271_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1272_ = l_Lean_MessageData_ofName(v_recName_1151_);
v___x_1273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1271_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
v___x_1274_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1273_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1275_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1276_;
}
}
}
else
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
lean_dec(v_a_1160_);
lean_dec(v_belowName_1153_);
lean_dec(v_nParams_1152_);
v___x_1278_ = l_Lean_MessageData_ofName(v_recName_1151_);
v___x_1279_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1278_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1280_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_);
return v___x_1281_;
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec(v_belowName_1153_);
lean_dec(v_nParams_1152_);
lean_dec(v_recName_1151_);
v_a_1282_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1159_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1159_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1290_, lean_object* v_nParams_1291_, lean_object* v_belowName_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1290_, v_nParams_1291_, v_belowName_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1299_, lean_object* v_msg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1307_, lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1307_, v_msg_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1315_, uint8_t v_s_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1315_, v_s_1316_, v___y_1318_, v___y_1320_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1323_, lean_object* v_s_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v_s_boxed_1330_; lean_object* v_res_1331_; 
v_s_boxed_1330_ = lean_unbox(v_s_1324_);
v_res_1331_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1323_, v_s_boxed_1330_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1332_, lean_object* v_constName_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1340_, lean_object* v_constName_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1340_, v_constName_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1348_, lean_object* v_ref_1349_, lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1349_, v_constName_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1357_, lean_object* v_ref_1358_, lean_object* v_constName_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1357_, v_ref_1358_, v_constName_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
lean_dec(v_ref_1358_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1366_, lean_object* v_ref_1367_, lean_object* v_msg_1368_, lean_object* v_declHint_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1367_, v_msg_1368_, v_declHint_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_ref_1377_, lean_object* v_msg_1378_, lean_object* v_declHint_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1376_, v_ref_1377_, v_msg_1378_, v_declHint_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v_ref_1377_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1386_, lean_object* v_declHint_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1386_, v_declHint_1387_, v___y_1391_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1394_, lean_object* v_declHint_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1394_, v_declHint_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1402_, lean_object* v_ref_1403_, lean_object* v_msg_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; 
v___x_1410_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1403_, v_msg_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1411_, lean_object* v_ref_1412_, lean_object* v_msg_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1411_, v_ref_1412_, v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v_ref_1412_);
return v_res_1419_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_unsigned_to_nat(32u);
v___x_1421_ = lean_mk_empty_array_with_capacity(v___x_1420_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1421_);
return v___x_1422_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; 
v___x_1423_ = ((size_t)5ULL);
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_unsigned_to_nat(32u);
v___x_1426_ = lean_mk_empty_array_with_capacity(v___x_1425_);
v___x_1427_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__0);
v___x_1428_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
lean_ctor_set(v___x_1428_, 1, v___x_1426_);
lean_ctor_set(v___x_1428_, 2, v___x_1424_);
lean_ctor_set(v___x_1428_, 3, v___x_1424_);
lean_ctor_set_usize(v___x_1428_, 4, v___x_1423_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; lean_object* v_traceState_1432_; lean_object* v_traces_1433_; lean_object* v___x_1434_; lean_object* v_traceState_1435_; lean_object* v_env_1436_; lean_object* v_nextMacroScope_1437_; lean_object* v_ngen_1438_; lean_object* v_auxDeclNGen_1439_; lean_object* v_cache_1440_; lean_object* v_messages_1441_; lean_object* v_infoState_1442_; lean_object* v_snapshotTasks_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1462_; 
v___x_1431_ = lean_st_ref_get(v___y_1429_);
v_traceState_1432_ = lean_ctor_get(v___x_1431_, 4);
lean_inc_ref(v_traceState_1432_);
lean_dec(v___x_1431_);
v_traces_1433_ = lean_ctor_get(v_traceState_1432_, 0);
lean_inc_ref(v_traces_1433_);
lean_dec_ref(v_traceState_1432_);
v___x_1434_ = lean_st_ref_take(v___y_1429_);
v_traceState_1435_ = lean_ctor_get(v___x_1434_, 4);
v_env_1436_ = lean_ctor_get(v___x_1434_, 0);
v_nextMacroScope_1437_ = lean_ctor_get(v___x_1434_, 1);
v_ngen_1438_ = lean_ctor_get(v___x_1434_, 2);
v_auxDeclNGen_1439_ = lean_ctor_get(v___x_1434_, 3);
v_cache_1440_ = lean_ctor_get(v___x_1434_, 5);
v_messages_1441_ = lean_ctor_get(v___x_1434_, 6);
v_infoState_1442_ = lean_ctor_get(v___x_1434_, 7);
v_snapshotTasks_1443_ = lean_ctor_get(v___x_1434_, 8);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1445_ = v___x_1434_;
v_isShared_1446_ = v_isSharedCheck_1462_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_snapshotTasks_1443_);
lean_inc(v_infoState_1442_);
lean_inc(v_messages_1441_);
lean_inc(v_cache_1440_);
lean_inc(v_traceState_1435_);
lean_inc(v_auxDeclNGen_1439_);
lean_inc(v_ngen_1438_);
lean_inc(v_nextMacroScope_1437_);
lean_inc(v_env_1436_);
lean_dec(v___x_1434_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1462_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
uint64_t v_tid_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1460_; 
v_tid_1447_ = lean_ctor_get_uint64(v_traceState_1435_, sizeof(void*)*1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_traceState_1435_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_traceState_1435_, 0);
lean_dec(v_unused_1461_);
v___x_1449_ = v_traceState_1435_;
v_isShared_1450_ = v_isSharedCheck_1460_;
goto v_resetjp_1448_;
}
else
{
lean_dec(v_traceState_1435_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1460_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1453_; 
v___x_1451_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 0, v___x_1451_);
v___x_1453_ = v___x_1449_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v___x_1451_);
lean_ctor_set_uint64(v_reuseFailAlloc_1459_, sizeof(void*)*1, v_tid_1447_);
v___x_1453_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1455_; 
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1453_);
v___x_1455_ = v___x_1445_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_env_1436_);
lean_ctor_set(v_reuseFailAlloc_1458_, 1, v_nextMacroScope_1437_);
lean_ctor_set(v_reuseFailAlloc_1458_, 2, v_ngen_1438_);
lean_ctor_set(v_reuseFailAlloc_1458_, 3, v_auxDeclNGen_1439_);
lean_ctor_set(v_reuseFailAlloc_1458_, 4, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1458_, 5, v_cache_1440_);
lean_ctor_set(v_reuseFailAlloc_1458_, 6, v_messages_1441_);
lean_ctor_set(v_reuseFailAlloc_1458_, 7, v_infoState_1442_);
lean_ctor_set(v_reuseFailAlloc_1458_, 8, v_snapshotTasks_1443_);
v___x_1455_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_st_ref_put(v___y_1429_, v___x_1455_);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v_traces_1433_);
return v___x_1457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1463_);
lean_dec(v___y_1463_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
return v_res_1477_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1478_, lean_object* v_opt_1479_){
_start:
{
lean_object* v_name_1480_; lean_object* v_defValue_1481_; lean_object* v_map_1482_; lean_object* v___x_1483_; 
v_name_1480_ = lean_ctor_get(v_opt_1479_, 0);
v_defValue_1481_ = lean_ctor_get(v_opt_1479_, 1);
v_map_1482_ = lean_ctor_get(v_opts_1478_, 0);
v___x_1483_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1482_, v_name_1480_);
if (lean_obj_tag(v___x_1483_) == 0)
{
uint8_t v___x_1484_; 
v___x_1484_ = lean_unbox(v_defValue_1481_);
return v___x_1484_;
}
else
{
lean_object* v_val_1485_; 
v_val_1485_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v___x_1483_, 1);
if (lean_obj_tag(v_val_1485_) == 1)
{
uint8_t v_v_1486_; 
v_v_1486_ = lean_ctor_get_uint8(v_val_1485_, 0);
lean_dec_ref_known(v_val_1485_, 0);
return v_v_1486_;
}
else
{
uint8_t v___x_1487_; 
lean_dec(v_val_1485_);
v___x_1487_ = lean_unbox(v_defValue_1481_);
return v___x_1487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1488_, lean_object* v_opt_1489_){
_start:
{
uint8_t v_res_1490_; lean_object* v_r_1491_; 
v_res_1490_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1488_, v_opt_1489_);
lean_dec_ref(v_opt_1489_);
lean_dec_ref(v_opts_1488_);
v_r_1491_ = lean_box(v_res_1490_);
return v_r_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1492_, lean_object* v_x_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = l_Lean_MessageData_ofName(v_indName_1492_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1501_, lean_object* v_x_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_mkBelow___lam__0(v_indName_1501_, v_x_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec_ref(v_x_1502_);
return v_res_1508_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_e_1509_){
_start:
{
if (lean_obj_tag(v_e_1509_) == 0)
{
uint8_t v___x_1510_; 
v___x_1510_ = 2;
return v___x_1510_;
}
else
{
uint8_t v___x_1511_; 
v___x_1511_ = 0;
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_e_1512_){
_start:
{
uint8_t v_res_1513_; lean_object* v_r_1514_; 
v_res_1513_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_e_1512_);
lean_dec_ref(v_e_1512_);
v_r_1514_ = lean_box(v_res_1513_);
return v_r_1514_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(lean_object* v_x_1515_){
_start:
{
if (lean_obj_tag(v_x_1515_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1524_; 
v_a_1517_ = lean_ctor_get(v_x_1515_, 0);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1519_ = v_x_1515_;
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v_x_1515_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1524_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___x_1522_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set_tag(v___x_1519_, 1);
v___x_1522_ = v___x_1519_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
v___x_1522_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
return v___x_1522_;
}
}
}
else
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_a_1525_ = lean_ctor_get(v_x_1515_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_x_1515_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v_x_1515_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v_x_1515_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 0);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg___boxed(lean_object* v_x_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_1533_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1536_, lean_object* v_opt_1537_){
_start:
{
lean_object* v_name_1538_; lean_object* v_defValue_1539_; lean_object* v_map_1540_; lean_object* v___x_1541_; 
v_name_1538_ = lean_ctor_get(v_opt_1537_, 0);
v_defValue_1539_ = lean_ctor_get(v_opt_1537_, 1);
v_map_1540_ = lean_ctor_get(v_opts_1536_, 0);
v___x_1541_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1540_, v_name_1538_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_inc(v_defValue_1539_);
return v_defValue_1539_;
}
else
{
lean_object* v_val_1542_; 
v_val_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_val_1542_);
lean_dec_ref_known(v___x_1541_, 1);
if (lean_obj_tag(v_val_1542_) == 3)
{
lean_object* v_v_1543_; 
v_v_1543_ = lean_ctor_get(v_val_1542_, 0);
lean_inc(v_v_1543_);
lean_dec_ref_known(v_val_1542_, 1);
return v_v_1543_;
}
else
{
lean_dec(v_val_1542_);
lean_inc(v_defValue_1539_);
return v_defValue_1539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1544_, lean_object* v_opt_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1544_, v_opt_1545_);
lean_dec_ref(v_opt_1545_);
lean_dec_ref(v_opts_1544_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(size_t v_sz_1547_, size_t v_i_1548_, lean_object* v_bs_1549_){
_start:
{
uint8_t v___x_1550_; 
v___x_1550_ = lean_usize_dec_lt(v_i_1548_, v_sz_1547_);
if (v___x_1550_ == 0)
{
return v_bs_1549_;
}
else
{
lean_object* v_v_1551_; lean_object* v_msg_1552_; lean_object* v___x_1553_; lean_object* v_bs_x27_1554_; size_t v___x_1555_; size_t v___x_1556_; lean_object* v___x_1557_; 
v_v_1551_ = lean_array_uget_borrowed(v_bs_1549_, v_i_1548_);
v_msg_1552_ = lean_ctor_get(v_v_1551_, 1);
lean_inc_ref(v_msg_1552_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v_bs_x27_1554_ = lean_array_uset(v_bs_1549_, v_i_1548_, v___x_1553_);
v___x_1555_ = ((size_t)1ULL);
v___x_1556_ = lean_usize_add(v_i_1548_, v___x_1555_);
v___x_1557_ = lean_array_uset(v_bs_x27_1554_, v_i_1548_, v_msg_1552_);
v_i_1548_ = v___x_1556_;
v_bs_1549_ = v___x_1557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4___boxed(lean_object* v_sz_1559_, lean_object* v_i_1560_, lean_object* v_bs_1561_){
_start:
{
size_t v_sz_boxed_1562_; size_t v_i_boxed_1563_; lean_object* v_res_1564_; 
v_sz_boxed_1562_ = lean_unbox_usize(v_sz_1559_);
lean_dec(v_sz_1559_);
v_i_boxed_1563_ = lean_unbox_usize(v_i_1560_);
lean_dec(v_i_1560_);
v_res_1564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_boxed_1562_, v_i_boxed_1563_, v_bs_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_oldTraces_1565_, lean_object* v_data_1566_, lean_object* v_ref_1567_, lean_object* v_msg_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v_toCold_1574_; lean_object* v_currRecDepth_1575_; lean_object* v_ref_1576_; uint8_t v_diag_1577_; uint8_t v_suppressElabErrors_1578_; lean_object* v___x_1579_; lean_object* v_traceState_1580_; lean_object* v_traces_1581_; lean_object* v_ref_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; lean_object* v_msg_1588_; lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1627_; 
v_toCold_1574_ = lean_ctor_get(v___y_1571_, 0);
v_currRecDepth_1575_ = lean_ctor_get(v___y_1571_, 1);
v_ref_1576_ = lean_ctor_get(v___y_1571_, 2);
v_diag_1577_ = lean_ctor_get_uint8(v___y_1571_, sizeof(void*)*3);
v_suppressElabErrors_1578_ = lean_ctor_get_uint8(v___y_1571_, sizeof(void*)*3 + 1);
v___x_1579_ = lean_st_ref_get(v___y_1572_);
v_traceState_1580_ = lean_ctor_get(v___x_1579_, 4);
lean_inc_ref(v_traceState_1580_);
lean_dec(v___x_1579_);
v_traces_1581_ = lean_ctor_get(v_traceState_1580_, 0);
lean_inc_ref(v_traces_1581_);
lean_dec_ref(v_traceState_1580_);
v_ref_1582_ = l_Lean_replaceRef(v_ref_1567_, v_ref_1576_);
lean_inc(v_currRecDepth_1575_);
lean_inc_ref(v_toCold_1574_);
v___x_1583_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1583_, 0, v_toCold_1574_);
lean_ctor_set(v___x_1583_, 1, v_currRecDepth_1575_);
lean_ctor_set(v___x_1583_, 2, v_ref_1582_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*3, v_diag_1577_);
lean_ctor_set_uint8(v___x_1583_, sizeof(void*)*3 + 1, v_suppressElabErrors_1578_);
v___x_1584_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1581_);
lean_dec_ref(v_traces_1581_);
v_sz_1585_ = lean_array_size(v___x_1584_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3_spec__4(v_sz_1585_, v___x_1586_, v___x_1584_);
v_msg_1588_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1588_, 0, v_data_1566_);
lean_ctor_set(v_msg_1588_, 1, v_msg_1568_);
lean_ctor_set(v_msg_1588_, 2, v___x_1587_);
v___x_1589_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1588_, v___y_1569_, v___y_1570_, v___x_1583_, v___y_1572_);
lean_dec_ref_known(v___x_1583_, 3);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1627_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1627_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v_traceState_1595_; lean_object* v_env_1596_; lean_object* v_nextMacroScope_1597_; lean_object* v_ngen_1598_; lean_object* v_auxDeclNGen_1599_; lean_object* v_cache_1600_; lean_object* v_messages_1601_; lean_object* v_infoState_1602_; lean_object* v_snapshotTasks_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1626_; 
v___x_1594_ = lean_st_ref_take(v___y_1572_);
v_traceState_1595_ = lean_ctor_get(v___x_1594_, 4);
v_env_1596_ = lean_ctor_get(v___x_1594_, 0);
v_nextMacroScope_1597_ = lean_ctor_get(v___x_1594_, 1);
v_ngen_1598_ = lean_ctor_get(v___x_1594_, 2);
v_auxDeclNGen_1599_ = lean_ctor_get(v___x_1594_, 3);
v_cache_1600_ = lean_ctor_get(v___x_1594_, 5);
v_messages_1601_ = lean_ctor_get(v___x_1594_, 6);
v_infoState_1602_ = lean_ctor_get(v___x_1594_, 7);
v_snapshotTasks_1603_ = lean_ctor_get(v___x_1594_, 8);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1605_ = v___x_1594_;
v_isShared_1606_ = v_isSharedCheck_1626_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_snapshotTasks_1603_);
lean_inc(v_infoState_1602_);
lean_inc(v_messages_1601_);
lean_inc(v_cache_1600_);
lean_inc(v_traceState_1595_);
lean_inc(v_auxDeclNGen_1599_);
lean_inc(v_ngen_1598_);
lean_inc(v_nextMacroScope_1597_);
lean_inc(v_env_1596_);
lean_dec(v___x_1594_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1626_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
uint64_t v_tid_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1624_; 
v_tid_1607_ = lean_ctor_get_uint64(v_traceState_1595_, sizeof(void*)*1);
v_isSharedCheck_1624_ = !lean_is_exclusive(v_traceState_1595_);
if (v_isSharedCheck_1624_ == 0)
{
lean_object* v_unused_1625_; 
v_unused_1625_ = lean_ctor_get(v_traceState_1595_, 0);
lean_dec(v_unused_1625_);
v___x_1609_ = v_traceState_1595_;
v_isShared_1610_ = v_isSharedCheck_1624_;
goto v_resetjp_1608_;
}
else
{
lean_dec(v_traceState_1595_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1624_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1611_, 0, v_ref_1567_);
lean_ctor_set(v___x_1611_, 1, v_a_1590_);
v___x_1612_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1565_, v___x_1611_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1612_);
v___x_1614_ = v___x_1609_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1612_);
lean_ctor_set_uint64(v_reuseFailAlloc_1623_, sizeof(void*)*1, v_tid_1607_);
v___x_1614_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
lean_object* v___x_1616_; 
if (v_isShared_1606_ == 0)
{
lean_ctor_set(v___x_1605_, 4, v___x_1614_);
v___x_1616_ = v___x_1605_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_env_1596_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_nextMacroScope_1597_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v_ngen_1598_);
lean_ctor_set(v_reuseFailAlloc_1622_, 3, v_auxDeclNGen_1599_);
lean_ctor_set(v_reuseFailAlloc_1622_, 4, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1622_, 5, v_cache_1600_);
lean_ctor_set(v_reuseFailAlloc_1622_, 6, v_messages_1601_);
lean_ctor_set(v_reuseFailAlloc_1622_, 7, v_infoState_1602_);
lean_ctor_set(v_reuseFailAlloc_1622_, 8, v_snapshotTasks_1603_);
v___x_1616_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1617_ = lean_st_ref_put(v___y_1572_, v___x_1616_);
v___x_1618_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 0, v___x_1618_);
v___x_1620_ = v___x_1592_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_oldTraces_1628_, lean_object* v_data_1629_, lean_object* v_ref_1630_, lean_object* v_msg_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1628_, v_data_1629_, v_ref_1630_, v_msg_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
return v_res_1637_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1638_; double v___x_1639_; 
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_float_of_nat(v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1));
v___x_1642_ = l_Lean_stringToMessageData(v___x_1641_);
return v___x_1642_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1643_; double v___x_1644_; 
v___x_1643_ = lean_unsigned_to_nat(1000u);
v___x_1644_ = lean_float_of_nat(v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1645_, uint8_t v_collapsed_1646_, lean_object* v_tag_1647_, lean_object* v_opts_1648_, uint8_t v_clsEnabled_1649_, lean_object* v_oldTraces_1650_, lean_object* v_msg_1651_, lean_object* v_resStartStop_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_fst_1658_; lean_object* v_snd_1659_; lean_object* v___y_1661_; lean_object* v___y_1662_; lean_object* v_data_1663_; lean_object* v_fst_1666_; lean_object* v_snd_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; lean_object* v___y_1671_; lean_object* v_a_1672_; uint8_t v___y_1687_; double v___y_1718_; 
v_fst_1658_ = lean_ctor_get(v_resStartStop_1652_, 0);
lean_inc(v_fst_1658_);
v_snd_1659_ = lean_ctor_get(v_resStartStop_1652_, 1);
lean_inc(v_snd_1659_);
lean_dec_ref(v_resStartStop_1652_);
v_fst_1666_ = lean_ctor_get(v_snd_1659_, 0);
lean_inc(v_fst_1666_);
v_snd_1667_ = lean_ctor_get(v_snd_1659_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_snd_1659_);
v___x_1668_ = l_Lean_trace_profiler;
v___x_1669_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1648_, v___x_1668_);
if (v___x_1669_ == 0)
{
v___y_1687_ = v___x_1669_;
goto v___jp_1686_;
}
else
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1724_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1648_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; double v___x_1727_; double v___x_1728_; double v___x_1729_; 
v___x_1725_ = l_Lean_trace_profiler_threshold;
v___x_1726_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1648_, v___x_1725_);
v___x_1727_ = lean_float_of_nat(v___x_1726_);
v___x_1728_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3);
v___x_1729_ = lean_float_div(v___x_1727_, v___x_1728_);
v___y_1718_ = v___x_1729_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; double v___x_1732_; 
v___x_1730_ = l_Lean_trace_profiler_threshold;
v___x_1731_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1648_, v___x_1730_);
v___x_1732_ = lean_float_of_nat(v___x_1731_);
v___y_1718_ = v___x_1732_;
goto v___jp_1717_;
}
}
v___jp_1660_:
{
lean_object* v___x_1664_; 
lean_inc(v___y_1662_);
v___x_1664_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_oldTraces_1650_, v_data_1663_, v___y_1662_, v___y_1661_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref_known(v___x_1664_, 1);
v___x_1665_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1658_);
return v___x_1665_;
}
else
{
lean_dec(v_fst_1658_);
return v___x_1664_;
}
}
v___jp_1670_:
{
uint8_t v_result_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; double v___x_1676_; lean_object* v_data_1677_; 
v_result_1673_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_fst_1658_);
v___x_1674_ = lean_box(v_result_1673_);
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
v___x_1676_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0);
lean_inc_ref(v_tag_1647_);
lean_inc_ref(v___x_1675_);
lean_inc(v_cls_1645_);
v_data_1677_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1677_, 0, v_cls_1645_);
lean_ctor_set(v_data_1677_, 1, v___x_1675_);
lean_ctor_set(v_data_1677_, 2, v_tag_1647_);
lean_ctor_set_float(v_data_1677_, sizeof(void*)*3, v___x_1676_);
lean_ctor_set_float(v_data_1677_, sizeof(void*)*3 + 8, v___x_1676_);
lean_ctor_set_uint8(v_data_1677_, sizeof(void*)*3 + 16, v_collapsed_1646_);
if (v___x_1669_ == 0)
{
lean_dec_ref_known(v___x_1675_, 1);
lean_dec(v_snd_1667_);
lean_dec(v_fst_1666_);
lean_dec_ref(v_tag_1647_);
lean_dec(v_cls_1645_);
v___y_1661_ = v_a_1672_;
v___y_1662_ = v___y_1671_;
v_data_1663_ = v_data_1677_;
goto v___jp_1660_;
}
else
{
lean_object* v_data_1678_; double v___x_1679_; double v___x_1680_; 
lean_dec_ref_known(v_data_1677_, 3);
v_data_1678_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1678_, 0, v_cls_1645_);
lean_ctor_set(v_data_1678_, 1, v___x_1675_);
lean_ctor_set(v_data_1678_, 2, v_tag_1647_);
v___x_1679_ = lean_unbox_float(v_fst_1666_);
lean_dec(v_fst_1666_);
lean_ctor_set_float(v_data_1678_, sizeof(void*)*3, v___x_1679_);
v___x_1680_ = lean_unbox_float(v_snd_1667_);
lean_dec(v_snd_1667_);
lean_ctor_set_float(v_data_1678_, sizeof(void*)*3 + 8, v___x_1680_);
lean_ctor_set_uint8(v_data_1678_, sizeof(void*)*3 + 16, v_collapsed_1646_);
v___y_1661_ = v_a_1672_;
v___y_1662_ = v___y_1671_;
v_data_1663_ = v_data_1678_;
goto v___jp_1660_;
}
}
v___jp_1681_:
{
lean_object* v_ref_1682_; lean_object* v___x_1683_; 
v_ref_1682_ = lean_ctor_get(v___y_1655_, 2);
lean_inc(v___y_1656_);
lean_inc_ref(v___y_1655_);
lean_inc(v___y_1654_);
lean_inc_ref(v___y_1653_);
lean_inc(v_fst_1658_);
v___x_1683_ = lean_apply_6(v_msg_1651_, v_fst_1658_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, lean_box(0));
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref_known(v___x_1683_, 1);
v___y_1671_ = v_ref_1682_;
v_a_1672_ = v_a_1684_;
goto v___jp_1670_;
}
else
{
lean_object* v___x_1685_; 
lean_dec_ref_known(v___x_1683_, 1);
v___x_1685_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
v___y_1671_ = v_ref_1682_;
v_a_1672_ = v___x_1685_;
goto v___jp_1670_;
}
}
v___jp_1686_:
{
if (v_clsEnabled_1649_ == 0)
{
if (v___y_1687_ == 0)
{
lean_object* v___x_1688_; lean_object* v_traceState_1689_; lean_object* v_env_1690_; lean_object* v_nextMacroScope_1691_; lean_object* v_ngen_1692_; lean_object* v_auxDeclNGen_1693_; lean_object* v_cache_1694_; lean_object* v_messages_1695_; lean_object* v_infoState_1696_; lean_object* v_snapshotTasks_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_snd_1667_);
lean_dec(v_fst_1666_);
lean_dec_ref(v_msg_1651_);
lean_dec_ref(v_tag_1647_);
lean_dec(v_cls_1645_);
v___x_1688_ = lean_st_ref_take(v___y_1656_);
v_traceState_1689_ = lean_ctor_get(v___x_1688_, 4);
v_env_1690_ = lean_ctor_get(v___x_1688_, 0);
v_nextMacroScope_1691_ = lean_ctor_get(v___x_1688_, 1);
v_ngen_1692_ = lean_ctor_get(v___x_1688_, 2);
v_auxDeclNGen_1693_ = lean_ctor_get(v___x_1688_, 3);
v_cache_1694_ = lean_ctor_get(v___x_1688_, 5);
v_messages_1695_ = lean_ctor_get(v___x_1688_, 6);
v_infoState_1696_ = lean_ctor_get(v___x_1688_, 7);
v_snapshotTasks_1697_ = lean_ctor_get(v___x_1688_, 8);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1699_ = v___x_1688_;
v_isShared_1700_ = v_isSharedCheck_1716_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snapshotTasks_1697_);
lean_inc(v_infoState_1696_);
lean_inc(v_messages_1695_);
lean_inc(v_cache_1694_);
lean_inc(v_traceState_1689_);
lean_inc(v_auxDeclNGen_1693_);
lean_inc(v_ngen_1692_);
lean_inc(v_nextMacroScope_1691_);
lean_inc(v_env_1690_);
lean_dec(v___x_1688_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1716_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
uint64_t v_tid_1701_; lean_object* v_traces_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1715_; 
v_tid_1701_ = lean_ctor_get_uint64(v_traceState_1689_, sizeof(void*)*1);
v_traces_1702_ = lean_ctor_get(v_traceState_1689_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_traceState_1689_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1704_ = v_traceState_1689_;
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_traces_1702_);
lean_dec(v_traceState_1689_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1715_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1650_, v_traces_1702_);
lean_dec_ref(v_traces_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1706_);
lean_ctor_set_uint64(v_reuseFailAlloc_1714_, sizeof(void*)*1, v_tid_1701_);
v___x_1708_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1710_; 
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 4, v___x_1708_);
v___x_1710_ = v___x_1699_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_env_1690_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v_nextMacroScope_1691_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_ngen_1692_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_auxDeclNGen_1693_);
lean_ctor_set(v_reuseFailAlloc_1713_, 4, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1713_, 5, v_cache_1694_);
lean_ctor_set(v_reuseFailAlloc_1713_, 6, v_messages_1695_);
lean_ctor_set(v_reuseFailAlloc_1713_, 7, v_infoState_1696_);
lean_ctor_set(v_reuseFailAlloc_1713_, 8, v_snapshotTasks_1697_);
v___x_1710_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = lean_st_ref_put(v___y_1656_, v___x_1710_);
v___x_1712_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_fst_1658_);
return v___x_1712_;
}
}
}
}
}
else
{
goto v___jp_1681_;
}
}
else
{
goto v___jp_1681_;
}
}
v___jp_1717_:
{
double v___x_1719_; double v___x_1720_; double v___x_1721_; uint8_t v___x_1722_; 
v___x_1719_ = lean_unbox_float(v_snd_1667_);
v___x_1720_ = lean_unbox_float(v_fst_1666_);
v___x_1721_ = lean_float_sub(v___x_1719_, v___x_1720_);
v___x_1722_ = lean_float_decLt(v___y_1718_, v___x_1721_);
v___y_1687_ = v___x_1722_;
goto v___jp_1686_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1733_, lean_object* v_collapsed_1734_, lean_object* v_tag_1735_, lean_object* v_opts_1736_, lean_object* v_clsEnabled_1737_, lean_object* v_oldTraces_1738_, lean_object* v_msg_1739_, lean_object* v_resStartStop_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
uint8_t v_collapsed_boxed_1746_; uint8_t v_clsEnabled_boxed_1747_; lean_object* v_res_1748_; 
v_collapsed_boxed_1746_ = lean_unbox(v_collapsed_1734_);
v_clsEnabled_boxed_1747_ = lean_unbox(v_clsEnabled_1737_);
v_res_1748_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1733_, v_collapsed_boxed_1746_, v_tag_1735_, v_opts_1736_, v_clsEnabled_boxed_1747_, v_oldTraces_1738_, v_msg_1739_, v_resStartStop_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_opts_1736_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1749_, lean_object* v___x_1750_, lean_object* v___x_1751_, lean_object* v___x_1752_, lean_object* v_a_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_nat_dec_lt(v_a_1753_, v_upperBound_1749_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
lean_dec(v_a_1753_);
lean_dec(v___x_1752_);
lean_dec(v___x_1751_);
lean_dec(v___x_1750_);
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_b_1754_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1762_ = lean_unsigned_to_nat(1u);
v___x_1763_ = lean_nat_add(v_a_1753_, v___x_1762_);
lean_dec(v_a_1753_);
lean_inc_n(v___x_1763_, 2);
lean_inc(v___x_1750_);
v___x_1764_ = lean_name_append_index_after(v___x_1750_, v___x_1763_);
lean_inc(v___x_1751_);
v___x_1765_ = lean_name_append_index_after(v___x_1751_, v___x_1763_);
lean_inc(v___x_1752_);
v___x_1766_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1764_, v___x_1752_, v___x_1765_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v___x_1767_; 
lean_dec_ref_known(v___x_1766_, 1);
v___x_1767_ = lean_box(0);
v_a_1753_ = v___x_1763_;
v_b_1754_ = v___x_1767_;
goto _start;
}
else
{
lean_dec(v___x_1763_);
lean_dec(v___x_1752_);
lean_dec(v___x_1751_);
lean_dec(v___x_1750_);
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1769_, lean_object* v___x_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, lean_object* v_a_1773_, lean_object* v_b_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1769_, v___x_1770_, v___x_1771_, v___x_1772_, v_a_1773_, v_b_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
lean_dec(v_upperBound_1769_);
return v_res_1780_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1791_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1792_ = l_Lean_Name_append(v___x_1791_, v___x_1790_);
return v___x_1792_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1793_; double v___x_1794_; 
v___x_1793_ = lean_unsigned_to_nat(1000000000u);
v___x_1794_ = lean_float_of_nat(v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v_toCold_1801_; lean_object* v_options_1802_; lean_object* v_inheritedTraceOptions_1803_; uint8_t v_hasTrace_1804_; lean_object* v___x_1805_; 
v_toCold_1801_ = lean_ctor_get(v_a_1798_, 0);
v_options_1802_ = lean_ctor_get(v_toCold_1801_, 2);
v_inheritedTraceOptions_1803_ = lean_ctor_get(v_toCold_1801_, 11);
v_hasTrace_1804_ = lean_ctor_get_uint8(v_options_1802_, sizeof(void*)*1);
v___x_1805_ = lean_box(0);
if (v_hasTrace_1804_ == 0)
{
lean_object* v___x_1806_; 
lean_inc(v_indName_1795_);
v___x_1806_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1870_; 
v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1809_ = v___x_1806_;
v_isShared_1810_ = v_isSharedCheck_1870_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___x_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1870_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
if (lean_obj_tag(v_a_1807_) == 5)
{
lean_object* v_val_1811_; uint8_t v_isRec_1812_; 
v_val_1811_ = lean_ctor_get(v_a_1807_, 0);
lean_inc_ref(v_val_1811_);
lean_dec_ref_known(v_a_1807_, 1);
v_isRec_1812_ = lean_ctor_get_uint8(v_val_1811_, sizeof(void*)*6);
if (v_isRec_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
lean_dec_ref(v_val_1811_);
lean_dec(v_indName_1795_);
v___x_1813_ = lean_box(0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1813_);
v___x_1815_ = v___x_1809_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1813_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
else
{
lean_object* v_toConstantVal_1817_; lean_object* v_numParams_1818_; lean_object* v_all_1819_; lean_object* v_numNested_1820_; lean_object* v_type_1821_; lean_object* v___x_1822_; 
lean_del_object(v___x_1809_);
v_toConstantVal_1817_ = lean_ctor_get(v_val_1811_, 0);
lean_inc_ref(v_toConstantVal_1817_);
v_numParams_1818_ = lean_ctor_get(v_val_1811_, 1);
lean_inc(v_numParams_1818_);
v_all_1819_ = lean_ctor_get(v_val_1811_, 3);
lean_inc(v_all_1819_);
v_numNested_1820_ = lean_ctor_get(v_val_1811_, 5);
lean_inc(v_numNested_1820_);
lean_dec_ref(v_val_1811_);
v_type_1821_ = lean_ctor_get(v_toConstantVal_1817_, 2);
lean_inc_ref(v_type_1821_);
lean_dec_ref(v_toConstantVal_1817_);
v___x_1822_ = l_Lean_Meta_isPropFormerType(v_type_1821_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1857_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1825_ = v___x_1822_;
v_isShared_1826_ = v_isSharedCheck_1857_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1822_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1857_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
uint8_t v___x_1827_; 
v___x_1827_ = lean_unbox(v_a_1823_);
lean_dec(v_a_1823_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
lean_del_object(v___x_1825_);
lean_inc_n(v_indName_1795_, 2);
v___x_1828_ = l_Lean_mkRecName(v_indName_1795_);
v___x_1829_ = l_Lean_mkBelowName(v_indName_1795_);
lean_inc(v___x_1829_);
lean_inc(v_numParams_1818_);
lean_inc(v___x_1828_);
v___x_1830_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1828_, v_numParams_1818_, v___x_1829_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1851_; 
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; 
v_unused_1852_ = lean_ctor_get(v___x_1830_, 0);
lean_dec(v_unused_1852_);
v___x_1832_ = v___x_1830_;
v_isShared_1833_ = v_isSharedCheck_1851_;
goto v_resetjp_1831_;
}
else
{
lean_dec(v___x_1830_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1851_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = l_List_get_x21Internal___redArg(v___x_1805_, v_all_1819_, v___x_1834_);
lean_dec(v_all_1819_);
v___x_1836_ = lean_name_eq(v___x_1835_, v_indName_1795_);
lean_dec(v_indName_1795_);
lean_dec(v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_dec(v___x_1829_);
lean_dec(v___x_1828_);
lean_dec(v_numNested_1820_);
lean_dec(v_numParams_1818_);
v___x_1837_ = lean_box(0);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1837_);
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
lean_del_object(v___x_1832_);
v___x_1841_ = lean_box(0);
v___x_1842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1820_, v___x_1828_, v___x_1829_, v_numParams_1818_, v___x_1834_, v___x_1841_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_numNested_1820_);
if (lean_obj_tag(v___x_1842_) == 0)
{
lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1849_; 
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1842_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v___x_1842_, 0);
lean_dec(v_unused_1850_);
v___x_1844_ = v___x_1842_;
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
else
{
lean_dec(v___x_1842_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1849_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1847_; 
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1841_);
v___x_1847_ = v___x_1844_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1841_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
else
{
return v___x_1842_;
}
}
}
}
else
{
lean_dec(v___x_1829_);
lean_dec(v___x_1828_);
lean_dec(v_numNested_1820_);
lean_dec(v_all_1819_);
lean_dec(v_numParams_1818_);
lean_dec(v_indName_1795_);
return v___x_1830_;
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec(v_numNested_1820_);
lean_dec(v_all_1819_);
lean_dec(v_numParams_1818_);
lean_dec(v_indName_1795_);
v___x_1853_ = lean_box(0);
if (v_isShared_1826_ == 0)
{
lean_ctor_set(v___x_1825_, 0, v___x_1853_);
v___x_1855_ = v___x_1825_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_dec(v_numNested_1820_);
lean_dec(v_all_1819_);
lean_dec(v_numParams_1818_);
lean_dec(v_indName_1795_);
v_a_1858_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1822_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1822_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
else
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_dec(v_a_1807_);
lean_dec(v_indName_1795_);
v___x_1866_ = lean_box(0);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 0, v___x_1866_);
v___x_1868_ = v___x_1809_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
else
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_indName_1795_);
v_a_1871_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1806_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1806_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_a_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
else
{
lean_object* v___f_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v_a_1887_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v_a_1902_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v_a_1907_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v_a_1912_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v_a_1924_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v_a_1929_; 
lean_inc(v_indName_1795_);
v___f_1879_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1879_, 0, v_indName_1795_);
v___x_1880_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1881_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1882_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1883_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1803_, v_options_1802_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1996_; uint8_t v___x_1997_; 
v___x_1996_ = l_Lean_trace_profiler;
v___x_1997_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1802_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_dec_ref(v___f_1879_);
lean_inc(v_indName_1795_);
v___x_1998_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2062_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2062_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2062_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
if (lean_obj_tag(v_a_1999_) == 5)
{
lean_object* v_val_2003_; uint8_t v_isRec_2004_; 
v_val_2003_ = lean_ctor_get(v_a_1999_, 0);
lean_inc_ref(v_val_2003_);
lean_dec_ref_known(v_a_1999_, 1);
v_isRec_2004_ = lean_ctor_get_uint8(v_val_2003_, sizeof(void*)*6);
if (v_isRec_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
lean_dec_ref(v_val_2003_);
lean_dec(v_indName_1795_);
v___x_2005_ = lean_box(0);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2005_);
v___x_2007_ = v___x_2001_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2005_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
else
{
lean_object* v_toConstantVal_2009_; lean_object* v_numParams_2010_; lean_object* v_all_2011_; lean_object* v_numNested_2012_; lean_object* v_type_2013_; lean_object* v___x_2014_; 
lean_del_object(v___x_2001_);
v_toConstantVal_2009_ = lean_ctor_get(v_val_2003_, 0);
lean_inc_ref(v_toConstantVal_2009_);
v_numParams_2010_ = lean_ctor_get(v_val_2003_, 1);
lean_inc(v_numParams_2010_);
v_all_2011_ = lean_ctor_get(v_val_2003_, 3);
lean_inc(v_all_2011_);
v_numNested_2012_ = lean_ctor_get(v_val_2003_, 5);
lean_inc(v_numNested_2012_);
lean_dec_ref(v_val_2003_);
v_type_2013_ = lean_ctor_get(v_toConstantVal_2009_, 2);
lean_inc_ref(v_type_2013_);
lean_dec_ref(v_toConstantVal_2009_);
v___x_2014_ = l_Lean_Meta_isPropFormerType(v_type_2013_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2049_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2017_ = v___x_2014_;
v_isShared_2018_ = v_isSharedCheck_2049_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_a_2015_);
lean_dec(v___x_2014_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2049_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_unbox(v_a_2015_);
lean_dec(v_a_2015_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_del_object(v___x_2017_);
lean_inc_n(v_indName_1795_, 2);
v___x_2020_ = l_Lean_mkRecName(v_indName_1795_);
v___x_2021_ = l_Lean_mkBelowName(v_indName_1795_);
lean_inc(v___x_2021_);
lean_inc(v_numParams_2010_);
lean_inc(v___x_2020_);
v___x_2022_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2020_, v_numParams_2010_, v___x_2021_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2043_; 
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2043_ == 0)
{
lean_object* v_unused_2044_; 
v_unused_2044_ = lean_ctor_get(v___x_2022_, 0);
lean_dec(v_unused_2044_);
v___x_2024_ = v___x_2022_;
v_isShared_2025_ = v_isSharedCheck_2043_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v___x_2022_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2043_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2026_ = lean_unsigned_to_nat(0u);
v___x_2027_ = l_List_get_x21Internal___redArg(v___x_1805_, v_all_2011_, v___x_2026_);
lean_dec(v_all_2011_);
v___x_2028_ = lean_name_eq(v___x_2027_, v_indName_1795_);
lean_dec(v_indName_1795_);
lean_dec(v___x_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
lean_dec(v___x_2021_);
lean_dec(v___x_2020_);
lean_dec(v_numNested_2012_);
lean_dec(v_numParams_2010_);
v___x_2029_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2029_);
v___x_2031_ = v___x_2024_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_del_object(v___x_2024_);
v___x_2033_ = lean_box(0);
v___x_2034_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2012_, v___x_2020_, v___x_2021_, v_numParams_2010_, v___x_2026_, v___x_2033_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_numNested_2012_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v___x_2034_, 0);
lean_dec(v_unused_2042_);
v___x_2036_ = v___x_2034_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_dec(v___x_2034_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2033_);
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2033_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
else
{
return v___x_2034_;
}
}
}
}
else
{
lean_dec(v___x_2021_);
lean_dec(v___x_2020_);
lean_dec(v_numNested_2012_);
lean_dec(v_all_2011_);
lean_dec(v_numParams_2010_);
lean_dec(v_indName_1795_);
return v___x_2022_;
}
}
else
{
lean_object* v___x_2045_; lean_object* v___x_2047_; 
lean_dec(v_numNested_2012_);
lean_dec(v_all_2011_);
lean_dec(v_numParams_2010_);
lean_dec(v_indName_1795_);
v___x_2045_ = lean_box(0);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 0, v___x_2045_);
v___x_2047_ = v___x_2017_;
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
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_numNested_2012_);
lean_dec(v_all_2011_);
lean_dec(v_numParams_2010_);
lean_dec(v_indName_1795_);
v_a_2050_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2014_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2014_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
else
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
lean_dec(v_a_1999_);
lean_dec(v_indName_1795_);
v___x_2058_ = lean_box(0);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2058_);
v___x_2060_ = v___x_2001_;
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
lean_dec(v_indName_1795_);
v_a_2063_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_1998_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_1998_);
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
else
{
goto v___jp_1931_;
}
}
else
{
goto v___jp_1931_;
}
v___jp_1884_:
{
lean_object* v___x_1888_; double v___x_1889_; double v___x_1890_; double v___x_1891_; double v___x_1892_; double v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1888_ = lean_io_mono_nanos_now();
v___x_1889_ = lean_float_of_nat(v___y_1886_);
v___x_1890_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1891_ = lean_float_div(v___x_1889_, v___x_1890_);
v___x_1892_ = lean_float_of_nat(v___x_1888_);
v___x_1893_ = lean_float_div(v___x_1892_, v___x_1890_);
v___x_1894_ = lean_box_float(v___x_1891_);
v___x_1895_ = lean_box_float(v___x_1893_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1897_, 0, v_a_1887_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1880_, v_hasTrace_1804_, v___x_1881_, v_options_1802_, v___x_1883_, v___y_1885_, v___f_1879_, v___x_1897_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
return v___x_1898_;
}
v___jp_1899_:
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_a_1902_);
v___y_1885_ = v___y_1900_;
v___y_1886_ = v___y_1901_;
v_a_1887_ = v___x_1903_;
goto v___jp_1884_;
}
v___jp_1904_:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_a_1907_);
v___y_1885_ = v___y_1905_;
v___y_1886_ = v___y_1906_;
v_a_1887_ = v___x_1908_;
goto v___jp_1884_;
}
v___jp_1909_:
{
lean_object* v___x_1913_; double v___x_1914_; double v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1913_ = lean_io_get_num_heartbeats();
v___x_1914_ = lean_float_of_nat(v___y_1911_);
v___x_1915_ = lean_float_of_nat(v___x_1913_);
v___x_1916_ = lean_box_float(v___x_1914_);
v___x_1917_ = lean_box_float(v___x_1915_);
v___x_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_a_1912_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1880_, v_hasTrace_1804_, v___x_1881_, v_options_1802_, v___x_1883_, v___y_1910_, v___f_1879_, v___x_1919_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
return v___x_1920_;
}
v___jp_1921_:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_a_1924_);
v___y_1910_ = v___y_1922_;
v___y_1911_ = v___y_1923_;
v_a_1912_ = v___x_1925_;
goto v___jp_1909_;
}
v___jp_1926_:
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_a_1929_);
v___y_1910_ = v___y_1927_;
v___y_1911_ = v___y_1928_;
v_a_1912_ = v___x_1930_;
goto v___jp_1909_;
}
v___jp_1931_:
{
lean_object* v___x_1932_; lean_object* v_a_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1932_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1799_);
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
v___x_1934_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1935_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1802_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1795_);
v___x_1937_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
if (lean_obj_tag(v_a_1938_) == 5)
{
lean_object* v_val_1939_; uint8_t v_isRec_1940_; 
v_val_1939_ = lean_ctor_get(v_a_1938_, 0);
lean_inc_ref(v_val_1939_);
lean_dec_ref_known(v_a_1938_, 1);
v_isRec_1940_ = lean_ctor_get_uint8(v_val_1939_, sizeof(void*)*6);
if (v_isRec_1940_ == 0)
{
lean_object* v___x_1941_; 
lean_dec_ref(v_val_1939_);
lean_dec(v_indName_1795_);
v___x_1941_ = lean_box(0);
v___y_1900_ = v_a_1933_;
v___y_1901_ = v___x_1936_;
v_a_1902_ = v___x_1941_;
goto v___jp_1899_;
}
else
{
lean_object* v_toConstantVal_1942_; lean_object* v_numParams_1943_; lean_object* v_all_1944_; lean_object* v_numNested_1945_; lean_object* v_type_1946_; lean_object* v___x_1947_; 
v_toConstantVal_1942_ = lean_ctor_get(v_val_1939_, 0);
lean_inc_ref(v_toConstantVal_1942_);
v_numParams_1943_ = lean_ctor_get(v_val_1939_, 1);
lean_inc(v_numParams_1943_);
v_all_1944_ = lean_ctor_get(v_val_1939_, 3);
lean_inc(v_all_1944_);
v_numNested_1945_ = lean_ctor_get(v_val_1939_, 5);
lean_inc(v_numNested_1945_);
lean_dec_ref(v_val_1939_);
v_type_1946_ = lean_ctor_get(v_toConstantVal_1942_, 2);
lean_inc_ref(v_type_1946_);
lean_dec_ref(v_toConstantVal_1942_);
v___x_1947_ = l_Lean_Meta_isPropFormerType(v_type_1946_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; uint8_t v___x_1949_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = lean_unbox(v_a_1948_);
lean_dec(v_a_1948_);
if (v___x_1949_ == 0)
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_inc_n(v_indName_1795_, 2);
v___x_1950_ = l_Lean_mkRecName(v_indName_1795_);
v___x_1951_ = l_Lean_mkBelowName(v_indName_1795_);
lean_inc(v___x_1951_);
lean_inc(v_numParams_1943_);
lean_inc(v___x_1950_);
v___x_1952_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1950_, v_numParams_1943_, v___x_1951_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1954_; uint8_t v___x_1955_; 
lean_dec_ref_known(v___x_1952_, 1);
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = l_List_get_x21Internal___redArg(v___x_1805_, v_all_1944_, v___x_1953_);
lean_dec(v_all_1944_);
v___x_1955_ = lean_name_eq(v___x_1954_, v_indName_1795_);
lean_dec(v_indName_1795_);
lean_dec(v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_dec(v___x_1951_);
lean_dec(v___x_1950_);
lean_dec(v_numNested_1945_);
lean_dec(v_numParams_1943_);
v___x_1956_ = lean_box(0);
v___y_1900_ = v_a_1933_;
v___y_1901_ = v___x_1936_;
v_a_1902_ = v___x_1956_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1957_ = lean_box(0);
v___x_1958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1945_, v___x_1950_, v___x_1951_, v_numParams_1943_, v___x_1953_, v___x_1957_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_numNested_1945_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref_known(v___x_1958_, 1);
v___y_1900_ = v_a_1933_;
v___y_1901_ = v___x_1936_;
v_a_1902_ = v___x_1957_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___y_1905_ = v_a_1933_;
v___y_1906_ = v___x_1936_;
v_a_1907_ = v_a_1959_;
goto v___jp_1904_;
}
}
}
else
{
lean_dec(v___x_1951_);
lean_dec(v___x_1950_);
lean_dec(v_numNested_1945_);
lean_dec(v_all_1944_);
lean_dec(v_numParams_1943_);
lean_dec(v_indName_1795_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1960_; 
v_a_1960_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1952_, 1);
v___y_1900_ = v_a_1933_;
v___y_1901_ = v___x_1936_;
v_a_1902_ = v_a_1960_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1961_; 
v_a_1961_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1952_, 1);
v___y_1905_ = v_a_1933_;
v___y_1906_ = v___x_1936_;
v_a_1907_ = v_a_1961_;
goto v___jp_1904_;
}
}
}
else
{
lean_object* v___x_1962_; 
lean_dec(v_numNested_1945_);
lean_dec(v_all_1944_);
lean_dec(v_numParams_1943_);
lean_dec(v_indName_1795_);
v___x_1962_ = lean_box(0);
v___y_1900_ = v_a_1933_;
v___y_1901_ = v___x_1936_;
v_a_1902_ = v___x_1962_;
goto v___jp_1899_;
}
}
else
{
lean_object* v_a_1963_; 
lean_dec(v_numNested_1945_);
lean_dec(v_all_1944_);
lean_dec(v_numParams_1943_);
lean_dec(v_indName_1795_);
v_a_1963_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1947_, 1);
v___y_1905_ = v_a_1933_;
v___y_1906_ = v___x_1936_;
v_a_1907_ = v_a_1963_;
goto v___jp_1904_;
}
}
}
else
{
lean_object* v___x_1964_; 
lean_dec(v_a_1938_);
lean_dec(v_indName_1795_);
v___x_1964_ = lean_box(0);
v___y_1900_ = v_a_1933_;
v___y_1901_ = v___x_1936_;
v_a_1902_ = v___x_1964_;
goto v___jp_1899_;
}
}
else
{
lean_object* v_a_1965_; 
lean_dec(v_indName_1795_);
v_a_1965_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1965_);
lean_dec_ref_known(v___x_1937_, 1);
v___y_1905_ = v_a_1933_;
v___y_1906_ = v___x_1936_;
v_a_1907_ = v_a_1965_;
goto v___jp_1904_;
}
}
else
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1795_);
v___x_1967_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1968_);
lean_dec_ref_known(v___x_1967_, 1);
if (lean_obj_tag(v_a_1968_) == 5)
{
lean_object* v_val_1969_; uint8_t v_isRec_1970_; 
v_val_1969_ = lean_ctor_get(v_a_1968_, 0);
lean_inc_ref(v_val_1969_);
lean_dec_ref_known(v_a_1968_, 1);
v_isRec_1970_ = lean_ctor_get_uint8(v_val_1969_, sizeof(void*)*6);
if (v_isRec_1970_ == 0)
{
lean_object* v___x_1971_; 
lean_dec_ref(v_val_1969_);
lean_dec(v_indName_1795_);
v___x_1971_ = lean_box(0);
v___y_1922_ = v_a_1933_;
v___y_1923_ = v___x_1966_;
v_a_1924_ = v___x_1971_;
goto v___jp_1921_;
}
else
{
lean_object* v_toConstantVal_1972_; lean_object* v_numParams_1973_; lean_object* v_all_1974_; lean_object* v_numNested_1975_; lean_object* v_type_1976_; lean_object* v___x_1977_; 
v_toConstantVal_1972_ = lean_ctor_get(v_val_1969_, 0);
lean_inc_ref(v_toConstantVal_1972_);
v_numParams_1973_ = lean_ctor_get(v_val_1969_, 1);
lean_inc(v_numParams_1973_);
v_all_1974_ = lean_ctor_get(v_val_1969_, 3);
lean_inc(v_all_1974_);
v_numNested_1975_ = lean_ctor_get(v_val_1969_, 5);
lean_inc(v_numNested_1975_);
lean_dec_ref(v_val_1969_);
v_type_1976_ = lean_ctor_get(v_toConstantVal_1972_, 2);
lean_inc_ref(v_type_1976_);
lean_dec_ref(v_toConstantVal_1972_);
v___x_1977_ = l_Lean_Meta_isPropFormerType(v_type_1976_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; uint8_t v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref_known(v___x_1977_, 1);
v___x_1979_ = lean_unbox(v_a_1978_);
lean_dec(v_a_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
lean_inc_n(v_indName_1795_, 2);
v___x_1980_ = l_Lean_mkRecName(v_indName_1795_);
v___x_1981_ = l_Lean_mkBelowName(v_indName_1795_);
lean_inc(v___x_1981_);
lean_inc(v_numParams_1973_);
lean_inc(v___x_1980_);
v___x_1982_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1980_, v_numParams_1973_, v___x_1981_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
lean_dec_ref_known(v___x_1982_, 1);
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = l_List_get_x21Internal___redArg(v___x_1805_, v_all_1974_, v___x_1983_);
lean_dec(v_all_1974_);
v___x_1985_ = lean_name_eq(v___x_1984_, v_indName_1795_);
lean_dec(v_indName_1795_);
lean_dec(v___x_1984_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1986_; 
lean_dec(v___x_1981_);
lean_dec(v___x_1980_);
lean_dec(v_numNested_1975_);
lean_dec(v_numParams_1973_);
v___x_1986_ = lean_box(0);
v___y_1922_ = v_a_1933_;
v___y_1923_ = v___x_1966_;
v_a_1924_ = v___x_1986_;
goto v___jp_1921_;
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1987_ = lean_box(0);
v___x_1988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1975_, v___x_1980_, v___x_1981_, v_numParams_1973_, v___x_1983_, v___x_1987_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
lean_dec(v_numNested_1975_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_dec_ref_known(v___x_1988_, 1);
v___y_1922_ = v_a_1933_;
v___y_1923_ = v___x_1966_;
v_a_1924_ = v___x_1987_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1989_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
v___y_1927_ = v_a_1933_;
v___y_1928_ = v___x_1966_;
v_a_1929_ = v_a_1989_;
goto v___jp_1926_;
}
}
}
else
{
lean_dec(v___x_1981_);
lean_dec(v___x_1980_);
lean_dec(v_numNested_1975_);
lean_dec(v_all_1974_);
lean_dec(v_numParams_1973_);
lean_dec(v_indName_1795_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1982_, 1);
v___y_1922_ = v_a_1933_;
v___y_1923_ = v___x_1966_;
v_a_1924_ = v_a_1990_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1982_, 1);
v___y_1927_ = v_a_1933_;
v___y_1928_ = v___x_1966_;
v_a_1929_ = v_a_1991_;
goto v___jp_1926_;
}
}
}
else
{
lean_object* v___x_1992_; 
lean_dec(v_numNested_1975_);
lean_dec(v_all_1974_);
lean_dec(v_numParams_1973_);
lean_dec(v_indName_1795_);
v___x_1992_ = lean_box(0);
v___y_1922_ = v_a_1933_;
v___y_1923_ = v___x_1966_;
v_a_1924_ = v___x_1992_;
goto v___jp_1921_;
}
}
else
{
lean_object* v_a_1993_; 
lean_dec(v_numNested_1975_);
lean_dec(v_all_1974_);
lean_dec(v_numParams_1973_);
lean_dec(v_indName_1795_);
v_a_1993_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1977_, 1);
v___y_1927_ = v_a_1933_;
v___y_1928_ = v___x_1966_;
v_a_1929_ = v_a_1993_;
goto v___jp_1926_;
}
}
}
else
{
lean_object* v___x_1994_; 
lean_dec(v_a_1968_);
lean_dec(v_indName_1795_);
v___x_1994_ = lean_box(0);
v___y_1922_ = v_a_1933_;
v___y_1923_ = v___x_1966_;
v_a_1924_ = v___x_1994_;
goto v___jp_1921_;
}
}
else
{
lean_object* v_a_1995_; 
lean_dec(v_indName_1795_);
v_a_1995_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1967_, 1);
v___y_1927_ = v_a_1933_;
v___y_1928_ = v___x_1966_;
v_a_1929_ = v_a_1995_;
goto v___jp_1926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_mkBelow(v_indName_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v___x_2081_, lean_object* v_inst_2082_, lean_object* v_R_2083_, lean_object* v_a_2084_, lean_object* v_b_2085_, lean_object* v_c_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2078_, v___x_2079_, v___x_2080_, v___x_2081_, v_a_2084_, v_b_2085_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2093_, lean_object* v___x_2094_, lean_object* v___x_2095_, lean_object* v___x_2096_, lean_object* v_inst_2097_, lean_object* v_R_2098_, lean_object* v_a_2099_, lean_object* v_b_2100_, lean_object* v_c_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2093_, v___x_2094_, v___x_2095_, v___x_2096_, v_inst_2097_, v_R_2098_, v_a_2099_, v_b_2100_, v_c_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v_upperBound_2093_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_00_u03b1_2108_, lean_object* v_x_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___redArg(v_x_2109_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_x_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_00_u03b1_2116_, v_x_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
if (lean_obj_tag(v_a_2124_) == 0)
{
lean_object* v___x_2126_; 
v___x_2126_ = l_List_reverse___redArg(v_a_2125_);
return v___x_2126_;
}
else
{
lean_object* v_head_2127_; lean_object* v_tail_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2137_; 
v_head_2127_ = lean_ctor_get(v_a_2124_, 0);
v_tail_2128_ = lean_ctor_get(v_a_2124_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_a_2124_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2130_ = v_a_2124_;
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_tail_2128_);
lean_inc(v_head_2127_);
lean_dec(v_a_2124_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2137_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2132_ = l_Lean_MessageData_ofExpr(v_head_2127_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 1, v_a_2125_);
lean_ctor_set(v___x_2130_, 0, v___x_2132_);
v___x_2134_ = v___x_2130_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v_a_2125_);
v___x_2134_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
v_a_2124_ = v_tail_2128_;
v_a_2125_ = v___x_2134_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2138_, lean_object* v_v_2139_, lean_object* v_i_2140_){
_start:
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_array_get_size(v_xs_2138_);
v___x_2142_ = lean_nat_dec_lt(v_i_2140_, v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; 
lean_dec(v_i_2140_);
v___x_2143_ = lean_box(0);
return v___x_2143_;
}
else
{
lean_object* v___x_2144_; uint8_t v___x_2145_; 
v___x_2144_ = lean_array_fget_borrowed(v_xs_2138_, v_i_2140_);
v___x_2145_ = lean_expr_eqv(v___x_2144_, v_v_2139_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_add(v_i_2140_, v___x_2146_);
lean_dec(v_i_2140_);
v_i_2140_ = v___x_2147_;
goto _start;
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_i_2140_);
return v___x_2149_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2150_, lean_object* v_v_2151_, lean_object* v_i_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2150_, v_v_2151_, v_i_2152_);
lean_dec_ref(v_v_2151_);
lean_dec_ref(v_xs_2150_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2154_, lean_object* v_v_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___x_2157_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2154_, v_v_2155_, v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2158_, lean_object* v_v_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2158_, v_v_2159_);
lean_dec_ref(v_v_2159_);
lean_dec_ref(v_xs_2158_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2161_, lean_object* v_v_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2161_, v_v_2162_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_box(0);
return v___x_2164_;
}
else
{
lean_object* v_val_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
v_val_2165_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2163_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_val_2165_);
lean_dec(v___x_2163_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_val_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2173_, lean_object* v_v_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2173_, v_v_2174_);
lean_dec_ref(v_v_2174_);
lean_dec_ref(v_xs_2173_);
return v_res_2175_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2177_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2178_ = l_Lean_stringToMessageData(v___x_2177_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2181_ = l_Lean_stringToMessageData(v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2182_, lean_object* v_prods_2183_, lean_object* v_motives_2184_, lean_object* v_fs_2185_, lean_object* v_minor__type_2186_, lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 5)
{
lean_object* v_fn_2195_; lean_object* v_arg_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_fn_2195_ = lean_ctor_get(v_x_2187_, 0);
lean_inc_ref(v_fn_2195_);
v_arg_2196_ = lean_ctor_get(v_x_2187_, 1);
lean_inc_ref(v_arg_2196_);
lean_dec_ref_known(v_x_2187_, 2);
v___x_2197_ = lean_array_set(v_x_2188_, v_x_2189_, v_arg_2196_);
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_sub(v_x_2189_, v___x_2198_);
lean_dec(v_x_2189_);
v_x_2187_ = v_fn_2195_;
v_x_2188_ = v___x_2197_;
v_x_2189_ = v___x_2199_;
goto _start;
}
else
{
lean_object* v___x_2201_; 
lean_dec(v_x_2189_);
v___x_2201_ = l_Lean_Meta_PProdN_mk(v_rlvl_2182_, v_prods_2183_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v___x_2203_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2184_, v_x_2187_);
lean_dec_ref(v_x_2187_);
if (lean_obj_tag(v___x_2203_) == 1)
{
lean_object* v_val_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec_ref(v_minor__type_2186_);
lean_dec_ref(v_motives_2184_);
v_val_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_val_2204_);
lean_dec_ref_known(v___x_2203_, 1);
v___x_2205_ = l_Lean_instInhabitedExpr;
v___x_2206_ = lean_array_get_borrowed(v___x_2205_, v_fs_2185_, v_val_2204_);
lean_dec(v_val_2204_);
lean_inc(v_a_2202_);
v___x_2207_ = lean_array_push(v_x_2188_, v_a_2202_);
lean_inc(v___x_2206_);
v___x_2208_ = l_Lean_mkAppN(v___x_2206_, v___x_2207_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = l_Lean_Meta_mkPProdMk(v___x_2208_, v_a_2202_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2209_;
}
else
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec(v___x_2203_);
lean_dec(v_a_2202_);
lean_dec_ref(v_x_2188_);
v___x_2210_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2211_ = l_Lean_MessageData_ofExpr(v_minor__type_2186_);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = lean_array_to_list(v_motives_2184_);
v___x_2216_ = lean_box(0);
v___x_2217_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2215_, v___x_2216_);
v___x_2218_ = l_Lean_MessageData_ofList(v___x_2217_);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2214_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2219_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2220_;
}
}
else
{
lean_dec_ref(v_x_2188_);
lean_dec_ref(v_x_2187_);
lean_dec_ref(v_minor__type_2186_);
lean_dec_ref(v_motives_2184_);
return v___x_2201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2221_, lean_object* v_prods_2222_, lean_object* v_motives_2223_, lean_object* v_fs_2224_, lean_object* v_minor__type_2225_, lean_object* v_x_2226_, lean_object* v_x_2227_, lean_object* v_x_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2221_, v_prods_2222_, v_motives_2223_, v_fs_2224_, v_minor__type_2225_, v_x_2226_, v_x_2227_, v_x_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v_fs_2224_);
return v_res_2234_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2235_; lean_object* v_dummy_2236_; 
v___x_2235_ = lean_box(0);
v_dummy_2236_ = l_Lean_Expr_sort___override(v___x_2235_);
return v_dummy_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2237_, lean_object* v_head_2238_, lean_object* v_belows_2239_, lean_object* v_prods_2240_, lean_object* v_rlvl_2241_, lean_object* v_fs_2242_, lean_object* v_minor__type_2243_, lean_object* v_tail_2244_, lean_object* v_arg__args_2245_, lean_object* v_arg__type_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2237_, v_head_2238_, v_belows_2239_, v_prods_2240_, v_rlvl_2241_, v_fs_2242_, v_minor__type_2243_, v_tail_2244_, v_arg__args_2245_, v_arg__type_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec_ref(v_arg__args_2245_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2253_, lean_object* v_motives_2254_, lean_object* v_belows_2255_, lean_object* v_fs_2256_, lean_object* v_minor__type_2257_, lean_object* v_prods_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_){
_start:
{
if (lean_obj_tag(v_a_2259_) == 0)
{
lean_object* v_dummy_2265_; lean_object* v_nargs_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v_belows_2255_);
v_dummy_2265_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2266_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2257_);
lean_inc(v_nargs_2266_);
v___x_2267_ = lean_mk_array(v_nargs_2266_, v_dummy_2265_);
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = lean_nat_sub(v_nargs_2266_, v___x_2268_);
lean_dec(v_nargs_2266_);
lean_inc_ref(v_minor__type_2257_);
v___x_2270_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2253_, v_prods_2258_, v_motives_2254_, v_fs_2256_, v_minor__type_2257_, v_minor__type_2257_, v___x_2267_, v___x_2269_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
lean_dec_ref(v_fs_2256_);
return v___x_2270_;
}
else
{
lean_object* v_head_2271_; lean_object* v_tail_2272_; lean_object* v___x_2273_; 
v_head_2271_ = lean_ctor_get(v_a_2259_, 0);
lean_inc_n(v_head_2271_, 2);
v_tail_2272_ = lean_ctor_get(v_a_2259_, 1);
lean_inc(v_tail_2272_);
lean_dec_ref_known(v_a_2259_, 2);
lean_inc(v_a_2263_);
lean_inc_ref(v_a_2262_);
lean_inc(v_a_2261_);
lean_inc_ref(v_a_2260_);
v___x_2273_ = lean_infer_type(v_head_2271_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___f_2275_; uint8_t v___x_2276_; lean_object* v___x_2277_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref_known(v___x_2273_, 1);
v___f_2275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2275_, 0, v_motives_2254_);
lean_closure_set(v___f_2275_, 1, v_head_2271_);
lean_closure_set(v___f_2275_, 2, v_belows_2255_);
lean_closure_set(v___f_2275_, 3, v_prods_2258_);
lean_closure_set(v___f_2275_, 4, v_rlvl_2253_);
lean_closure_set(v___f_2275_, 5, v_fs_2256_);
lean_closure_set(v___f_2275_, 6, v_minor__type_2257_);
lean_closure_set(v___f_2275_, 7, v_tail_2272_);
v___x_2276_ = 0;
v___x_2277_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2274_, v___f_2275_, v___x_2276_, v_a_2260_, v_a_2261_, v_a_2262_, v_a_2263_);
return v___x_2277_;
}
else
{
lean_dec(v_tail_2272_);
lean_dec(v_head_2271_);
lean_dec_ref(v_prods_2258_);
lean_dec_ref(v_minor__type_2257_);
lean_dec_ref(v_fs_2256_);
lean_dec_ref(v_belows_2255_);
lean_dec_ref(v_motives_2254_);
lean_dec(v_rlvl_2253_);
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2278_, lean_object* v_rlvl_2279_, lean_object* v_motives_2280_, lean_object* v_belows_2281_, lean_object* v_fs_2282_, lean_object* v_minor__type_2283_, lean_object* v_tail_2284_, uint8_t v___x_2285_, uint8_t v___x_2286_, uint8_t v___x_2287_, lean_object* v_arg_x27_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_inc_ref(v_arg_x27_2288_);
v___x_2294_ = lean_array_push(v_prods_2278_, v_arg_x27_2288_);
v___x_2295_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2279_, v_motives_2280_, v_belows_2281_, v_fs_2282_, v_minor__type_2283_, v___x_2294_, v_tail_2284_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref_known(v___x_2295_, 1);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_mk_empty_array_with_capacity(v___x_2297_);
v___x_2299_ = lean_array_push(v___x_2298_, v_arg_x27_2288_);
v___x_2300_ = l_Lean_Meta_mkLambdaFVars(v___x_2299_, v_a_2296_, v___x_2285_, v___x_2286_, v___x_2285_, v___x_2286_, v___x_2287_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec_ref(v___x_2299_);
return v___x_2300_;
}
else
{
lean_dec_ref(v_arg_x27_2288_);
return v___x_2295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2301_, lean_object* v_rlvl_2302_, lean_object* v_motives_2303_, lean_object* v_belows_2304_, lean_object* v_fs_2305_, lean_object* v_minor__type_2306_, lean_object* v_tail_2307_, lean_object* v___x_2308_, lean_object* v___x_2309_, lean_object* v___x_2310_, lean_object* v_arg_x27_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v___x_1743__boxed_2317_; uint8_t v___x_1744__boxed_2318_; uint8_t v___x_1745__boxed_2319_; lean_object* v_res_2320_; 
v___x_1743__boxed_2317_ = lean_unbox(v___x_2308_);
v___x_1744__boxed_2318_ = lean_unbox(v___x_2309_);
v___x_1745__boxed_2319_ = lean_unbox(v___x_2310_);
v_res_2320_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2301_, v_rlvl_2302_, v_motives_2303_, v_belows_2304_, v_fs_2305_, v_minor__type_2306_, v_tail_2307_, v___x_1743__boxed_2317_, v___x_1744__boxed_2318_, v___x_1745__boxed_2319_, v_arg_x27_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2321_, lean_object* v_head_2322_, lean_object* v_belows_2323_, lean_object* v_arg__type_2324_, lean_object* v_prods_2325_, lean_object* v_rlvl_2326_, lean_object* v_fs_2327_, lean_object* v_minor__type_2328_, lean_object* v_tail_2329_, lean_object* v_arg__args_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
if (lean_obj_tag(v_x_2331_) == 5)
{
lean_object* v_fn_2339_; lean_object* v_arg_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_fn_2339_ = lean_ctor_get(v_x_2331_, 0);
lean_inc_ref(v_fn_2339_);
v_arg_2340_ = lean_ctor_get(v_x_2331_, 1);
lean_inc_ref(v_arg_2340_);
lean_dec_ref_known(v_x_2331_, 2);
v___x_2341_ = lean_array_set(v_x_2332_, v_x_2333_, v_arg_2340_);
v___x_2342_ = lean_unsigned_to_nat(1u);
v___x_2343_ = lean_nat_sub(v_x_2333_, v___x_2342_);
lean_dec(v_x_2333_);
v_x_2331_ = v_fn_2339_;
v_x_2332_ = v___x_2341_;
v_x_2333_ = v___x_2343_;
goto _start;
}
else
{
lean_object* v___x_2345_; 
lean_dec(v_x_2333_);
v___x_2345_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2321_, v_x_2331_);
lean_dec_ref(v_x_2331_);
if (lean_obj_tag(v___x_2345_) == 1)
{
lean_object* v_val_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_val_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_val_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v___x_2347_ = l_Lean_Expr_fvarId_x21(v_head_2322_);
lean_dec_ref(v_head_2322_);
v___x_2348_ = l_Lean_FVarId_getUserName___redArg(v___x_2347_, v___y_2334_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = l_Lean_instInhabitedExpr;
v___x_2351_ = lean_array_get_borrowed(v___x_2350_, v_belows_2323_, v_val_2346_);
lean_dec(v_val_2346_);
lean_inc(v___x_2351_);
v___x_2352_ = l_Lean_mkAppN(v___x_2351_, v_x_2332_);
lean_dec_ref(v_x_2332_);
v___x_2353_ = l_Lean_Meta_mkPProd(v_arg__type_2324_, v___x_2352_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; uint8_t v___x_2355_; uint8_t v___x_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = 0;
v___x_2356_ = 1;
v___x_2357_ = 1;
v___x_2358_ = l_Lean_Meta_mkForallFVars(v_arg__args_2330_, v_a_2354_, v___x_2355_, v___x_2356_, v___x_2356_, v___x_2357_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___f_2363_; lean_object* v___x_2364_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v___x_2358_, 1);
v___x_2360_ = lean_box(v___x_2355_);
v___x_2361_ = lean_box(v___x_2356_);
v___x_2362_ = lean_box(v___x_2357_);
v___f_2363_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2363_, 0, v_prods_2325_);
lean_closure_set(v___f_2363_, 1, v_rlvl_2326_);
lean_closure_set(v___f_2363_, 2, v_motives_2321_);
lean_closure_set(v___f_2363_, 3, v_belows_2323_);
lean_closure_set(v___f_2363_, 4, v_fs_2327_);
lean_closure_set(v___f_2363_, 5, v_minor__type_2328_);
lean_closure_set(v___f_2363_, 6, v_tail_2329_);
lean_closure_set(v___f_2363_, 7, v___x_2360_);
lean_closure_set(v___f_2363_, 8, v___x_2361_);
lean_closure_set(v___f_2363_, 9, v___x_2362_);
v___x_2364_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2349_, v_a_2359_, v___f_2363_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2364_;
}
else
{
lean_dec(v_a_2349_);
lean_dec(v_tail_2329_);
lean_dec_ref(v_minor__type_2328_);
lean_dec_ref(v_fs_2327_);
lean_dec(v_rlvl_2326_);
lean_dec_ref(v_prods_2325_);
lean_dec_ref(v_belows_2323_);
lean_dec_ref(v_motives_2321_);
return v___x_2358_;
}
}
else
{
lean_dec(v_a_2349_);
lean_dec(v_tail_2329_);
lean_dec_ref(v_minor__type_2328_);
lean_dec_ref(v_fs_2327_);
lean_dec(v_rlvl_2326_);
lean_dec_ref(v_prods_2325_);
lean_dec_ref(v_belows_2323_);
lean_dec_ref(v_motives_2321_);
return v___x_2353_;
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_val_2346_);
lean_dec_ref(v_x_2332_);
lean_dec(v_tail_2329_);
lean_dec_ref(v_minor__type_2328_);
lean_dec_ref(v_fs_2327_);
lean_dec(v_rlvl_2326_);
lean_dec_ref(v_prods_2325_);
lean_dec_ref(v_arg__type_2324_);
lean_dec_ref(v_belows_2323_);
lean_dec_ref(v_motives_2321_);
v_a_2365_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2348_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2348_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v___x_2373_; 
lean_dec(v___x_2345_);
lean_dec_ref(v_x_2332_);
lean_dec_ref(v_arg__type_2324_);
v___x_2373_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2326_, v_motives_2321_, v_belows_2323_, v_fs_2327_, v_minor__type_2328_, v_prods_2325_, v_tail_2329_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; uint8_t v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_mk_empty_array_with_capacity(v___x_2375_);
v___x_2377_ = lean_array_push(v___x_2376_, v_head_2322_);
v___x_2378_ = 0;
v___x_2379_ = 1;
v___x_2380_ = 1;
v___x_2381_ = l_Lean_Meta_mkLambdaFVars(v___x_2377_, v_a_2374_, v___x_2378_, v___x_2379_, v___x_2378_, v___x_2379_, v___x_2380_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
lean_dec_ref(v___x_2377_);
return v___x_2381_;
}
else
{
lean_dec_ref(v_head_2322_);
return v___x_2373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2382_, lean_object* v_head_2383_, lean_object* v_belows_2384_, lean_object* v_prods_2385_, lean_object* v_rlvl_2386_, lean_object* v_fs_2387_, lean_object* v_minor__type_2388_, lean_object* v_tail_2389_, lean_object* v_arg__args_2390_, lean_object* v_arg__type_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v_dummy_2397_; lean_object* v_nargs_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v_dummy_2397_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2398_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2391_);
lean_inc(v_nargs_2398_);
v___x_2399_ = lean_mk_array(v_nargs_2398_, v_dummy_2397_);
v___x_2400_ = lean_unsigned_to_nat(1u);
v___x_2401_ = lean_nat_sub(v_nargs_2398_, v___x_2400_);
lean_dec(v_nargs_2398_);
lean_inc_ref(v_arg__type_2391_);
v___x_2402_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2382_, v_head_2383_, v_belows_2384_, v_arg__type_2391_, v_prods_2385_, v_rlvl_2386_, v_fs_2387_, v_minor__type_2388_, v_tail_2389_, v_arg__args_2390_, v_arg__type_2391_, v___x_2399_, v___x_2401_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2403_, lean_object* v_motives_2404_, lean_object* v_belows_2405_, lean_object* v_fs_2406_, lean_object* v_minor__type_2407_, lean_object* v_prods_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_, lean_object* v_a_2413_, lean_object* v_a_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2403_, v_motives_2404_, v_belows_2405_, v_fs_2406_, v_minor__type_2407_, v_prods_2408_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_, v_a_2413_);
lean_dec(v_a_2413_);
lean_dec_ref(v_a_2412_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2416_ = _args[0];
lean_object* v_head_2417_ = _args[1];
lean_object* v_belows_2418_ = _args[2];
lean_object* v_arg__type_2419_ = _args[3];
lean_object* v_prods_2420_ = _args[4];
lean_object* v_rlvl_2421_ = _args[5];
lean_object* v_fs_2422_ = _args[6];
lean_object* v_minor__type_2423_ = _args[7];
lean_object* v_tail_2424_ = _args[8];
lean_object* v_arg__args_2425_ = _args[9];
lean_object* v_x_2426_ = _args[10];
lean_object* v_x_2427_ = _args[11];
lean_object* v_x_2428_ = _args[12];
lean_object* v___y_2429_ = _args[13];
lean_object* v___y_2430_ = _args[14];
lean_object* v___y_2431_ = _args[15];
lean_object* v___y_2432_ = _args[16];
lean_object* v___y_2433_ = _args[17];
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2416_, v_head_2417_, v_belows_2418_, v_arg__type_2419_, v_prods_2420_, v_rlvl_2421_, v_fs_2422_, v_minor__type_2423_, v_tail_2424_, v_arg__args_2425_, v_x_2426_, v_x_2427_, v_x_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
lean_dec(v___y_2432_);
lean_dec_ref(v___y_2431_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec_ref(v_arg__args_2425_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2435_, lean_object* v_motives_2436_, lean_object* v_belows_2437_, lean_object* v_fs_2438_, lean_object* v_minor__args_2439_, lean_object* v_minor__type_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2447_ = lean_array_to_list(v_minor__args_2439_);
v___x_2448_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2435_, v_motives_2436_, v_belows_2437_, v_fs_2438_, v_minor__type_2440_, v___x_2446_, v___x_2447_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2449_, lean_object* v_motives_2450_, lean_object* v_belows_2451_, lean_object* v_fs_2452_, lean_object* v_minor__args_2453_, lean_object* v_minor__type_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2449_, v_motives_2450_, v_belows_2451_, v_fs_2452_, v_minor__args_2453_, v_minor__type_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2461_, lean_object* v_motives_2462_, lean_object* v_belows_2463_, lean_object* v_fs_2464_, lean_object* v_minorType_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___f_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; 
v___f_2471_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2471_, 0, v_rlvl_2461_);
lean_closure_set(v___f_2471_, 1, v_motives_2462_);
lean_closure_set(v___f_2471_, 2, v_belows_2463_);
lean_closure_set(v___f_2471_, 3, v_fs_2464_);
v___x_2472_ = 0;
v___x_2473_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2465_, v___f_2471_, v___x_2472_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2474_, lean_object* v_motives_2475_, lean_object* v_belows_2476_, lean_object* v_fs_2477_, lean_object* v_minorType_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2474_, v_motives_2475_, v_belows_2476_, v_fs_2477_, v_minorType_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___f_2491_; lean_object* v___x_27155__overap_2492_; lean_object* v___x_2493_; 
v___f_2491_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27155__overap_2492_ = lean_panic_fn_borrowed(v___f_2491_, v_msg_2485_);
lean_inc(v___y_2489_);
lean_inc_ref(v___y_2488_);
lean_inc(v___y_2487_);
lean_inc_ref(v___y_2486_);
v___x_2493_ = lean_apply_5(v___x_27155__overap_2492_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, lean_box(0));
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2501_, lean_object* v___y_2502_){
_start:
{
uint8_t v___x_2504_; 
v___x_2504_ = l_Lean_Expr_hasMVar(v_e_2501_);
if (v___x_2504_ == 0)
{
lean_object* v___x_2505_; 
v___x_2505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2505_, 0, v_e_2501_);
return v___x_2505_;
}
else
{
lean_object* v___x_2506_; lean_object* v_mctx_2507_; lean_object* v___x_2508_; lean_object* v_fst_2509_; lean_object* v_snd_2510_; lean_object* v___x_2511_; lean_object* v_cache_2512_; lean_object* v_zetaDeltaFVarIds_2513_; lean_object* v_postponed_2514_; lean_object* v_diag_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2524_; 
v___x_2506_ = lean_st_ref_get(v___y_2502_);
v_mctx_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc_ref(v_mctx_2507_);
lean_dec(v___x_2506_);
v___x_2508_ = l_Lean_instantiateMVarsCore(v_mctx_2507_, v_e_2501_);
v_fst_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_fst_2509_);
v_snd_2510_ = lean_ctor_get(v___x_2508_, 1);
lean_inc(v_snd_2510_);
lean_dec_ref(v___x_2508_);
v___x_2511_ = lean_st_ref_take(v___y_2502_);
v_cache_2512_ = lean_ctor_get(v___x_2511_, 1);
v_zetaDeltaFVarIds_2513_ = lean_ctor_get(v___x_2511_, 2);
v_postponed_2514_ = lean_ctor_get(v___x_2511_, 3);
v_diag_2515_ = lean_ctor_get(v___x_2511_, 4);
v_isSharedCheck_2524_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2524_ == 0)
{
lean_object* v_unused_2525_; 
v_unused_2525_ = lean_ctor_get(v___x_2511_, 0);
lean_dec(v_unused_2525_);
v___x_2517_ = v___x_2511_;
v_isShared_2518_ = v_isSharedCheck_2524_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_diag_2515_);
lean_inc(v_postponed_2514_);
lean_inc(v_zetaDeltaFVarIds_2513_);
lean_inc(v_cache_2512_);
lean_dec(v___x_2511_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2524_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v_snd_2510_);
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_snd_2510_);
lean_ctor_set(v_reuseFailAlloc_2523_, 1, v_cache_2512_);
lean_ctor_set(v_reuseFailAlloc_2523_, 2, v_zetaDeltaFVarIds_2513_);
lean_ctor_set(v_reuseFailAlloc_2523_, 3, v_postponed_2514_);
lean_ctor_set(v_reuseFailAlloc_2523_, 4, v_diag_2515_);
v___x_2520_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_st_ref_put(v___y_2502_, v___x_2520_);
v___x_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2522_, 0, v_fst_2509_);
return v___x_2522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2526_, v___y_2527_);
lean_dec(v___y_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2530_, v___y_2532_);
return v___x_2536_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___x_2547_; lean_object* v_env_2548_; lean_object* v_toConstantVal_2549_; lean_object* v_value_2550_; lean_object* v_all_2551_; uint8_t v___y_2553_; lean_object* v_type_2561_; uint8_t v___x_2562_; 
v___x_2547_ = lean_st_ref_get(v___y_2545_);
v_env_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc_ref_n(v_env_2548_, 2);
lean_dec(v___x_2547_);
v_toConstantVal_2549_ = lean_ctor_get(v_thm_2544_, 0);
v_value_2550_ = lean_ctor_get(v_thm_2544_, 1);
v_all_2551_ = lean_ctor_get(v_thm_2544_, 2);
v_type_2561_ = lean_ctor_get(v_toConstantVal_2549_, 2);
v___x_2562_ = l_Lean_Environment_hasUnsafe(v_env_2548_, v_type_2561_);
if (v___x_2562_ == 0)
{
uint8_t v___x_2563_; 
v___x_2563_ = l_Lean_Environment_hasUnsafe(v_env_2548_, v_value_2550_);
v___y_2553_ = v___x_2563_;
goto v___jp_2552_;
}
else
{
lean_dec_ref(v_env_2548_);
v___y_2553_ = v___x_2562_;
goto v___jp_2552_;
}
v___jp_2552_:
{
if (v___y_2553_ == 0)
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2554_, 0, v_thm_2544_);
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; uint8_t v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_inc(v_all_2551_);
lean_inc_ref(v_value_2550_);
lean_inc_ref(v_toConstantVal_2549_);
lean_dec_ref(v_thm_2544_);
v___x_2556_ = lean_box(0);
v___x_2557_ = 0;
v___x_2558_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2558_, 0, v_toConstantVal_2549_);
lean_ctor_set(v___x_2558_, 1, v_value_2550_);
lean_ctor_set(v___x_2558_, 2, v___x_2556_);
lean_ctor_set(v___x_2558_, 3, v_all_2551_);
lean_ctor_set_uint8(v___x_2558_, sizeof(void*)*4, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
return v___x_2560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2564_, v___y_2565_);
lean_dec(v___y_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v___x_2574_; 
v___x_2574_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2568_, v___y_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2583_, lean_object* v___x_2584_, lean_object* v___x_2585_, lean_object* v_all_2586_, lean_object* v___x_2587_, lean_object* v___x_2588_, lean_object* v___x_2589_, lean_object* v_x_2590_){
_start:
{
lean_object* v___y_2592_; lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = lean_array_get_size(v_all_2586_);
v___x_2597_ = lean_nat_dec_lt(v_x_2590_, v___x_2596_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2598_ = lean_array_get_borrowed(v___x_2587_, v_all_2586_, v___x_2588_);
v___x_2599_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2600_ = lean_nat_sub(v_x_2590_, v___x_2596_);
v___x_2601_ = lean_nat_add(v___x_2600_, v___x_2589_);
lean_dec(v___x_2600_);
v___x_2602_ = l_Nat_reprFast(v___x_2601_);
v___x_2603_ = lean_string_append(v___x_2599_, v___x_2602_);
lean_dec_ref(v___x_2602_);
lean_inc(v___x_2598_);
v___x_2604_ = l_Lean_Name_str___override(v___x_2598_, v___x_2603_);
v___y_2592_ = v___x_2604_;
goto v___jp_2591_;
}
else
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_array_fget_borrowed(v_all_2586_, v_x_2590_);
lean_inc(v___x_2605_);
v___x_2606_ = l_Lean_mkBelowName(v___x_2605_);
v___y_2592_ = v___x_2606_;
goto v___jp_2591_;
}
v___jp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = l_Lean_Expr_const___override(v___y_2592_, v___x_2583_);
v___x_2594_ = l_Array_append___redArg(v___x_2584_, v___x_2585_);
v___x_2595_ = l_Lean_mkAppN(v___x_2593_, v___x_2594_);
lean_dec_ref(v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2607_, lean_object* v___x_2608_, lean_object* v___x_2609_, lean_object* v_all_2610_, lean_object* v___x_2611_, lean_object* v___x_2612_, lean_object* v___x_2613_, lean_object* v_x_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2607_, v___x_2608_, v___x_2609_, v_all_2610_, v___x_2611_, v___x_2612_, v___x_2613_, v_x_2614_);
lean_dec(v_x_2614_);
lean_dec(v___x_2613_);
lean_dec(v___x_2612_);
lean_dec(v___x_2611_);
lean_dec_ref(v_all_2610_);
lean_dec_ref(v___x_2609_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2616_, lean_object* v___x_2617_, uint8_t v___x_2618_, lean_object* v_targs_2619_, lean_object* v_x_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = l_Lean_mkAppN(v_a_2616_, v_targs_2619_);
v___x_2627_ = l_Lean_mkAppN(v___x_2617_, v_targs_2619_);
v___x_2628_ = l_Lean_Meta_mkPProd(v___x_2626_, v___x_2627_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; uint8_t v___x_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___x_2628_, 1);
v___x_2630_ = 0;
v___x_2631_ = 1;
v___x_2632_ = l_Lean_Meta_mkLambdaFVars(v_targs_2619_, v_a_2629_, v___x_2630_, v___x_2618_, v___x_2630_, v___x_2618_, v___x_2631_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2632_;
}
else
{
return v___x_2628_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2633_, lean_object* v___x_2634_, lean_object* v___x_2635_, lean_object* v_targs_2636_, lean_object* v_x_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_){
_start:
{
uint8_t v___x_30350__boxed_2643_; lean_object* v_res_2644_; 
v___x_30350__boxed_2643_ = lean_unbox(v___x_2635_);
v_res_2644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2633_, v___x_2634_, v___x_30350__boxed_2643_, v_targs_2636_, v_x_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec_ref(v_x_2637_);
lean_dec_ref(v_targs_2636_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v___x_2645_, lean_object* v___x_2646_, lean_object* v_as_2647_, size_t v_sz_2648_, size_t v_i_2649_, lean_object* v_b_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_usize_dec_lt(v_i_2649_, v_sz_2648_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2657_, 0, v_b_2650_);
return v___x_2657_;
}
else
{
lean_object* v_snd_2658_; lean_object* v_fst_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2716_; 
v_snd_2658_ = lean_ctor_get(v_b_2650_, 1);
v_fst_2659_ = lean_ctor_get(v_b_2650_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v_b_2650_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2661_ = v_b_2650_;
v_isShared_2662_ = v_isSharedCheck_2716_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2659_);
lean_dec(v_b_2650_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2716_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v_array_2663_; lean_object* v_start_2664_; lean_object* v_stop_2665_; uint8_t v___x_2666_; 
v_array_2663_ = lean_ctor_get(v_snd_2658_, 0);
v_start_2664_ = lean_ctor_get(v_snd_2658_, 1);
v_stop_2665_ = lean_ctor_get(v_snd_2658_, 2);
v___x_2666_ = lean_nat_dec_lt(v_start_2664_, v_stop_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2668_; 
if (v_isShared_2662_ == 0)
{
v___x_2668_ = v___x_2661_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v_fst_2659_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_snd_2658_);
v___x_2668_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
return v___x_2669_;
}
}
else
{
lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2712_; 
lean_inc(v_stop_2665_);
lean_inc(v_start_2664_);
lean_inc_ref(v_array_2663_);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_snd_2658_);
if (v_isSharedCheck_2712_ == 0)
{
lean_object* v_unused_2713_; lean_object* v_unused_2714_; lean_object* v_unused_2715_; 
v_unused_2713_ = lean_ctor_get(v_snd_2658_, 2);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_snd_2658_, 1);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v_snd_2658_, 0);
lean_dec(v_unused_2715_);
v___x_2672_ = v_snd_2658_;
v_isShared_2673_ = v_isSharedCheck_2712_;
goto v_resetjp_2671_;
}
else
{
lean_dec(v_snd_2658_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2712_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
v_a_2674_ = lean_array_uget_borrowed(v_as_2647_, v_i_2649_);
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
lean_inc(v_a_2674_);
v___x_2675_ = lean_infer_type(v_a_2674_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; uint8_t v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___f_2680_; uint8_t v___x_2681_; lean_object* v___x_2682_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = lean_nat_dec_lt(v___x_2645_, v___x_2646_);
v___x_2678_ = lean_array_fget_borrowed(v_array_2663_, v_start_2664_);
v___x_2679_ = lean_box(v___x_2677_);
lean_inc(v___x_2678_);
lean_inc(v_a_2674_);
v___f_2680_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2680_, 0, v_a_2674_);
lean_closure_set(v___f_2680_, 1, v___x_2678_);
lean_closure_set(v___f_2680_, 2, v___x_2679_);
v___x_2681_ = 0;
v___x_2682_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2676_, v___f_2680_, v___x_2681_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_nat_add(v_start_2664_, v___x_2684_);
lean_dec(v_start_2664_);
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2685_);
v___x_2687_ = v___x_2672_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_array_2663_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2695_, 2, v_stop_2665_);
v___x_2687_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2688_ = l_Lean_Expr_app___override(v_fst_2659_, v_a_2683_);
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 1, v___x_2687_);
lean_ctor_set(v___x_2661_, 0, v___x_2688_);
v___x_2690_ = v___x_2661_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2694_; 
v_reuseFailAlloc_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2694_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2694_, 1, v___x_2687_);
v___x_2690_ = v_reuseFailAlloc_2694_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
size_t v___x_2691_; size_t v___x_2692_; 
v___x_2691_ = ((size_t)1ULL);
v___x_2692_ = lean_usize_add(v_i_2649_, v___x_2691_);
v_i_2649_ = v___x_2692_;
v_b_2650_ = v___x_2690_;
goto _start;
}
}
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
lean_del_object(v___x_2672_);
lean_dec(v_stop_2665_);
lean_dec(v_start_2664_);
lean_dec_ref(v_array_2663_);
lean_del_object(v___x_2661_);
lean_dec(v_fst_2659_);
v_a_2696_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2682_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2682_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_del_object(v___x_2672_);
lean_dec(v_stop_2665_);
lean_dec(v_start_2664_);
lean_dec_ref(v_array_2663_);
lean_del_object(v___x_2661_);
lean_dec(v_fst_2659_);
v_a_2704_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2675_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2675_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v___x_2717_, lean_object* v___x_2718_, lean_object* v_as_2719_, lean_object* v_sz_2720_, lean_object* v_i_2721_, lean_object* v_b_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
size_t v_sz_boxed_2728_; size_t v_i_boxed_2729_; lean_object* v_res_2730_; 
v_sz_boxed_2728_ = lean_unbox_usize(v_sz_2720_);
lean_dec(v_sz_2720_);
v_i_boxed_2729_ = lean_unbox_usize(v_i_2721_);
lean_dec(v_i_2721_);
v_res_2730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2717_, v___x_2718_, v_as_2719_, v_sz_boxed_2728_, v_i_boxed_2729_, v_b_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v_as_2719_);
lean_dec(v___x_2718_);
lean_dec(v___x_2717_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2731_, size_t v_sz_2732_, size_t v_i_2733_, lean_object* v_b_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v___x_2740_; 
v___x_2740_ = lean_usize_dec_lt(v_i_2733_, v_sz_2732_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v_b_2734_);
return v___x_2741_;
}
else
{
lean_object* v_a_2742_; lean_object* v_toInductionSubgoal_2743_; lean_object* v_mvarId_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; 
v_a_2742_ = lean_array_uget_borrowed(v_as_2731_, v_i_2733_);
v_toInductionSubgoal_2743_ = lean_ctor_get(v_a_2742_, 0);
v_mvarId_2744_ = lean_ctor_get(v_toInductionSubgoal_2743_, 0);
v___x_2745_ = 0;
lean_inc(v_mvarId_2744_);
v___x_2746_ = l_Lean_MVarId_refl(v_mvarId_2744_, v___x_2745_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v___x_2747_; size_t v___x_2748_; size_t v___x_2749_; 
lean_dec_ref_known(v___x_2746_, 1);
v___x_2747_ = lean_box(0);
v___x_2748_ = ((size_t)1ULL);
v___x_2749_ = lean_usize_add(v_i_2733_, v___x_2748_);
v_i_2733_ = v___x_2749_;
v_b_2734_ = v___x_2747_;
goto _start;
}
else
{
return v___x_2746_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2751_, lean_object* v_sz_2752_, lean_object* v_i_2753_, lean_object* v_b_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
size_t v_sz_boxed_2760_; size_t v_i_boxed_2761_; lean_object* v_res_2762_; 
v_sz_boxed_2760_ = lean_unbox_usize(v_sz_2752_);
lean_dec(v_sz_2752_);
v_i_boxed_2761_ = lean_unbox_usize(v_i_2753_);
lean_dec(v_i_2753_);
v_res_2762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2751_, v_sz_boxed_2760_, v_i_boxed_2761_, v_b_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec_ref(v_as_2751_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2763_, lean_object* v___x_2764_, lean_object* v___x_2765_, lean_object* v_fs_2766_, lean_object* v_as_2767_, size_t v_sz_2768_, size_t v_i_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_lt(v_i_2769_, v_sz_2768_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; 
lean_dec_ref(v_fs_2766_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2764_);
lean_dec(v___x_2763_);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_b_2770_);
return v___x_2777_;
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_a_2778_ = lean_array_uget_borrowed(v_as_2767_, v_i_2769_);
lean_inc(v___y_2774_);
lean_inc_ref(v___y_2773_);
lean_inc(v___y_2772_);
lean_inc_ref(v___y_2771_);
lean_inc(v_a_2778_);
v___x_2779_ = lean_infer_type(v_a_2778_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
lean_inc_ref(v_fs_2766_);
lean_inc_ref(v___x_2765_);
lean_inc_ref(v___x_2764_);
lean_inc(v___x_2763_);
v___x_2781_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2763_, v___x_2764_, v___x_2765_, v_fs_2766_, v_a_2780_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = l_Lean_Expr_app___override(v_b_2770_, v_a_2782_);
v___x_2784_ = ((size_t)1ULL);
v___x_2785_ = lean_usize_add(v_i_2769_, v___x_2784_);
v_i_2769_ = v___x_2785_;
v_b_2770_ = v___x_2783_;
goto _start;
}
else
{
lean_dec_ref(v_b_2770_);
lean_dec_ref(v_fs_2766_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2764_);
lean_dec(v___x_2763_);
return v___x_2781_;
}
}
else
{
lean_dec_ref(v_b_2770_);
lean_dec_ref(v_fs_2766_);
lean_dec_ref(v___x_2765_);
lean_dec_ref(v___x_2764_);
lean_dec(v___x_2763_);
return v___x_2779_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2787_, lean_object* v___x_2788_, lean_object* v___x_2789_, lean_object* v_fs_2790_, lean_object* v_as_2791_, lean_object* v_sz_2792_, lean_object* v_i_2793_, lean_object* v_b_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
size_t v_sz_boxed_2800_; size_t v_i_boxed_2801_; lean_object* v_res_2802_; 
v_sz_boxed_2800_ = lean_unbox_usize(v_sz_2792_);
lean_dec(v_sz_2792_);
v_i_boxed_2801_ = lean_unbox_usize(v_i_2793_);
lean_dec(v_i_2793_);
v_res_2802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2787_, v___x_2788_, v___x_2789_, v_fs_2790_, v_as_2791_, v_sz_boxed_2800_, v_i_boxed_2801_, v_b_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec_ref(v_as_2791_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2803_, lean_object* v_tail_2804_, lean_object* v_recName_2805_, lean_object* v___x_2806_, lean_object* v___x_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v___x_2810_, size_t v_sz_2811_, size_t v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v___x_2817_, lean_object* v___x_2818_, lean_object* v_val_2819_, uint8_t v___x_2820_, lean_object* v_brecOnGoName_2821_, lean_object* v_levelParams_2822_, lean_object* v___x_2823_, lean_object* v_brecOnName_2824_, lean_object* v___x_2825_, lean_object* v_brecOnEqName_2826_, lean_object* v_fs_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
lean_inc(v___x_2803_);
v___x_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2803_);
lean_ctor_set(v___x_2833_, 1, v_tail_2804_);
v___x_2834_ = l_Lean_Expr_const___override(v_recName_2805_, v___x_2833_);
v___x_2835_ = l_Lean_mkAppN(v___x_2834_, v___x_2806_);
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
lean_ctor_set(v___x_2836_, 1, v___x_2807_);
v___x_2837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2808_, v___x_2809_, v___x_2810_, v_sz_2811_, v___x_2812_, v___x_2836_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v_fst_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_3200_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
lean_inc(v_a_2838_);
lean_dec_ref_known(v___x_2837_, 1);
v_fst_2839_ = lean_ctor_get(v_a_2838_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v_a_2838_);
if (v_isSharedCheck_3200_ == 0)
{
lean_object* v_unused_3201_; 
v_unused_3201_ = lean_ctor_get(v_a_2838_, 1);
lean_dec(v_unused_3201_);
v___x_2841_ = v_a_2838_;
v_isShared_2842_ = v_isSharedCheck_3200_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_fst_2839_);
lean_dec(v_a_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_3200_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
size_t v_sz_2843_; lean_object* v___x_2844_; 
v_sz_2843_ = lean_array_size(v___x_2813_);
lean_inc_ref(v_fs_2827_);
lean_inc_ref(v___x_2814_);
lean_inc_ref(v___x_2810_);
v___x_2844_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2803_, v___x_2810_, v___x_2814_, v_fs_2827_, v___x_2813_, v_sz_2843_, v___x_2812_, v_fst_2839_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___x_2846_ = l_Lean_mkAppN(v_a_2845_, v___x_2815_);
lean_inc_ref_n(v___x_2816_, 3);
v___x_2847_ = l_Lean_Expr_app___override(v___x_2846_, v___x_2816_);
v___x_2848_ = l_Array_append___redArg(v___x_2806_, v___x_2810_);
v___x_2849_ = l_Array_append___redArg(v___x_2848_, v___x_2815_);
v___x_2850_ = lean_mk_empty_array_with_capacity(v___x_2817_);
v___x_2851_ = lean_array_push(v___x_2850_, v___x_2816_);
v___x_2852_ = lean_array_get(v___x_2818_, v___x_2810_, v_val_2819_);
lean_dec_ref(v___x_2810_);
v___x_2853_ = lean_array_push(v___x_2815_, v___x_2816_);
v___x_2854_ = l_Lean_mkAppN(v___x_2852_, v___x_2853_);
v___x_2855_ = lean_array_get(v___x_2818_, v___x_2814_, v_val_2819_);
lean_dec_ref(v___x_2814_);
v___x_2856_ = l_Lean_mkAppN(v___x_2855_, v___x_2853_);
lean_inc_ref(v___x_2854_);
v___x_2857_ = l_Lean_Meta_mkPProd(v___x_2854_, v___x_2856_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
v___x_2859_ = l_Array_append___redArg(v___x_2849_, v___x_2851_);
lean_dec_ref(v___x_2851_);
v___x_2860_ = l_Array_append___redArg(v___x_2859_, v_fs_2827_);
v___x_2861_ = 0;
v___x_2862_ = 1;
v___x_2863_ = l_Lean_Meta_mkForallFVars(v___x_2860_, v_a_2858_, v___x_2861_, v___x_2820_, v___x_2820_, v___x_2862_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
v___x_2865_ = l_Lean_Meta_mkLambdaFVars(v___x_2860_, v___x_2847_, v___x_2861_, v___x_2820_, v___x_2861_, v___x_2820_, v___x_2862_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_3167_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = lean_box(1);
lean_inc(v_levelParams_2822_);
lean_inc(v_brecOnGoName_2821_);
v___x_2868_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2821_, v_levelParams_2822_, v_a_2864_, v_a_2866_, v___x_2867_, v___y_2831_);
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_3167_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_3167_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
lean_inc(v_a_2869_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set_tag(v___x_2871_, 1);
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_3166_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_addDecl(v___x_2874_, v___x_2861_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_toConstantVal_2876_; lean_object* v_name_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_3163_; 
lean_dec_ref_known(v___x_2875_, 1);
v_toConstantVal_2876_ = lean_ctor_get(v_a_2869_, 0);
lean_inc_ref(v_toConstantVal_2876_);
lean_dec(v_a_2869_);
v_name_2877_ = lean_ctor_get(v_toConstantVal_2876_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_toConstantVal_2876_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; lean_object* v_unused_3165_; 
v_unused_3164_ = lean_ctor_get(v_toConstantVal_2876_, 2);
lean_dec(v_unused_3164_);
v_unused_3165_ = lean_ctor_get(v_toConstantVal_2876_, 1);
lean_dec(v_unused_3165_);
v___x_2879_ = v_toConstantVal_2876_;
v_isShared_2880_ = v_isSharedCheck_3163_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_name_2877_);
lean_dec(v_toConstantVal_2876_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_3163_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v_env_2883_; lean_object* v_nextMacroScope_2884_; lean_object* v_ngen_2885_; lean_object* v_auxDeclNGen_2886_; lean_object* v_traceState_2887_; lean_object* v_messages_2888_; lean_object* v_infoState_2889_; lean_object* v_snapshotTasks_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_3161_; 
lean_inc(v_name_2877_);
v___x_2881_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2877_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec_ref(v___x_2881_);
v___x_2882_ = lean_st_ref_take(v___y_2831_);
v_env_2883_ = lean_ctor_get(v___x_2882_, 0);
v_nextMacroScope_2884_ = lean_ctor_get(v___x_2882_, 1);
v_ngen_2885_ = lean_ctor_get(v___x_2882_, 2);
v_auxDeclNGen_2886_ = lean_ctor_get(v___x_2882_, 3);
v_traceState_2887_ = lean_ctor_get(v___x_2882_, 4);
v_messages_2888_ = lean_ctor_get(v___x_2882_, 6);
v_infoState_2889_ = lean_ctor_get(v___x_2882_, 7);
v_snapshotTasks_2890_ = lean_ctor_get(v___x_2882_, 8);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v___x_2882_, 5);
lean_dec(v_unused_3162_);
v___x_2892_ = v___x_2882_;
v_isShared_2893_ = v_isSharedCheck_3161_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_snapshotTasks_2890_);
lean_inc(v_infoState_2889_);
lean_inc(v_messages_2888_);
lean_inc(v_traceState_2887_);
lean_inc(v_auxDeclNGen_2886_);
lean_inc(v_ngen_2885_);
lean_inc(v_nextMacroScope_2884_);
lean_inc(v_env_2883_);
lean_dec(v___x_2882_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_3161_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2894_ = l_Lean_addProtected(v_env_2883_, v_name_2877_);
v___x_2895_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 5, v___x_2895_);
lean_ctor_set(v___x_2892_, 0, v___x_2894_);
v___x_2897_ = v___x_2892_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_2894_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v_nextMacroScope_2884_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_ngen_2885_);
lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_auxDeclNGen_2886_);
lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_traceState_2887_);
lean_ctor_set(v_reuseFailAlloc_3160_, 5, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_3160_, 6, v_messages_2888_);
lean_ctor_set(v_reuseFailAlloc_3160_, 7, v_infoState_2889_);
lean_ctor_set(v_reuseFailAlloc_3160_, 8, v_snapshotTasks_2890_);
v___x_2897_ = v_reuseFailAlloc_3160_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v_mctx_2900_; lean_object* v_zetaDeltaFVarIds_2901_; lean_object* v_postponed_2902_; lean_object* v_diag_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_3158_; 
v___x_2898_ = lean_st_ref_put(v___y_2831_, v___x_2897_);
v___x_2899_ = lean_st_ref_take(v___y_2829_);
v_mctx_2900_ = lean_ctor_get(v___x_2899_, 0);
v_zetaDeltaFVarIds_2901_ = lean_ctor_get(v___x_2899_, 2);
v_postponed_2902_ = lean_ctor_get(v___x_2899_, 3);
v_diag_2903_ = lean_ctor_get(v___x_2899_, 4);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v___x_2899_, 1);
lean_dec(v_unused_3159_);
v___x_2905_ = v___x_2899_;
v_isShared_2906_ = v_isSharedCheck_3158_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_diag_2903_);
lean_inc(v_postponed_2902_);
lean_inc(v_zetaDeltaFVarIds_2901_);
lean_inc(v_mctx_2900_);
lean_dec(v___x_2899_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_3158_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2909_; 
v___x_2907_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 1, v___x_2907_);
v___x_2909_ = v___x_2905_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_mctx_2900_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_zetaDeltaFVarIds_2901_);
lean_ctor_set(v_reuseFailAlloc_3157_, 3, v_postponed_2902_);
lean_ctor_set(v_reuseFailAlloc_3157_, 4, v_diag_2903_);
v___x_2909_ = v_reuseFailAlloc_3157_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2910_ = lean_st_ref_put(v___y_2829_, v___x_2909_);
lean_inc(v___x_2823_);
v___x_2911_ = l_Lean_Expr_const___override(v_brecOnGoName_2821_, v___x_2823_);
v___x_2912_ = l_Lean_mkAppN(v___x_2911_, v___x_2860_);
lean_inc_ref(v___x_2912_);
v___x_2913_ = l_Lean_Meta_mkPProdFstM(v___x_2912_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2915_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
v___x_2915_ = l_Lean_Meta_mkLambdaFVars(v___x_2860_, v_a_2914_, v___x_2861_, v___x_2820_, v___x_2861_, v___x_2820_, v___x_2862_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2915_) == 0)
{
lean_object* v_a_2916_; lean_object* v___x_2917_; 
v_a_2916_ = lean_ctor_get(v___x_2915_, 0);
lean_inc(v_a_2916_);
lean_dec_ref_known(v___x_2915_, 1);
v___x_2917_ = l_Lean_Meta_mkForallFVars(v___x_2860_, v___x_2854_, v___x_2861_, v___x_2820_, v___x_2820_, v___x_2862_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2917_) == 0)
{
lean_object* v_a_2918_; lean_object* v___x_2919_; lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_3132_; 
v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v___x_2917_, 1);
lean_inc(v_levelParams_2822_);
v___x_2919_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2824_, v_levelParams_2822_, v_a_2918_, v_a_2916_, v___x_2867_, v___y_2831_);
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_2922_ = v___x_2919_;
v_isShared_2923_ = v_isSharedCheck_3132_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2919_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_3132_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
lean_inc(v_a_2920_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set_tag(v___x_2922_, 1);
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_3131_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_addDecl(v___x_2925_, v___x_2861_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_toConstantVal_2927_; lean_object* v_name_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_3128_; 
lean_dec_ref_known(v___x_2926_, 1);
v_toConstantVal_2927_ = lean_ctor_get(v_a_2920_, 0);
lean_inc_ref(v_toConstantVal_2927_);
lean_dec(v_a_2920_);
v_name_2928_ = lean_ctor_get(v_toConstantVal_2927_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_toConstantVal_2927_);
if (v_isSharedCheck_3128_ == 0)
{
lean_object* v_unused_3129_; lean_object* v_unused_3130_; 
v_unused_3129_ = lean_ctor_get(v_toConstantVal_2927_, 2);
lean_dec(v_unused_3129_);
v_unused_3130_ = lean_ctor_get(v_toConstantVal_2927_, 1);
lean_dec(v_unused_3130_);
v___x_2930_ = v_toConstantVal_2927_;
v_isShared_2931_ = v_isSharedCheck_3128_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_name_2928_);
lean_dec(v_toConstantVal_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_3128_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v_env_2934_; lean_object* v_nextMacroScope_2935_; lean_object* v_ngen_2936_; lean_object* v_auxDeclNGen_2937_; lean_object* v_traceState_2938_; lean_object* v_messages_2939_; lean_object* v_infoState_2940_; lean_object* v_snapshotTasks_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_3126_; 
lean_inc(v_name_2928_);
v___x_2932_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2928_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec_ref(v___x_2932_);
v___x_2933_ = lean_st_ref_take(v___y_2831_);
v_env_2934_ = lean_ctor_get(v___x_2933_, 0);
v_nextMacroScope_2935_ = lean_ctor_get(v___x_2933_, 1);
v_ngen_2936_ = lean_ctor_get(v___x_2933_, 2);
v_auxDeclNGen_2937_ = lean_ctor_get(v___x_2933_, 3);
v_traceState_2938_ = lean_ctor_get(v___x_2933_, 4);
v_messages_2939_ = lean_ctor_get(v___x_2933_, 6);
v_infoState_2940_ = lean_ctor_get(v___x_2933_, 7);
v_snapshotTasks_2941_ = lean_ctor_get(v___x_2933_, 8);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v___x_2933_, 5);
lean_dec(v_unused_3127_);
v___x_2943_ = v___x_2933_;
v_isShared_2944_ = v_isSharedCheck_3126_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_snapshotTasks_2941_);
lean_inc(v_infoState_2940_);
lean_inc(v_messages_2939_);
lean_inc(v_traceState_2938_);
lean_inc(v_auxDeclNGen_2937_);
lean_inc(v_ngen_2936_);
lean_inc(v_nextMacroScope_2935_);
lean_inc(v_env_2934_);
lean_dec(v___x_2933_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_3126_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
lean_inc(v_name_2928_);
v___x_2945_ = l_Lean_markAuxRecursor(v_env_2934_, v_name_2928_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 5, v___x_2895_);
lean_ctor_set(v___x_2943_, 0, v___x_2945_);
v___x_2947_ = v___x_2943_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_2945_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_nextMacroScope_2935_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_ngen_2936_);
lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_auxDeclNGen_2937_);
lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_traceState_2938_);
lean_ctor_set(v_reuseFailAlloc_3125_, 5, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_3125_, 6, v_messages_2939_);
lean_ctor_set(v_reuseFailAlloc_3125_, 7, v_infoState_2940_);
lean_ctor_set(v_reuseFailAlloc_3125_, 8, v_snapshotTasks_2941_);
v___x_2947_ = v_reuseFailAlloc_3125_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v_mctx_2950_; lean_object* v_zetaDeltaFVarIds_2951_; lean_object* v_postponed_2952_; lean_object* v_diag_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3123_; 
v___x_2948_ = lean_st_ref_put(v___y_2831_, v___x_2947_);
v___x_2949_ = lean_st_ref_take(v___y_2829_);
v_mctx_2950_ = lean_ctor_get(v___x_2949_, 0);
v_zetaDeltaFVarIds_2951_ = lean_ctor_get(v___x_2949_, 2);
v_postponed_2952_ = lean_ctor_get(v___x_2949_, 3);
v_diag_2953_ = lean_ctor_get(v___x_2949_, 4);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3123_ == 0)
{
lean_object* v_unused_3124_; 
v_unused_3124_ = lean_ctor_get(v___x_2949_, 1);
lean_dec(v_unused_3124_);
v___x_2955_ = v___x_2949_;
v_isShared_2956_ = v_isSharedCheck_3123_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_diag_2953_);
lean_inc(v_postponed_2952_);
lean_inc(v_zetaDeltaFVarIds_2951_);
lean_inc(v_mctx_2950_);
lean_dec(v___x_2949_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3123_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2907_);
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_mctx_2950_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_zetaDeltaFVarIds_2951_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_postponed_2952_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_diag_2953_);
v___x_2958_ = v_reuseFailAlloc_3122_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_env_2961_; lean_object* v_nextMacroScope_2962_; lean_object* v_ngen_2963_; lean_object* v_auxDeclNGen_2964_; lean_object* v_traceState_2965_; lean_object* v_messages_2966_; lean_object* v_infoState_2967_; lean_object* v_snapshotTasks_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3120_; 
v___x_2959_ = lean_st_ref_put(v___y_2829_, v___x_2958_);
v___x_2960_ = lean_st_ref_take(v___y_2831_);
v_env_2961_ = lean_ctor_get(v___x_2960_, 0);
v_nextMacroScope_2962_ = lean_ctor_get(v___x_2960_, 1);
v_ngen_2963_ = lean_ctor_get(v___x_2960_, 2);
v_auxDeclNGen_2964_ = lean_ctor_get(v___x_2960_, 3);
v_traceState_2965_ = lean_ctor_get(v___x_2960_, 4);
v_messages_2966_ = lean_ctor_get(v___x_2960_, 6);
v_infoState_2967_ = lean_ctor_get(v___x_2960_, 7);
v_snapshotTasks_2968_ = lean_ctor_get(v___x_2960_, 8);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v___x_2960_, 5);
lean_dec(v_unused_3121_);
v___x_2970_ = v___x_2960_;
v_isShared_2971_ = v_isSharedCheck_3120_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_snapshotTasks_2968_);
lean_inc(v_infoState_2967_);
lean_inc(v_messages_2966_);
lean_inc(v_traceState_2965_);
lean_inc(v_auxDeclNGen_2964_);
lean_inc(v_ngen_2963_);
lean_inc(v_nextMacroScope_2962_);
lean_inc(v_env_2961_);
lean_dec(v___x_2960_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3120_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_inc(v_name_2928_);
v___x_2972_ = l_Lean_addProtected(v_env_2961_, v_name_2928_);
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 5, v___x_2895_);
lean_ctor_set(v___x_2970_, 0, v___x_2972_);
v___x_2974_ = v___x_2970_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v___x_2972_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_nextMacroScope_2962_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_ngen_2963_);
lean_ctor_set(v_reuseFailAlloc_3119_, 3, v_auxDeclNGen_2964_);
lean_ctor_set(v_reuseFailAlloc_3119_, 4, v_traceState_2965_);
lean_ctor_set(v_reuseFailAlloc_3119_, 5, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_3119_, 6, v_messages_2966_);
lean_ctor_set(v_reuseFailAlloc_3119_, 7, v_infoState_2967_);
lean_ctor_set(v_reuseFailAlloc_3119_, 8, v_snapshotTasks_2968_);
v___x_2974_ = v_reuseFailAlloc_3119_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v_mctx_2977_; lean_object* v_zetaDeltaFVarIds_2978_; lean_object* v_postponed_2979_; lean_object* v_diag_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3117_; 
v___x_2975_ = lean_st_ref_put(v___y_2831_, v___x_2974_);
v___x_2976_ = lean_st_ref_take(v___y_2829_);
v_mctx_2977_ = lean_ctor_get(v___x_2976_, 0);
v_zetaDeltaFVarIds_2978_ = lean_ctor_get(v___x_2976_, 2);
v_postponed_2979_ = lean_ctor_get(v___x_2976_, 3);
v_diag_2980_ = lean_ctor_get(v___x_2976_, 4);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v___x_2976_, 1);
lean_dec(v_unused_3118_);
v___x_2982_ = v___x_2976_;
v_isShared_2983_ = v_isSharedCheck_3117_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_diag_2980_);
lean_inc(v_postponed_2979_);
lean_inc(v_zetaDeltaFVarIds_2978_);
lean_inc(v_mctx_2977_);
lean_dec(v___x_2976_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3117_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 1, v___x_2907_);
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_mctx_2977_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_zetaDeltaFVarIds_2978_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_postponed_2979_);
lean_ctor_set(v_reuseFailAlloc_3116_, 4, v_diag_2980_);
v___x_2985_ = v_reuseFailAlloc_3116_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_st_ref_put(v___y_2829_, v___x_2985_);
v___x_2987_ = l_Lean_Meta_mkPProdSndM(v___x_2912_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = l_Lean_Expr_const___override(v_name_2928_, v___x_2823_);
v___x_2990_ = l_Lean_mkAppN(v___x_2989_, v___x_2860_);
v___x_2991_ = lean_array_get(v___x_2818_, v_fs_2827_, v_val_2819_);
lean_dec_ref(v_fs_2827_);
v___x_2992_ = l_Lean_mkAppN(v___x_2991_, v___x_2853_);
lean_dec_ref(v___x_2853_);
v___x_2993_ = l_Lean_Expr_app___override(v___x_2992_, v_a_2988_);
v___x_2994_ = l_Lean_Meta_mkEq(v___x_2990_, v___x_2993_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc_n(v_a_2995_, 2);
lean_dec_ref_known(v___x_2994_, 1);
v___x_2996_ = lean_box(0);
v___x_2997_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_2995_, v___x_2996_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = l_Lean_Expr_mvarId_x21(v_a_2998_);
v___x_3000_ = l_Lean_Expr_fvarId_x21(v___x_2816_);
lean_dec_ref(v___x_2816_);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_2825_);
v___x_3002_ = lean_box(0);
v___x_3003_ = l_Lean_MVarId_cases(v___x_2999_, v___x_3000_, v___x_3001_, v___x_2861_, v___x_3002_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; size_t v_sz_3006_; lean_object* v___x_3007_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = lean_box(0);
v_sz_3006_ = lean_array_size(v_a_3004_);
v___x_3007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3004_, v_sz_3006_, v___x_2812_, v___x_3005_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v_a_3004_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v___x_3008_; lean_object* v_a_3009_; lean_object* v___x_3010_; 
lean_dec_ref_known(v___x_3007_, 1);
v___x_3008_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_2998_, v___y_2829_);
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
lean_inc(v_a_3009_);
lean_dec_ref(v___x_3008_);
v___x_3010_ = l_Lean_Meta_mkForallFVars(v___x_2860_, v_a_2995_, v___x_2861_, v___x_2820_, v___x_2820_, v___x_2862_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = l_Lean_Meta_mkLambdaFVars(v___x_2860_, v_a_3009_, v___x_2861_, v___x_2820_, v___x_2861_, v___x_2820_, v___x_2862_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec_ref(v___x_2860_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3015_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref_known(v___x_3012_, 1);
lean_inc(v_brecOnEqName_2826_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 2, v_a_3011_);
lean_ctor_set(v___x_2930_, 1, v_levelParams_2822_);
lean_ctor_set(v___x_2930_, 0, v_brecOnEqName_2826_);
v___x_3015_ = v___x_2930_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_brecOnEqName_2826_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v_levelParams_2822_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_a_3011_);
v___x_3015_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3016_ = lean_box(0);
lean_inc(v_brecOnEqName_2826_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set_tag(v___x_2841_, 1);
lean_ctor_set(v___x_2841_, 1, v___x_3016_);
lean_ctor_set(v___x_2841_, 0, v_brecOnEqName_2826_);
v___x_3018_ = v___x_2841_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_brecOnEqName_2826_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3020_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 2, v___x_3018_);
lean_ctor_set(v___x_2879_, 1, v_a_3013_);
lean_ctor_set(v___x_2879_, 0, v___x_3015_);
v___x_3020_ = v___x_2879_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_a_3013_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v_a_3022_; lean_object* v___x_3023_; 
v___x_3021_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3020_, v___y_2831_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = l_Lean_addDecl(v_a_3022_, v___x_2861_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3063_; 
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; 
v_unused_3064_ = lean_ctor_get(v___x_3023_, 0);
lean_dec(v_unused_3064_);
v___x_3025_ = v___x_3023_;
v_isShared_3026_ = v_isSharedCheck_3063_;
goto v_resetjp_3024_;
}
else
{
lean_dec(v___x_3023_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3063_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3027_; lean_object* v_env_3028_; lean_object* v_nextMacroScope_3029_; lean_object* v_ngen_3030_; lean_object* v_auxDeclNGen_3031_; lean_object* v_traceState_3032_; lean_object* v_messages_3033_; lean_object* v_infoState_3034_; lean_object* v_snapshotTasks_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3061_; 
v___x_3027_ = lean_st_ref_take(v___y_2831_);
v_env_3028_ = lean_ctor_get(v___x_3027_, 0);
v_nextMacroScope_3029_ = lean_ctor_get(v___x_3027_, 1);
v_ngen_3030_ = lean_ctor_get(v___x_3027_, 2);
v_auxDeclNGen_3031_ = lean_ctor_get(v___x_3027_, 3);
v_traceState_3032_ = lean_ctor_get(v___x_3027_, 4);
v_messages_3033_ = lean_ctor_get(v___x_3027_, 6);
v_infoState_3034_ = lean_ctor_get(v___x_3027_, 7);
v_snapshotTasks_3035_ = lean_ctor_get(v___x_3027_, 8);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3061_ == 0)
{
lean_object* v_unused_3062_; 
v_unused_3062_ = lean_ctor_get(v___x_3027_, 5);
lean_dec(v_unused_3062_);
v___x_3037_ = v___x_3027_;
v_isShared_3038_ = v_isSharedCheck_3061_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_snapshotTasks_3035_);
lean_inc(v_infoState_3034_);
lean_inc(v_messages_3033_);
lean_inc(v_traceState_3032_);
lean_inc(v_auxDeclNGen_3031_);
lean_inc(v_ngen_3030_);
lean_inc(v_nextMacroScope_3029_);
lean_inc(v_env_3028_);
lean_dec(v___x_3027_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3061_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3039_ = l_Lean_addProtected(v_env_3028_, v_brecOnEqName_2826_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 5, v___x_2895_);
lean_ctor_set(v___x_3037_, 0, v___x_3039_);
v___x_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v_nextMacroScope_3029_);
lean_ctor_set(v_reuseFailAlloc_3060_, 2, v_ngen_3030_);
lean_ctor_set(v_reuseFailAlloc_3060_, 3, v_auxDeclNGen_3031_);
lean_ctor_set(v_reuseFailAlloc_3060_, 4, v_traceState_3032_);
lean_ctor_set(v_reuseFailAlloc_3060_, 5, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_3060_, 6, v_messages_3033_);
lean_ctor_set(v_reuseFailAlloc_3060_, 7, v_infoState_3034_);
lean_ctor_set(v_reuseFailAlloc_3060_, 8, v_snapshotTasks_3035_);
v___x_3041_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v_mctx_3044_; lean_object* v_zetaDeltaFVarIds_3045_; lean_object* v_postponed_3046_; lean_object* v_diag_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3058_; 
v___x_3042_ = lean_st_ref_put(v___y_2831_, v___x_3041_);
v___x_3043_ = lean_st_ref_take(v___y_2829_);
v_mctx_3044_ = lean_ctor_get(v___x_3043_, 0);
v_zetaDeltaFVarIds_3045_ = lean_ctor_get(v___x_3043_, 2);
v_postponed_3046_ = lean_ctor_get(v___x_3043_, 3);
v_diag_3047_ = lean_ctor_get(v___x_3043_, 4);
v_isSharedCheck_3058_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3058_ == 0)
{
lean_object* v_unused_3059_; 
v_unused_3059_ = lean_ctor_get(v___x_3043_, 1);
lean_dec(v_unused_3059_);
v___x_3049_ = v___x_3043_;
v_isShared_3050_ = v_isSharedCheck_3058_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_diag_3047_);
lean_inc(v_postponed_3046_);
lean_inc(v_zetaDeltaFVarIds_3045_);
lean_inc(v_mctx_3044_);
lean_dec(v___x_3043_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3058_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 1, v___x_2907_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_mctx_3044_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_2907_);
lean_ctor_set(v_reuseFailAlloc_3057_, 2, v_zetaDeltaFVarIds_3045_);
lean_ctor_set(v_reuseFailAlloc_3057_, 3, v_postponed_3046_);
lean_ctor_set(v_reuseFailAlloc_3057_, 4, v_diag_3047_);
v___x_3052_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = lean_st_ref_put(v___y_2829_, v___x_3052_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 0, v___x_3005_);
v___x_3055_ = v___x_3025_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3005_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2826_);
return v___x_3023_;
}
}
}
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v_a_3011_);
lean_del_object(v___x_2930_);
lean_del_object(v___x_2879_);
lean_del_object(v___x_2841_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_levelParams_2822_);
v_a_3068_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3012_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3012_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_3009_);
lean_del_object(v___x_2930_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_del_object(v___x_2841_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_levelParams_2822_);
v_a_3076_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3010_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3010_);
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
lean_dec(v_a_2998_);
lean_dec(v_a_2995_);
lean_del_object(v___x_2930_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_del_object(v___x_2841_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_levelParams_2822_);
return v___x_3007_;
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_2998_);
lean_dec(v_a_2995_);
lean_del_object(v___x_2930_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_del_object(v___x_2841_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_levelParams_2822_);
v_a_3084_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3003_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3003_);
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
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_2995_);
lean_del_object(v___x_2930_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_del_object(v___x_2841_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_levelParams_2822_);
lean_dec_ref(v___x_2816_);
v_a_3092_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_2997_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_2997_);
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
lean_del_object(v___x_2930_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_del_object(v___x_2841_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_levelParams_2822_);
lean_dec_ref(v___x_2816_);
v_a_3100_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_2994_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_2994_);
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
lean_del_object(v___x_2930_);
lean_dec(v_name_2928_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec_ref(v___x_2816_);
v_a_3108_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_2987_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_2987_);
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
lean_dec(v_a_2920_);
lean_dec_ref(v___x_2912_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec_ref(v___x_2816_);
return v___x_2926_;
}
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_dec(v_a_2916_);
lean_dec_ref(v___x_2912_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec_ref(v___x_2816_);
v_a_3133_ = lean_ctor_get(v___x_2917_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_2917_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_2917_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_2917_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v___x_2912_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec_ref(v___x_2816_);
v_a_3141_ = lean_ctor_get(v___x_2915_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_2915_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_2915_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_2915_);
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
lean_dec_ref(v___x_2912_);
lean_del_object(v___x_2879_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec_ref(v___x_2816_);
v_a_3149_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_2913_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_2913_);
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
}
}
}
}
}
else
{
lean_dec(v_a_2869_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec(v_brecOnGoName_2821_);
lean_dec_ref(v___x_2816_);
return v___x_2875_;
}
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_a_2864_);
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2853_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec(v_brecOnGoName_2821_);
lean_dec_ref(v___x_2816_);
v_a_3168_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_2865_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_2865_);
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
lean_dec_ref(v___x_2860_);
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2853_);
lean_dec_ref(v___x_2847_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec(v_brecOnGoName_2821_);
lean_dec_ref(v___x_2816_);
v_a_3176_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_2863_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_2863_);
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
lean_dec_ref(v___x_2854_);
lean_dec_ref(v___x_2853_);
lean_dec_ref(v___x_2851_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2847_);
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec(v_brecOnGoName_2821_);
lean_dec_ref(v___x_2816_);
v_a_3184_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_2857_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_2857_);
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
lean_del_object(v___x_2841_);
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec(v_brecOnGoName_2821_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v___x_2810_);
lean_dec_ref(v___x_2806_);
v_a_3192_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_2844_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_2844_);
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
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v_fs_2827_);
lean_dec(v_brecOnEqName_2826_);
lean_dec(v_brecOnName_2824_);
lean_dec(v___x_2823_);
lean_dec(v_levelParams_2822_);
lean_dec(v_brecOnGoName_2821_);
lean_dec_ref(v___x_2816_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v___x_2810_);
lean_dec_ref(v___x_2806_);
lean_dec(v___x_2803_);
v_a_3202_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_2837_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_2837_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3210_ = _args[0];
lean_object* v_tail_3211_ = _args[1];
lean_object* v_recName_3212_ = _args[2];
lean_object* v___x_3213_ = _args[3];
lean_object* v___x_3214_ = _args[4];
lean_object* v___x_3215_ = _args[5];
lean_object* v___x_3216_ = _args[6];
lean_object* v___x_3217_ = _args[7];
lean_object* v_sz_3218_ = _args[8];
lean_object* v___x_3219_ = _args[9];
lean_object* v___x_3220_ = _args[10];
lean_object* v___x_3221_ = _args[11];
lean_object* v___x_3222_ = _args[12];
lean_object* v___x_3223_ = _args[13];
lean_object* v___x_3224_ = _args[14];
lean_object* v___x_3225_ = _args[15];
lean_object* v_val_3226_ = _args[16];
lean_object* v___x_3227_ = _args[17];
lean_object* v_brecOnGoName_3228_ = _args[18];
lean_object* v_levelParams_3229_ = _args[19];
lean_object* v___x_3230_ = _args[20];
lean_object* v_brecOnName_3231_ = _args[21];
lean_object* v___x_3232_ = _args[22];
lean_object* v_brecOnEqName_3233_ = _args[23];
lean_object* v_fs_3234_ = _args[24];
lean_object* v___y_3235_ = _args[25];
lean_object* v___y_3236_ = _args[26];
lean_object* v___y_3237_ = _args[27];
lean_object* v___y_3238_ = _args[28];
lean_object* v___y_3239_ = _args[29];
_start:
{
size_t v_sz_boxed_3240_; size_t v___x_30618__boxed_3241_; uint8_t v___x_30626__boxed_3242_; lean_object* v_res_3243_; 
v_sz_boxed_3240_ = lean_unbox_usize(v_sz_3218_);
lean_dec(v_sz_3218_);
v___x_30618__boxed_3241_ = lean_unbox_usize(v___x_3219_);
lean_dec(v___x_3219_);
v___x_30626__boxed_3242_ = lean_unbox(v___x_3227_);
v_res_3243_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3210_, v_tail_3211_, v_recName_3212_, v___x_3213_, v___x_3214_, v___x_3215_, v___x_3216_, v___x_3217_, v_sz_boxed_3240_, v___x_30618__boxed_3241_, v___x_3220_, v___x_3221_, v___x_3222_, v___x_3223_, v___x_3224_, v___x_3225_, v_val_3226_, v___x_30626__boxed_3242_, v_brecOnGoName_3228_, v_levelParams_3229_, v___x_3230_, v_brecOnName_3231_, v___x_3232_, v_brecOnEqName_3233_, v_fs_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___x_3232_);
lean_dec(v_val_3226_);
lean_dec_ref(v___x_3225_);
lean_dec(v___x_3224_);
lean_dec_ref(v___x_3220_);
lean_dec(v___x_3216_);
lean_dec(v___x_3215_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3244_, lean_object* v_a_3245_, uint8_t v___x_3246_, lean_object* v_f_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; uint8_t v___x_3256_; lean_object* v___x_3257_; 
lean_inc_ref(v_targs_3244_);
v___x_3253_ = lean_array_push(v_targs_3244_, v_f_3247_);
v___x_3254_ = l_Lean_mkAppN(v_a_3245_, v_targs_3244_);
lean_dec_ref(v_targs_3244_);
v___x_3255_ = 0;
v___x_3256_ = 1;
v___x_3257_ = l_Lean_Meta_mkForallFVars(v___x_3253_, v___x_3254_, v___x_3255_, v___x_3246_, v___x_3246_, v___x_3256_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec_ref(v___x_3253_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3258_, lean_object* v_a_3259_, lean_object* v___x_3260_, lean_object* v_f_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
uint8_t v___x_31340__boxed_3267_; lean_object* v_res_3268_; 
v___x_31340__boxed_3267_ = lean_unbox(v___x_3260_);
v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3258_, v_a_3259_, v___x_31340__boxed_3267_, v_f_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3272_, uint8_t v___x_3273_, lean_object* v___x_3274_, lean_object* v_targs_3275_, lean_object* v_x_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3282_ = lean_box(v___x_3273_);
lean_inc_ref(v_targs_3275_);
v___f_3283_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3283_, 0, v_targs_3275_);
lean_closure_set(v___f_3283_, 1, v_a_3272_);
lean_closure_set(v___f_3283_, 2, v___x_3282_);
v___x_3284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3285_ = l_Lean_mkAppN(v___x_3274_, v_targs_3275_);
lean_dec_ref(v_targs_3275_);
v___x_3286_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3284_, v___x_3285_, v___f_3283_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3287_, lean_object* v___x_3288_, lean_object* v___x_3289_, lean_object* v_targs_3290_, lean_object* v_x_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
uint8_t v___x_31374__boxed_3297_; lean_object* v_res_3298_; 
v___x_31374__boxed_3297_ = lean_unbox(v___x_3288_);
v_res_3298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3287_, v___x_31374__boxed_3297_, v___x_3289_, v_targs_3290_, v_x_3291_, v___y_3292_, v___y_3293_, v___y_3294_, v___y_3295_);
lean_dec(v___y_3295_);
lean_dec_ref(v___y_3294_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec_ref(v_x_3291_);
return v_res_3298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3306_, 0, v_a_3299_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3307_, v_x_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec_ref(v_x_3308_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v___x_3316_, lean_object* v___x_3317_, lean_object* v_as_3318_, size_t v_sz_3319_, size_t v_i_3320_, lean_object* v_b_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
uint8_t v___x_3327_; 
v___x_3327_ = lean_usize_dec_lt(v_i_3320_, v_sz_3319_);
if (v___x_3327_ == 0)
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_b_3321_);
return v___x_3328_;
}
else
{
lean_object* v_snd_3329_; lean_object* v_fst_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3427_; 
v_snd_3329_ = lean_ctor_get(v_b_3321_, 1);
v_fst_3330_ = lean_ctor_get(v_b_3321_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_b_3321_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3332_ = v_b_3321_;
v_isShared_3333_ = v_isSharedCheck_3427_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_snd_3329_);
lean_inc(v_fst_3330_);
lean_dec(v_b_3321_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3427_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v_fst_3334_; lean_object* v_snd_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3426_; 
v_fst_3334_ = lean_ctor_get(v_snd_3329_, 0);
v_snd_3335_ = lean_ctor_get(v_snd_3329_, 1);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_snd_3329_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3337_ = v_snd_3329_;
v_isShared_3338_ = v_isSharedCheck_3426_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_snd_3335_);
lean_inc(v_fst_3334_);
lean_dec(v_snd_3329_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3426_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v_next_3347_; 
v_next_3347_ = lean_ctor_get(v_snd_3335_, 0);
lean_inc(v_next_3347_);
if (lean_obj_tag(v_next_3347_) == 0)
{
goto v___jp_3339_;
}
else
{
lean_object* v_upperBound_3348_; lean_object* v_val_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3425_; 
v_upperBound_3348_ = lean_ctor_get(v_snd_3335_, 1);
v_val_3349_ = lean_ctor_get(v_next_3347_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v_next_3347_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3351_ = v_next_3347_;
v_isShared_3352_ = v_isSharedCheck_3425_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_val_3349_);
lean_dec(v_next_3347_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3425_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
uint8_t v___x_3353_; 
v___x_3353_ = lean_nat_dec_lt(v_val_3349_, v_upperBound_3348_);
if (v___x_3353_ == 0)
{
lean_del_object(v___x_3351_);
lean_dec(v_val_3349_);
goto v___jp_3339_;
}
else
{
lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3422_; 
lean_inc(v_upperBound_3348_);
lean_del_object(v___x_3337_);
lean_del_object(v___x_3332_);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_snd_3335_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; lean_object* v_unused_3424_; 
v_unused_3423_ = lean_ctor_get(v_snd_3335_, 1);
lean_dec(v_unused_3423_);
v_unused_3424_ = lean_ctor_get(v_snd_3335_, 0);
lean_dec(v_unused_3424_);
v___x_3355_ = v_snd_3335_;
v_isShared_3356_ = v_isSharedCheck_3422_;
goto v_resetjp_3354_;
}
else
{
lean_dec(v_snd_3335_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3422_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v_array_3357_; lean_object* v_start_3358_; lean_object* v_stop_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v_array_3357_ = lean_ctor_get(v_fst_3334_, 0);
v_start_3358_ = lean_ctor_get(v_fst_3334_, 1);
v_stop_3359_ = lean_ctor_get(v_fst_3334_, 2);
v___x_3360_ = lean_unsigned_to_nat(1u);
v___x_3361_ = lean_nat_add(v_val_3349_, v___x_3360_);
lean_dec(v_val_3349_);
lean_inc(v___x_3361_);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3361_);
v___x_3363_ = v___x_3351_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3363_);
v___x_3365_ = v___x_3355_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_upperBound_3348_);
v___x_3365_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
uint8_t v___x_3366_; 
v___x_3366_ = lean_nat_dec_lt(v_start_3358_, v_stop_3359_);
if (v___x_3366_ == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec(v___x_3361_);
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v_fst_3334_);
lean_ctor_set(v___x_3367_, 1, v___x_3365_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_fst_3330_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
return v___x_3369_;
}
else
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3416_; 
lean_inc(v_stop_3359_);
lean_inc(v_start_3358_);
lean_inc_ref(v_array_3357_);
v_isSharedCheck_3416_ = !lean_is_exclusive(v_fst_3334_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; lean_object* v_unused_3418_; lean_object* v_unused_3419_; 
v_unused_3417_ = lean_ctor_get(v_fst_3334_, 2);
lean_dec(v_unused_3417_);
v_unused_3418_ = lean_ctor_get(v_fst_3334_, 1);
lean_dec(v_unused_3418_);
v_unused_3419_ = lean_ctor_get(v_fst_3334_, 0);
lean_dec(v_unused_3419_);
v___x_3371_ = v_fst_3334_;
v_isShared_3372_ = v_isSharedCheck_3416_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v_fst_3334_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3416_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v_a_3373_; lean_object* v___x_3374_; 
v_a_3373_ = lean_array_uget_borrowed(v_as_3318_, v_i_3320_);
lean_inc(v___y_3325_);
lean_inc_ref(v___y_3324_);
lean_inc(v___y_3323_);
lean_inc_ref(v___y_3322_);
lean_inc(v_a_3373_);
v___x_3374_ = lean_infer_type(v_a_3373_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; uint8_t v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___f_3379_; uint8_t v___x_3380_; lean_object* v___x_3381_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = lean_nat_dec_lt(v___x_3316_, v___x_3317_);
v___x_3377_ = lean_array_fget_borrowed(v_array_3357_, v_start_3358_);
v___x_3378_ = lean_box(v___x_3376_);
lean_inc(v___x_3377_);
lean_inc(v_a_3373_);
v___f_3379_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3379_, 0, v_a_3373_);
lean_closure_set(v___f_3379_, 1, v___x_3378_);
lean_closure_set(v___f_3379_, 2, v___x_3377_);
v___x_3380_ = 0;
v___x_3381_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3375_, v___f_3379_, v___x_3380_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___f_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
v___f_3383_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3383_, 0, v_a_3382_);
v___x_3384_ = lean_nat_add(v_start_3358_, v___x_3360_);
lean_dec(v_start_3358_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 1, v___x_3384_);
v___x_3386_ = v___x_3371_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_array_3357_);
lean_ctor_set(v_reuseFailAlloc_3399_, 1, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3399_, 2, v_stop_3359_);
v___x_3386_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; size_t v___x_3396_; size_t v___x_3397_; 
v___x_3387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3388_ = l_Nat_reprFast(v___x_3361_);
v___x_3389_ = lean_string_append(v___x_3387_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v___x_3390_ = lean_box(0);
v___x_3391_ = l_Lean_Name_str___override(v___x_3390_, v___x_3389_);
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v___f_3383_);
v___x_3393_ = lean_array_push(v_fst_3330_, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3386_);
lean_ctor_set(v___x_3394_, 1, v___x_3365_);
v___x_3395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
v___x_3396_ = ((size_t)1ULL);
v___x_3397_ = lean_usize_add(v_i_3320_, v___x_3396_);
v_i_3320_ = v___x_3397_;
v_b_3321_ = v___x_3395_;
goto _start;
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
lean_del_object(v___x_3371_);
lean_dec_ref(v___x_3365_);
lean_dec(v___x_3361_);
lean_dec(v_stop_3359_);
lean_dec(v_start_3358_);
lean_dec_ref(v_array_3357_);
lean_dec(v_fst_3330_);
v_a_3400_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3402_ = v___x_3381_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3381_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3400_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
lean_del_object(v___x_3371_);
lean_dec_ref(v___x_3365_);
lean_dec(v___x_3361_);
lean_dec(v_stop_3359_);
lean_dec(v_start_3358_);
lean_dec_ref(v_array_3357_);
lean_dec(v_fst_3330_);
v_a_3408_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3415_ == 0)
{
v___x_3410_ = v___x_3374_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3374_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3408_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
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
v___jp_3339_:
{
lean_object* v___x_3341_; 
if (v_isShared_3338_ == 0)
{
v___x_3341_ = v___x_3337_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_fst_3334_);
lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_snd_3335_);
v___x_3341_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
lean_object* v___x_3343_; 
if (v_isShared_3333_ == 0)
{
lean_ctor_set(v___x_3332_, 1, v___x_3341_);
v___x_3343_ = v___x_3332_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_fst_3330_);
lean_ctor_set(v_reuseFailAlloc_3345_, 1, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3344_; 
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v___x_3428_, lean_object* v___x_3429_, lean_object* v_as_3430_, lean_object* v_sz_3431_, lean_object* v_i_3432_, lean_object* v_b_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
size_t v_sz_boxed_3439_; size_t v_i_boxed_3440_; lean_object* v_res_3441_; 
v_sz_boxed_3439_ = lean_unbox_usize(v_sz_3431_);
lean_dec(v_sz_3431_);
v_i_boxed_3440_ = lean_unbox_usize(v_i_3432_);
lean_dec(v_i_3432_);
v_res_3441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3428_, v___x_3429_, v_as_3430_, v_sz_boxed_3439_, v_i_boxed_3440_, v_b_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_);
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3436_);
lean_dec(v___y_3435_);
lean_dec_ref(v___y_3434_);
lean_dec_ref(v_as_3430_);
lean_dec(v___x_3429_);
lean_dec(v___x_3428_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3442_, size_t v_i_3443_, lean_object* v_bs_3444_){
_start:
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_usize_dec_lt(v_i_3443_, v_sz_3442_);
if (v___x_3445_ == 0)
{
return v_bs_3444_;
}
else
{
lean_object* v_v_3446_; lean_object* v_fst_3447_; lean_object* v_snd_3448_; lean_object* v___x_3450_; uint8_t v_isShared_3451_; uint8_t v_isSharedCheck_3464_; 
v_v_3446_ = lean_array_uget(v_bs_3444_, v_i_3443_);
v_fst_3447_ = lean_ctor_get(v_v_3446_, 0);
v_snd_3448_ = lean_ctor_get(v_v_3446_, 1);
v_isSharedCheck_3464_ = !lean_is_exclusive(v_v_3446_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3450_ = v_v_3446_;
v_isShared_3451_ = v_isSharedCheck_3464_;
goto v_resetjp_3449_;
}
else
{
lean_inc(v_snd_3448_);
lean_inc(v_fst_3447_);
lean_dec(v_v_3446_);
v___x_3450_ = lean_box(0);
v_isShared_3451_ = v_isSharedCheck_3464_;
goto v_resetjp_3449_;
}
v_resetjp_3449_:
{
lean_object* v___x_3452_; lean_object* v_bs_x27_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v___x_3452_ = lean_unsigned_to_nat(0u);
v_bs_x27_3453_ = lean_array_uset(v_bs_3444_, v_i_3443_, v___x_3452_);
v___x_3454_ = 0;
v___x_3455_ = lean_box(v___x_3454_);
if (v_isShared_3451_ == 0)
{
lean_ctor_set(v___x_3450_, 0, v___x_3455_);
v___x_3457_ = v___x_3450_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3463_, 1, v_snd_3448_);
v___x_3457_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; size_t v___x_3459_; size_t v___x_3460_; lean_object* v___x_3461_; 
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v_fst_3447_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = ((size_t)1ULL);
v___x_3460_ = lean_usize_add(v_i_3443_, v___x_3459_);
v___x_3461_ = lean_array_uset(v_bs_x27_3453_, v_i_3443_, v___x_3458_);
v_i_3443_ = v___x_3460_;
v_bs_3444_ = v___x_3461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3465_, lean_object* v_i_3466_, lean_object* v_bs_3467_){
_start:
{
size_t v_sz_boxed_3468_; size_t v_i_boxed_3469_; lean_object* v_res_3470_; 
v_sz_boxed_3468_ = lean_unbox_usize(v_sz_3465_);
lean_dec(v_sz_3465_);
v_i_boxed_3469_ = lean_unbox_usize(v_i_3466_);
lean_dec(v_i_3466_);
v_res_3470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3468_, v_i_boxed_3469_, v_bs_3467_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3471_, lean_object* v___x_3472_, lean_object* v_a_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v___x_30168__overap_3479_; lean_object* v___x_3480_; 
v___x_30168__overap_3479_ = l_instInhabitedOfMonad___redArg(v___x_3471_, v___x_3472_);
lean_inc(v___y_3477_);
lean_inc_ref(v___y_3476_);
lean_inc(v___y_3475_);
lean_inc_ref(v___y_3474_);
v___x_3480_ = lean_apply_5(v___x_30168__overap_3479_, v___y_3474_, v___y_3475_, v___y_3476_, v___y_3477_, lean_box(0));
return v___x_3480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3481_, lean_object* v___x_3482_, lean_object* v_a_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3481_, v___x_3482_, v_a_3483_, v___y_3484_, v___y_3485_, v___y_3486_, v___y_3487_);
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
lean_object* v___x_3550_; lean_object* v_toApplicative_3551_; lean_object* v_toFunctor_3552_; lean_object* v_toSeq_3553_; lean_object* v_toSeqLeft_3554_; lean_object* v_toSeqRight_3555_; lean_object* v___f_3556_; lean_object* v___f_3557_; lean_object* v___f_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; lean_object* v___f_3561_; lean_object* v___f_3562_; lean_object* v___f_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v_toApplicative_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3623_; 
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
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3623_ == 0)
{
lean_object* v_unused_3624_; 
v_unused_3624_ = lean_ctor_get(v___x_3566_, 1);
lean_dec(v_unused_3624_);
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3623_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_toApplicative_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3623_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v_toFunctor_3571_; lean_object* v_toSeq_3572_; lean_object* v_toSeqLeft_3573_; lean_object* v_toSeqRight_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3621_; 
v_toFunctor_3571_ = lean_ctor_get(v_toApplicative_3567_, 0);
v_toSeq_3572_ = lean_ctor_get(v_toApplicative_3567_, 2);
v_toSeqLeft_3573_ = lean_ctor_get(v_toApplicative_3567_, 3);
v_toSeqRight_3574_ = lean_ctor_get(v_toApplicative_3567_, 4);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_toApplicative_3567_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v_toApplicative_3567_, 1);
lean_dec(v_unused_3622_);
v___x_3576_ = v_toApplicative_3567_;
v_isShared_3577_ = v_isSharedCheck_3621_;
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
v_isShared_3577_ = v_isSharedCheck_3621_;
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
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v___f_3578_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v___f_3585_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v___f_3584_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v___f_3583_);
v___x_3587_ = v_reuseFailAlloc_3620_;
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
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3587_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___f_3579_);
v___x_3589_ = v_reuseFailAlloc_3619_;
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
lean_object* v___x_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___f_3597_; lean_object* v___f_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v_snd_3603_; lean_object* v_fst_3604_; lean_object* v_fst_3605_; lean_object* v_snd_3606_; lean_object* v___x_3607_; 
v___x_3594_ = lean_box(0);
v___x_3595_ = 0;
v___x_3596_ = l_Lean_instInhabitedExpr;
v___f_3597_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3597_, 0, v___x_3589_);
lean_closure_set(v___f_3597_, 1, v___x_3596_);
v___f_3598_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3598_, 0, v___f_3597_);
v___x_3599_ = lean_box(v___x_3595_);
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
lean_ctor_set(v___x_3600_, 1, v___f_3598_);
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3594_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = lean_array_get(v___x_3601_, v_declInfos_3541_, v___x_3590_);
lean_dec_ref_known(v___x_3601_, 2);
v_snd_3603_ = lean_ctor_get(v___x_3602_, 1);
lean_inc(v_snd_3603_);
v_fst_3604_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_fst_3604_);
lean_dec(v___x_3602_);
v_fst_3605_ = lean_ctor_get(v_snd_3603_, 0);
lean_inc(v_fst_3605_);
v_snd_3606_ = lean_ctor_get(v_snd_3603_, 1);
lean_inc(v_snd_3606_);
lean_dec(v_snd_3603_);
lean_inc(v___y_3548_);
lean_inc_ref(v___y_3547_);
lean_inc(v___y_3546_);
lean_inc_ref(v___y_3545_);
lean_inc_ref(v_acc_3544_);
v___x_3607_ = lean_apply_6(v_snd_3606_, v_acc_3544_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_, lean_box(0));
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; uint8_t v___x_3609_; lean_object* v___x_3610_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
v___x_3609_ = lean_unbox(v_fst_3605_);
lean_dec(v_fst_3605_);
v___x_3610_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3544_, v_declInfos_3541_, v_k_3542_, v_kind_3543_, v_fst_3604_, v___x_3609_, v_a_3608_, v_kind_3543_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3610_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_fst_3605_);
lean_dec(v_fst_3604_);
lean_dec_ref(v_acc_3544_);
lean_dec_ref(v_k_3542_);
lean_dec_ref(v_declInfos_3541_);
v_a_3611_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3607_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3607_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3625_, lean_object* v_declInfos_3626_, lean_object* v_k_3627_, uint8_t v_kind_3628_, lean_object* v_b_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_array_push(v_acc_3625_, v_b_3629_);
v___x_3636_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3626_, v_k_3627_, v_kind_3628_, v___x_3635_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3637_, lean_object* v_declInfos_3638_, lean_object* v_k_3639_, lean_object* v_kind_3640_, lean_object* v_name_3641_, lean_object* v_bi_3642_, lean_object* v_type_3643_, lean_object* v_kind_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
uint8_t v_kind_boxed_3650_; uint8_t v_bi_boxed_3651_; uint8_t v_kind_boxed_3652_; lean_object* v_res_3653_; 
v_kind_boxed_3650_ = lean_unbox(v_kind_3640_);
v_bi_boxed_3651_ = lean_unbox(v_bi_3642_);
v_kind_boxed_3652_ = lean_unbox(v_kind_3644_);
v_res_3653_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3637_, v_declInfos_3638_, v_k_3639_, v_kind_boxed_3650_, v_name_3641_, v_bi_boxed_3651_, v_type_3643_, v_kind_boxed_3652_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
return v_res_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3654_, lean_object* v_k_3655_, lean_object* v_kind_3656_, lean_object* v_acc_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
uint8_t v_kind_boxed_3663_; lean_object* v_res_3664_; 
v_kind_boxed_3663_ = lean_unbox(v_kind_3656_);
v_res_3664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3654_, v_k_3655_, v_kind_boxed_3663_, v_acc_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec(v___y_3661_);
lean_dec_ref(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v___y_3658_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3665_, lean_object* v_k_3666_, uint8_t v_kind_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3674_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3665_, v_k_3666_, v_kind_3667_, v___x_3673_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
return v___x_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3675_, lean_object* v_k_3676_, lean_object* v_kind_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
uint8_t v_kind_boxed_3683_; lean_object* v_res_3684_; 
v_kind_boxed_3683_ = lean_unbox(v_kind_3677_);
v_res_3684_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3675_, v_k_3676_, v_kind_boxed_3683_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3685_, lean_object* v_k_3686_, uint8_t v_kind_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
size_t v_sz_3693_; size_t v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v_sz_3693_ = lean_array_size(v_declInfos_3685_);
v___x_3694_ = ((size_t)0ULL);
v___x_3695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3693_, v___x_3694_, v_declInfos_3685_);
v___x_3696_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3695_, v_k_3686_, v_kind_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
return v___x_3696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3697_, lean_object* v_k_3698_, lean_object* v_kind_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
uint8_t v_kind_boxed_3705_; lean_object* v_res_3706_; 
v_kind_boxed_3705_ = lean_unbox(v_kind_3699_);
v_res_3706_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3697_, v_k_3698_, v_kind_boxed_3705_, v___y_3700_, v___y_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
return v_res_3706_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3708_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3709_ = lean_unsigned_to_nat(4u);
v___x_3710_ = lean_unsigned_to_nat(202u);
v___x_3711_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3712_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3713_ = l_mkPanicMessageWithDecl(v___x_3712_, v___x_3711_, v___x_3710_, v___x_3709_, v___x_3708_);
return v___x_3713_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3720_ = l_Lean_stringToMessageData(v___x_3719_);
return v___x_3720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3726_, lean_object* v_numMotives_3727_, lean_object* v_numMinors_3728_, lean_object* v___x_3729_, lean_object* v___x_3730_, lean_object* v_all_3731_, lean_object* v___x_3732_, lean_object* v_head_3733_, lean_object* v_tail_3734_, lean_object* v_recName_3735_, lean_object* v_brecOnGoName_3736_, lean_object* v_levelParams_3737_, lean_object* v_brecOnName_3738_, lean_object* v_brecOnEqName_3739_, lean_object* v_type_3740_, lean_object* v_refArgs_3741_, lean_object* v_refBody_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; uint8_t v___x_3751_; 
v___x_3748_ = lean_nat_add(v_nParams_3726_, v_numMotives_3727_);
v___x_3749_ = lean_nat_add(v___x_3748_, v_numMinors_3728_);
v___x_3750_ = lean_array_get_size(v_refArgs_3741_);
v___x_3751_ = lean_nat_dec_lt(v___x_3749_, v___x_3750_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_dec(v___x_3749_);
lean_dec(v___x_3748_);
lean_dec_ref(v_refArgs_3741_);
lean_dec_ref(v_type_3740_);
lean_dec(v_brecOnEqName_3739_);
lean_dec(v_brecOnName_3738_);
lean_dec(v_levelParams_3737_);
lean_dec(v_brecOnGoName_3736_);
lean_dec(v_recName_3735_);
lean_dec(v_tail_3734_);
lean_dec(v_head_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_all_3731_);
lean_dec(v___x_3730_);
lean_dec_ref(v___x_3729_);
lean_dec(v_nParams_3726_);
v___x_3752_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3753_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3752_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3753_;
}
else
{
lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3754_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3726_);
lean_inc_ref_n(v_refArgs_3741_, 2);
v___x_3755_ = l_Array_toSubarray___redArg(v_refArgs_3741_, v___x_3754_, v_nParams_3726_);
lean_inc(v___x_3748_);
v___x_3756_ = l_Array_toSubarray___redArg(v_refArgs_3741_, v_nParams_3726_, v___x_3748_);
v___x_3757_ = l_Subarray_copy___redArg(v___x_3756_);
v___x_3758_ = l_Lean_Expr_getAppFn(v_refBody_3742_);
v___x_3759_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3757_, v___x_3758_);
lean_dec_ref(v___x_3758_);
if (lean_obj_tag(v___x_3759_) == 1)
{
lean_object* v_val_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
lean_dec_ref(v_type_3740_);
v_val_3760_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_val_3760_);
lean_dec_ref_known(v___x_3759_, 1);
v___x_3761_ = lean_unsigned_to_nat(1u);
v___x_3762_ = lean_nat_sub(v___x_3750_, v___x_3761_);
v___x_3763_ = lean_array_get(v___x_3729_, v_refArgs_3741_, v___x_3762_);
lean_inc(v___y_3746_);
lean_inc_ref(v___y_3745_);
lean_inc(v___y_3744_);
lean_inc_ref(v___y_3743_);
lean_inc(v___x_3763_);
v___x_3764_ = lean_infer_type(v___x_3763_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref_known(v___x_3764_, 1);
lean_inc(v___y_3746_);
lean_inc_ref(v___y_3745_);
lean_inc(v___y_3744_);
lean_inc_ref(v___y_3743_);
v___x_3766_ = lean_infer_type(v_a_3765_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3768_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___x_3768_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3767_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_a_3769_);
lean_dec_ref_known(v___x_3768_, 1);
if (lean_obj_tag(v_a_3769_) == 1)
{
lean_object* v_val_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___f_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; size_t v_sz_3783_; size_t v___x_3784_; lean_object* v___x_3785_; 
v_val_3770_ = lean_ctor_get(v_a_3769_, 0);
lean_inc(v_val_3770_);
lean_dec_ref_known(v_a_3769_, 1);
lean_inc(v___x_3749_);
lean_inc_ref(v_refArgs_3741_);
v___x_3771_ = l_Array_toSubarray___redArg(v_refArgs_3741_, v___x_3748_, v___x_3749_);
v___x_3772_ = l_Subarray_copy___redArg(v___x_3755_);
lean_inc_ref(v___x_3757_);
lean_inc_ref(v___x_3772_);
lean_inc(v___x_3730_);
v___f_3773_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3773_, 0, v___x_3730_);
lean_closure_set(v___f_3773_, 1, v___x_3772_);
lean_closure_set(v___f_3773_, 2, v___x_3757_);
lean_closure_set(v___f_3773_, 3, v_all_3731_);
lean_closure_set(v___f_3773_, 4, v___x_3732_);
lean_closure_set(v___f_3773_, 5, v___x_3754_);
lean_closure_set(v___f_3773_, 6, v___x_3761_);
v___x_3774_ = lean_array_get_size(v___x_3757_);
v___x_3775_ = l_Array_ofFn___redArg(v___x_3774_, v___f_3773_);
v___x_3776_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3777_ = lean_array_get_size(v___x_3775_);
lean_inc_ref(v___x_3775_);
v___x_3778_ = l_Array_toSubarray___redArg(v___x_3775_, v___x_3754_, v___x_3777_);
v___x_3779_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
lean_ctor_set(v___x_3780_, 1, v___x_3774_);
lean_inc_ref(v___x_3778_);
v___x_3781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3778_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3776_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v_sz_3783_ = lean_array_size(v___x_3757_);
v___x_3784_ = ((size_t)0ULL);
v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3749_, v___x_3750_, v___x_3757_, v_sz_3783_, v___x_3784_, v___x_3782_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v_fst_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___f_3795_; uint8_t v___x_3796_; lean_object* v___x_3797_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v_fst_3787_ = lean_ctor_get(v_a_3786_, 0);
lean_inc(v_fst_3787_);
lean_dec(v_a_3786_);
v___x_3788_ = l_Subarray_copy___redArg(v___x_3771_);
lean_inc(v___x_3749_);
v___x_3789_ = l_Array_toSubarray___redArg(v_refArgs_3741_, v___x_3749_, v___x_3762_);
v___x_3790_ = l_Subarray_copy___redArg(v___x_3789_);
v___x_3791_ = l_Lean_mkLevelMax(v_val_3770_, v_head_3733_);
v___x_3792_ = lean_box_usize(v_sz_3783_);
v___x_3793_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3794_ = lean_box(v___x_3751_);
v___f_3795_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 30, 24);
lean_closure_set(v___f_3795_, 0, v___x_3791_);
lean_closure_set(v___f_3795_, 1, v_tail_3734_);
lean_closure_set(v___f_3795_, 2, v_recName_3735_);
lean_closure_set(v___f_3795_, 3, v___x_3772_);
lean_closure_set(v___f_3795_, 4, v___x_3778_);
lean_closure_set(v___f_3795_, 5, v___x_3749_);
lean_closure_set(v___f_3795_, 6, v___x_3750_);
lean_closure_set(v___f_3795_, 7, v___x_3757_);
lean_closure_set(v___f_3795_, 8, v___x_3792_);
lean_closure_set(v___f_3795_, 9, v___x_3793_);
lean_closure_set(v___f_3795_, 10, v___x_3788_);
lean_closure_set(v___f_3795_, 11, v___x_3775_);
lean_closure_set(v___f_3795_, 12, v___x_3790_);
lean_closure_set(v___f_3795_, 13, v___x_3763_);
lean_closure_set(v___f_3795_, 14, v___x_3761_);
lean_closure_set(v___f_3795_, 15, v___x_3729_);
lean_closure_set(v___f_3795_, 16, v_val_3760_);
lean_closure_set(v___f_3795_, 17, v___x_3794_);
lean_closure_set(v___f_3795_, 18, v_brecOnGoName_3736_);
lean_closure_set(v___f_3795_, 19, v_levelParams_3737_);
lean_closure_set(v___f_3795_, 20, v___x_3730_);
lean_closure_set(v___f_3795_, 21, v_brecOnName_3738_);
lean_closure_set(v___f_3795_, 22, v___x_3754_);
lean_closure_set(v___f_3795_, 23, v_brecOnEqName_3739_);
v___x_3796_ = 0;
v___x_3797_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3787_, v___f_3795_, v___x_3796_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3797_;
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v___x_3778_);
lean_dec_ref(v___x_3775_);
lean_dec_ref(v___x_3772_);
lean_dec_ref(v___x_3771_);
lean_dec(v_val_3770_);
lean_dec(v___x_3763_);
lean_dec(v___x_3762_);
lean_dec(v_val_3760_);
lean_dec_ref(v___x_3757_);
lean_dec(v___x_3749_);
lean_dec_ref(v_refArgs_3741_);
lean_dec(v_brecOnEqName_3739_);
lean_dec(v_brecOnName_3738_);
lean_dec(v_levelParams_3737_);
lean_dec(v_brecOnGoName_3736_);
lean_dec(v_recName_3735_);
lean_dec(v_tail_3734_);
lean_dec(v_head_3733_);
lean_dec(v___x_3730_);
lean_dec_ref(v___x_3729_);
v_a_3798_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3785_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3785_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; 
lean_dec(v_a_3769_);
lean_dec(v___x_3762_);
lean_dec(v_val_3760_);
lean_dec_ref(v___x_3757_);
lean_dec_ref(v___x_3755_);
lean_dec(v___x_3749_);
lean_dec(v___x_3748_);
lean_dec_ref(v_refArgs_3741_);
lean_dec(v_brecOnEqName_3739_);
lean_dec(v_brecOnName_3738_);
lean_dec(v_levelParams_3737_);
lean_dec(v_brecOnGoName_3736_);
lean_dec(v_recName_3735_);
lean_dec(v_tail_3734_);
lean_dec(v_head_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_all_3731_);
lean_dec(v___x_3730_);
lean_dec_ref(v___x_3729_);
v___x_3806_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3807_ = l_Lean_MessageData_ofExpr(v___x_3763_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3810_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3811_;
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec(v___x_3763_);
lean_dec(v___x_3762_);
lean_dec(v_val_3760_);
lean_dec_ref(v___x_3757_);
lean_dec_ref(v___x_3755_);
lean_dec(v___x_3749_);
lean_dec(v___x_3748_);
lean_dec_ref(v_refArgs_3741_);
lean_dec(v_brecOnEqName_3739_);
lean_dec(v_brecOnName_3738_);
lean_dec(v_levelParams_3737_);
lean_dec(v_brecOnGoName_3736_);
lean_dec(v_recName_3735_);
lean_dec(v_tail_3734_);
lean_dec(v_head_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_all_3731_);
lean_dec(v___x_3730_);
lean_dec_ref(v___x_3729_);
v_a_3812_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3768_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3768_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
lean_dec(v___x_3763_);
lean_dec(v___x_3762_);
lean_dec(v_val_3760_);
lean_dec_ref(v___x_3757_);
lean_dec_ref(v___x_3755_);
lean_dec(v___x_3749_);
lean_dec(v___x_3748_);
lean_dec_ref(v_refArgs_3741_);
lean_dec(v_brecOnEqName_3739_);
lean_dec(v_brecOnName_3738_);
lean_dec(v_levelParams_3737_);
lean_dec(v_brecOnGoName_3736_);
lean_dec(v_recName_3735_);
lean_dec(v_tail_3734_);
lean_dec(v_head_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_all_3731_);
lean_dec(v___x_3730_);
lean_dec_ref(v___x_3729_);
v_a_3820_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3766_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3766_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v___x_3763_);
lean_dec(v___x_3762_);
lean_dec(v_val_3760_);
lean_dec_ref(v___x_3757_);
lean_dec_ref(v___x_3755_);
lean_dec(v___x_3749_);
lean_dec(v___x_3748_);
lean_dec_ref(v_refArgs_3741_);
lean_dec(v_brecOnEqName_3739_);
lean_dec(v_brecOnName_3738_);
lean_dec(v_levelParams_3737_);
lean_dec(v_brecOnGoName_3736_);
lean_dec(v_recName_3735_);
lean_dec(v_tail_3734_);
lean_dec(v_head_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_all_3731_);
lean_dec(v___x_3730_);
lean_dec_ref(v___x_3729_);
v_a_3828_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3764_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3764_);
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
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec(v___x_3759_);
lean_dec_ref(v___x_3755_);
lean_dec(v___x_3749_);
lean_dec(v___x_3748_);
lean_dec_ref(v_refArgs_3741_);
lean_dec(v_brecOnEqName_3739_);
lean_dec(v_brecOnName_3738_);
lean_dec(v_levelParams_3737_);
lean_dec(v_brecOnGoName_3736_);
lean_dec(v_recName_3735_);
lean_dec(v_tail_3734_);
lean_dec(v_head_3733_);
lean_dec(v___x_3732_);
lean_dec_ref(v_all_3731_);
lean_dec(v___x_3730_);
lean_dec_ref(v___x_3729_);
v___x_3836_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3837_ = l_Lean_MessageData_ofExpr(v_type_3740_);
v___x_3838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3836_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = lean_array_to_list(v___x_3757_);
v___x_3842_ = lean_box(0);
v___x_3843_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3841_, v___x_3842_);
v___x_3844_ = l_Lean_MessageData_ofList(v___x_3843_);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3840_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3845_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3847_ = _args[0];
lean_object* v_numMotives_3848_ = _args[1];
lean_object* v_numMinors_3849_ = _args[2];
lean_object* v___x_3850_ = _args[3];
lean_object* v___x_3851_ = _args[4];
lean_object* v_all_3852_ = _args[5];
lean_object* v___x_3853_ = _args[6];
lean_object* v_head_3854_ = _args[7];
lean_object* v_tail_3855_ = _args[8];
lean_object* v_recName_3856_ = _args[9];
lean_object* v_brecOnGoName_3857_ = _args[10];
lean_object* v_levelParams_3858_ = _args[11];
lean_object* v_brecOnName_3859_ = _args[12];
lean_object* v_brecOnEqName_3860_ = _args[13];
lean_object* v_type_3861_ = _args[14];
lean_object* v_refArgs_3862_ = _args[15];
lean_object* v_refBody_3863_ = _args[16];
lean_object* v___y_3864_ = _args[17];
lean_object* v___y_3865_ = _args[18];
lean_object* v___y_3866_ = _args[19];
lean_object* v___y_3867_ = _args[20];
lean_object* v___y_3868_ = _args[21];
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3847_, v_numMotives_3848_, v_numMinors_3849_, v___x_3850_, v___x_3851_, v_all_3852_, v___x_3853_, v_head_3854_, v_tail_3855_, v_recName_3856_, v_brecOnGoName_3857_, v_levelParams_3858_, v_brecOnName_3859_, v_brecOnEqName_3860_, v_type_3861_, v_refArgs_3862_, v_refBody_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec_ref(v_refBody_3863_);
lean_dec(v_numMinors_3849_);
lean_dec(v_numMotives_3848_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3872_, lean_object* v_nParams_3873_, lean_object* v_all_3874_, lean_object* v_brecOnName_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
lean_object* v___x_3881_; 
lean_inc(v_recName_3872_);
v___x_3881_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3872_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3884_; uint8_t v_isShared_3885_; uint8_t v_isSharedCheck_3915_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3884_ = v___x_3881_;
v_isShared_3885_ = v_isSharedCheck_3915_;
goto v_resetjp_3883_;
}
else
{
lean_inc(v_a_3882_);
lean_dec(v___x_3881_);
v___x_3884_ = lean_box(0);
v_isShared_3885_ = v_isSharedCheck_3915_;
goto v_resetjp_3883_;
}
v_resetjp_3883_:
{
if (lean_obj_tag(v_a_3882_) == 7)
{
lean_object* v_val_3886_; lean_object* v_toConstantVal_3887_; lean_object* v_numMotives_3888_; lean_object* v_numMinors_3889_; lean_object* v_levelParams_3890_; lean_object* v_type_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_del_object(v___x_3884_);
v_val_3886_ = lean_ctor_get(v_a_3882_, 0);
lean_inc_ref(v_val_3886_);
lean_dec_ref_known(v_a_3882_, 1);
v_toConstantVal_3887_ = lean_ctor_get(v_val_3886_, 0);
lean_inc_ref(v_toConstantVal_3887_);
v_numMotives_3888_ = lean_ctor_get(v_val_3886_, 4);
lean_inc(v_numMotives_3888_);
v_numMinors_3889_ = lean_ctor_get(v_val_3886_, 5);
lean_inc(v_numMinors_3889_);
lean_dec_ref(v_val_3886_);
v_levelParams_3890_ = lean_ctor_get(v_toConstantVal_3887_, 1);
lean_inc_n(v_levelParams_3890_, 2);
v_type_3891_ = lean_ctor_get(v_toConstantVal_3887_, 2);
lean_inc_ref(v_type_3891_);
lean_dec_ref(v_toConstantVal_3887_);
v___x_3892_ = lean_box(0);
v___x_3893_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3890_, v___x_3892_);
if (lean_obj_tag(v___x_3893_) == 1)
{
lean_object* v_head_3894_; lean_object* v_tail_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v_brecOnGoName_3899_; lean_object* v___x_3900_; lean_object* v_brecOnEqName_3901_; lean_object* v___f_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; 
v_head_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_head_3894_);
v_tail_3895_ = lean_ctor_get(v___x_3893_, 1);
lean_inc(v_tail_3895_);
v___x_3896_ = l_Lean_instInhabitedExpr;
v___x_3897_ = lean_box(0);
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3875_, 2);
v_brecOnGoName_3899_ = l_Lean_Name_str___override(v_brecOnName_3875_, v___x_3898_);
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3901_ = l_Lean_Name_str___override(v_brecOnName_3875_, v___x_3900_);
lean_inc_ref(v_type_3891_);
v___f_3902_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 22, 15);
lean_closure_set(v___f_3902_, 0, v_nParams_3873_);
lean_closure_set(v___f_3902_, 1, v_numMotives_3888_);
lean_closure_set(v___f_3902_, 2, v_numMinors_3889_);
lean_closure_set(v___f_3902_, 3, v___x_3896_);
lean_closure_set(v___f_3902_, 4, v___x_3893_);
lean_closure_set(v___f_3902_, 5, v_all_3874_);
lean_closure_set(v___f_3902_, 6, v___x_3897_);
lean_closure_set(v___f_3902_, 7, v_head_3894_);
lean_closure_set(v___f_3902_, 8, v_tail_3895_);
lean_closure_set(v___f_3902_, 9, v_recName_3872_);
lean_closure_set(v___f_3902_, 10, v_brecOnGoName_3899_);
lean_closure_set(v___f_3902_, 11, v_levelParams_3890_);
lean_closure_set(v___f_3902_, 12, v_brecOnName_3875_);
lean_closure_set(v___f_3902_, 13, v_brecOnEqName_3901_);
lean_closure_set(v___f_3902_, 14, v_type_3891_);
v___x_3903_ = 0;
v___x_3904_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3891_, v___f_3902_, v___x_3903_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec(v___x_3893_);
lean_dec_ref(v_type_3891_);
lean_dec(v_levelParams_3890_);
lean_dec(v_numMinors_3889_);
lean_dec(v_numMotives_3888_);
lean_dec(v_brecOnName_3875_);
lean_dec_ref(v_all_3874_);
lean_dec(v_nParams_3873_);
v___x_3905_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3906_ = l_Lean_MessageData_ofName(v_recName_3872_);
v___x_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3905_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
v___x_3908_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3907_);
lean_ctor_set(v___x_3909_, 1, v___x_3908_);
v___x_3910_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3909_, v_a_3876_, v_a_3877_, v_a_3878_, v_a_3879_);
return v___x_3910_;
}
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec(v_a_3882_);
lean_dec(v_brecOnName_3875_);
lean_dec_ref(v_all_3874_);
lean_dec(v_nParams_3873_);
lean_dec(v_recName_3872_);
v___x_3911_ = lean_box(0);
if (v_isShared_3885_ == 0)
{
lean_ctor_set(v___x_3884_, 0, v___x_3911_);
v___x_3913_ = v___x_3884_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec(v_brecOnName_3875_);
lean_dec_ref(v_all_3874_);
lean_dec(v_nParams_3873_);
lean_dec(v_recName_3872_);
v_a_3916_ = lean_ctor_get(v___x_3881_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3881_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3881_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3881_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3924_, lean_object* v_nParams_3925_, lean_object* v_all_3926_, lean_object* v_brecOnName_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3924_, v_nParams_3925_, v_all_3926_, v_brecOnName_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
return v_res_3933_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3934_, lean_object* v___x_3935_, lean_object* v___x_3936_, lean_object* v___x_3937_, lean_object* v___x_3938_, lean_object* v_a_3939_, lean_object* v_b_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_nat_dec_lt(v_a_3939_, v_upperBound_3934_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
lean_dec(v_a_3939_);
lean_dec_ref(v___x_3938_);
lean_dec(v___x_3937_);
lean_dec(v___x_3936_);
lean_dec(v___x_3935_);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v_b_3940_);
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3948_ = lean_unsigned_to_nat(1u);
v___x_3949_ = lean_nat_add(v_a_3939_, v___x_3948_);
lean_dec(v_a_3939_);
lean_inc_n(v___x_3949_, 2);
lean_inc(v___x_3935_);
v___x_3950_ = lean_name_append_index_after(v___x_3935_, v___x_3949_);
lean_inc(v___x_3936_);
v___x_3951_ = lean_name_append_index_after(v___x_3936_, v___x_3949_);
lean_inc_ref(v___x_3938_);
lean_inc(v___x_3937_);
v___x_3952_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3950_, v___x_3937_, v___x_3938_, v___x_3951_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref_known(v___x_3952_, 1);
v___x_3953_ = lean_box(0);
v_a_3939_ = v___x_3949_;
v_b_3940_ = v___x_3953_;
goto _start;
}
else
{
lean_dec(v___x_3949_);
lean_dec_ref(v___x_3938_);
lean_dec(v___x_3937_);
lean_dec(v___x_3936_);
lean_dec(v___x_3935_);
return v___x_3952_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3955_, lean_object* v___x_3956_, lean_object* v___x_3957_, lean_object* v___x_3958_, lean_object* v___x_3959_, lean_object* v_a_3960_, lean_object* v_b_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3955_, v___x_3956_, v___x_3957_, v___x_3958_, v___x_3959_, v_a_3960_, v_b_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec(v___y_3963_);
lean_dec_ref(v___y_3962_);
lean_dec(v_upperBound_3955_);
return v_res_3967_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3972_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3973_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3974_ = l_Lean_Name_append(v___x_3973_, v___x_3972_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v_toCold_3981_; lean_object* v_options_3982_; lean_object* v_inheritedTraceOptions_3983_; uint8_t v_hasTrace_3984_; lean_object* v___x_3985_; 
v_toCold_3981_ = lean_ctor_get(v_a_3978_, 0);
v_options_3982_ = lean_ctor_get(v_toCold_3981_, 2);
v_inheritedTraceOptions_3983_ = lean_ctor_get(v_toCold_3981_, 11);
v_hasTrace_3984_ = lean_ctor_get_uint8(v_options_3982_, sizeof(void*)*1);
v___x_3985_ = lean_box(0);
if (v_hasTrace_3984_ == 0)
{
lean_object* v___x_3986_; 
lean_inc(v_indName_3975_);
v___x_3986_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_4051_; 
v_a_3987_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_3989_ = v___x_3986_;
v_isShared_3990_ = v_isSharedCheck_4051_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3986_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_4051_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
if (lean_obj_tag(v_a_3987_) == 5)
{
lean_object* v_val_3991_; uint8_t v_isRec_3992_; 
v_val_3991_ = lean_ctor_get(v_a_3987_, 0);
lean_inc_ref(v_val_3991_);
lean_dec_ref_known(v_a_3987_, 1);
v_isRec_3992_ = lean_ctor_get_uint8(v_val_3991_, sizeof(void*)*6);
if (v_isRec_3992_ == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
lean_dec_ref(v_val_3991_);
lean_dec(v_indName_3975_);
v___x_3993_ = lean_box(0);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v___x_3993_);
v___x_3995_ = v___x_3989_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
else
{
lean_object* v_toConstantVal_3997_; lean_object* v_numParams_3998_; lean_object* v_all_3999_; lean_object* v_numNested_4000_; lean_object* v_type_4001_; lean_object* v___x_4002_; 
lean_del_object(v___x_3989_);
v_toConstantVal_3997_ = lean_ctor_get(v_val_3991_, 0);
lean_inc_ref(v_toConstantVal_3997_);
v_numParams_3998_ = lean_ctor_get(v_val_3991_, 1);
lean_inc(v_numParams_3998_);
v_all_3999_ = lean_ctor_get(v_val_3991_, 3);
lean_inc(v_all_3999_);
v_numNested_4000_ = lean_ctor_get(v_val_3991_, 5);
lean_inc(v_numNested_4000_);
lean_dec_ref(v_val_3991_);
v_type_4001_ = lean_ctor_get(v_toConstantVal_3997_, 2);
lean_inc_ref(v_type_4001_);
lean_dec_ref(v_toConstantVal_3997_);
v___x_4002_ = l_Lean_Meta_isPropFormerType(v_type_4001_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4038_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4005_ = v___x_4002_;
v_isShared_4006_ = v_isSharedCheck_4038_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_4002_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4038_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_unbox(v_a_4003_);
lean_dec(v_a_4003_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
lean_del_object(v___x_4005_);
lean_inc_n(v_indName_3975_, 2);
v___x_4008_ = l_Lean_mkRecName(v_indName_3975_);
v___x_4009_ = l_Lean_mkBRecOnName(v_indName_3975_);
lean_inc(v_all_3999_);
v___x_4010_ = lean_array_mk(v_all_3999_);
lean_inc(v___x_4009_);
lean_inc_ref(v___x_4010_);
lean_inc(v_numParams_3998_);
lean_inc(v___x_4008_);
v___x_4011_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4008_, v_numParams_3998_, v___x_4010_, v___x_4009_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4032_; 
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4032_ == 0)
{
lean_object* v_unused_4033_; 
v_unused_4033_ = lean_ctor_get(v___x_4011_, 0);
lean_dec(v_unused_4033_);
v___x_4013_ = v___x_4011_;
v_isShared_4014_ = v_isSharedCheck_4032_;
goto v_resetjp_4012_;
}
else
{
lean_dec(v___x_4011_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4032_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4015_ = lean_unsigned_to_nat(0u);
v___x_4016_ = l_List_get_x21Internal___redArg(v___x_3985_, v_all_3999_, v___x_4015_);
lean_dec(v_all_3999_);
v___x_4017_ = lean_name_eq(v___x_4016_, v_indName_3975_);
lean_dec(v_indName_3975_);
lean_dec(v___x_4016_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; lean_object* v___x_4020_; 
lean_dec_ref(v___x_4010_);
lean_dec(v___x_4009_);
lean_dec(v___x_4008_);
lean_dec(v_numNested_4000_);
lean_dec(v_numParams_3998_);
v___x_4018_ = lean_box(0);
if (v_isShared_4014_ == 0)
{
lean_ctor_set(v___x_4013_, 0, v___x_4018_);
v___x_4020_ = v___x_4013_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v___x_4018_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_del_object(v___x_4013_);
v___x_4022_ = lean_box(0);
v___x_4023_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4000_, v___x_4008_, v___x_4009_, v_numParams_3998_, v___x_4010_, v___x_4015_, v___x_4022_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_numNested_4000_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4030_ == 0)
{
lean_object* v_unused_4031_; 
v_unused_4031_ = lean_ctor_get(v___x_4023_, 0);
lean_dec(v_unused_4031_);
v___x_4025_ = v___x_4023_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_dec(v___x_4023_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
lean_ctor_set(v___x_4025_, 0, v___x_4022_);
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v___x_4022_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
else
{
return v___x_4023_;
}
}
}
}
else
{
lean_dec_ref(v___x_4010_);
lean_dec(v___x_4009_);
lean_dec(v___x_4008_);
lean_dec(v_numNested_4000_);
lean_dec(v_all_3999_);
lean_dec(v_numParams_3998_);
lean_dec(v_indName_3975_);
return v___x_4011_;
}
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4036_; 
lean_dec(v_numNested_4000_);
lean_dec(v_all_3999_);
lean_dec(v_numParams_3998_);
lean_dec(v_indName_3975_);
v___x_4034_ = lean_box(0);
if (v_isShared_4006_ == 0)
{
lean_ctor_set(v___x_4005_, 0, v___x_4034_);
v___x_4036_ = v___x_4005_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4034_);
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
else
{
lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_numNested_4000_);
lean_dec(v_all_3999_);
lean_dec(v_numParams_3998_);
lean_dec(v_indName_3975_);
v_a_4039_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4002_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_dec(v___x_4002_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
else
{
lean_object* v___x_4047_; lean_object* v___x_4049_; 
lean_dec(v_a_3987_);
lean_dec(v_indName_3975_);
v___x_4047_ = lean_box(0);
if (v_isShared_3990_ == 0)
{
lean_ctor_set(v___x_3989_, 0, v___x_4047_);
v___x_4049_ = v___x_3989_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v___x_4047_);
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
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_dec(v_indName_3975_);
v_a_4052_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_3986_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_3986_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_object* v___f_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v_a_4068_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v_a_4083_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v_a_4088_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v_a_4093_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v_a_4105_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v_a_4110_; 
lean_inc(v_indName_3975_);
v___f_4060_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4060_, 0, v_indName_3975_);
v___x_4061_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4062_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4063_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4064_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3983_, v_options_3982_, v___x_4063_);
if (v___x_4064_ == 0)
{
lean_object* v___x_4179_; uint8_t v___x_4180_; 
v___x_4179_ = l_Lean_trace_profiler;
v___x_4180_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3982_, v___x_4179_);
if (v___x_4180_ == 0)
{
lean_object* v___x_4181_; 
lean_dec_ref(v___f_4060_);
lean_inc(v_indName_3975_);
v___x_4181_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
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
lean_dec(v_indName_3975_);
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
v___x_4197_ = l_Lean_Meta_isPropFormerType(v_type_4196_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
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
lean_inc_n(v_indName_3975_, 2);
v___x_4203_ = l_Lean_mkRecName(v_indName_3975_);
v___x_4204_ = l_Lean_mkBRecOnName(v_indName_3975_);
lean_inc(v_all_4194_);
v___x_4205_ = lean_array_mk(v_all_4194_);
lean_inc(v___x_4204_);
lean_inc_ref(v___x_4205_);
lean_inc(v_numParams_4193_);
lean_inc(v___x_4203_);
v___x_4206_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4203_, v_numParams_4193_, v___x_4205_, v___x_4204_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
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
v___x_4211_ = l_List_get_x21Internal___redArg(v___x_3985_, v_all_4194_, v___x_4210_);
lean_dec(v_all_4194_);
v___x_4212_ = lean_name_eq(v___x_4211_, v_indName_3975_);
lean_dec(v_indName_3975_);
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
v___x_4218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4195_, v___x_4203_, v___x_4204_, v_numParams_4193_, v___x_4205_, v___x_4210_, v___x_4217_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
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
lean_dec(v_indName_3975_);
return v___x_4206_;
}
}
else
{
lean_object* v___x_4229_; lean_object* v___x_4231_; 
lean_dec(v_numNested_4195_);
lean_dec(v_all_4194_);
lean_dec(v_numParams_4193_);
lean_dec(v_indName_3975_);
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
lean_dec(v_indName_3975_);
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
lean_dec(v_indName_3975_);
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
lean_dec(v_indName_3975_);
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
goto v___jp_4112_;
}
}
else
{
goto v___jp_4112_;
}
v___jp_4065_:
{
lean_object* v___x_4069_; double v___x_4070_; double v___x_4071_; double v___x_4072_; double v___x_4073_; double v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4069_ = lean_io_mono_nanos_now();
v___x_4070_ = lean_float_of_nat(v___y_4066_);
v___x_4071_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4072_ = lean_float_div(v___x_4070_, v___x_4071_);
v___x_4073_ = lean_float_of_nat(v___x_4069_);
v___x_4074_ = lean_float_div(v___x_4073_, v___x_4071_);
v___x_4075_ = lean_box_float(v___x_4072_);
v___x_4076_ = lean_box_float(v___x_4074_);
v___x_4077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4075_);
lean_ctor_set(v___x_4077_, 1, v___x_4076_);
v___x_4078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4078_, 0, v_a_4068_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4061_, v_hasTrace_3984_, v___x_4062_, v_options_3982_, v___x_4064_, v___y_4067_, v___f_4060_, v___x_4078_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
return v___x_4079_;
}
v___jp_4080_:
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4084_, 0, v_a_4083_);
v___y_4066_ = v___y_4081_;
v___y_4067_ = v___y_4082_;
v_a_4068_ = v___x_4084_;
goto v___jp_4065_;
}
v___jp_4085_:
{
lean_object* v___x_4089_; 
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v_a_4088_);
v___y_4066_ = v___y_4086_;
v___y_4067_ = v___y_4087_;
v_a_4068_ = v___x_4089_;
goto v___jp_4065_;
}
v___jp_4090_:
{
lean_object* v___x_4094_; double v___x_4095_; double v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4094_ = lean_io_get_num_heartbeats();
v___x_4095_ = lean_float_of_nat(v___y_4092_);
v___x_4096_ = lean_float_of_nat(v___x_4094_);
v___x_4097_ = lean_box_float(v___x_4095_);
v___x_4098_ = lean_box_float(v___x_4096_);
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4097_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v_a_4093_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4061_, v_hasTrace_3984_, v___x_4062_, v_options_3982_, v___x_4064_, v___y_4091_, v___f_4060_, v___x_4100_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
return v___x_4101_;
}
v___jp_4102_:
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_a_4105_);
v___y_4091_ = v___y_4103_;
v___y_4092_ = v___y_4104_;
v_a_4093_ = v___x_4106_;
goto v___jp_4090_;
}
v___jp_4107_:
{
lean_object* v___x_4111_; 
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v_a_4110_);
v___y_4091_ = v___y_4108_;
v___y_4092_ = v___y_4109_;
v_a_4093_ = v___x_4111_;
goto v___jp_4090_;
}
v___jp_4112_:
{
lean_object* v___x_4113_; lean_object* v_a_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; 
v___x_4113_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_3979_);
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref(v___x_4113_);
v___x_4115_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4116_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_3982_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3975_);
v___x_4118_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
if (lean_obj_tag(v_a_4119_) == 5)
{
lean_object* v_val_4120_; uint8_t v_isRec_4121_; 
v_val_4120_ = lean_ctor_get(v_a_4119_, 0);
lean_inc_ref(v_val_4120_);
lean_dec_ref_known(v_a_4119_, 1);
v_isRec_4121_ = lean_ctor_get_uint8(v_val_4120_, sizeof(void*)*6);
if (v_isRec_4121_ == 0)
{
lean_object* v___x_4122_; 
lean_dec_ref(v_val_4120_);
lean_dec(v_indName_3975_);
v___x_4122_ = lean_box(0);
v___y_4081_ = v___x_4117_;
v___y_4082_ = v_a_4114_;
v_a_4083_ = v___x_4122_;
goto v___jp_4080_;
}
else
{
lean_object* v_toConstantVal_4123_; lean_object* v_numParams_4124_; lean_object* v_all_4125_; lean_object* v_numNested_4126_; lean_object* v_type_4127_; lean_object* v___x_4128_; 
v_toConstantVal_4123_ = lean_ctor_get(v_val_4120_, 0);
lean_inc_ref(v_toConstantVal_4123_);
v_numParams_4124_ = lean_ctor_get(v_val_4120_, 1);
lean_inc(v_numParams_4124_);
v_all_4125_ = lean_ctor_get(v_val_4120_, 3);
lean_inc(v_all_4125_);
v_numNested_4126_ = lean_ctor_get(v_val_4120_, 5);
lean_inc(v_numNested_4126_);
lean_dec_ref(v_val_4120_);
v_type_4127_ = lean_ctor_get(v_toConstantVal_4123_, 2);
lean_inc_ref(v_type_4127_);
lean_dec_ref(v_toConstantVal_4123_);
v___x_4128_ = l_Lean_Meta_isPropFormerType(v_type_4127_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; uint8_t v___x_4130_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref_known(v___x_4128_, 1);
v___x_4130_ = lean_unbox(v_a_4129_);
lean_dec(v_a_4129_);
if (v___x_4130_ == 0)
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
lean_inc_n(v_indName_3975_, 2);
v___x_4131_ = l_Lean_mkRecName(v_indName_3975_);
v___x_4132_ = l_Lean_mkBRecOnName(v_indName_3975_);
lean_inc(v_all_4125_);
v___x_4133_ = lean_array_mk(v_all_4125_);
lean_inc(v___x_4132_);
lean_inc_ref(v___x_4133_);
lean_inc(v_numParams_4124_);
lean_inc(v___x_4131_);
v___x_4134_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4131_, v_numParams_4124_, v___x_4133_, v___x_4132_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; uint8_t v___x_4137_; 
lean_dec_ref_known(v___x_4134_, 1);
v___x_4135_ = lean_unsigned_to_nat(0u);
v___x_4136_ = l_List_get_x21Internal___redArg(v___x_3985_, v_all_4125_, v___x_4135_);
lean_dec(v_all_4125_);
v___x_4137_ = lean_name_eq(v___x_4136_, v_indName_3975_);
lean_dec(v_indName_3975_);
lean_dec(v___x_4136_);
if (v___x_4137_ == 0)
{
lean_object* v___x_4138_; 
lean_dec_ref(v___x_4133_);
lean_dec(v___x_4132_);
lean_dec(v___x_4131_);
lean_dec(v_numNested_4126_);
lean_dec(v_numParams_4124_);
v___x_4138_ = lean_box(0);
v___y_4081_ = v___x_4117_;
v___y_4082_ = v_a_4114_;
v_a_4083_ = v___x_4138_;
goto v___jp_4080_;
}
else
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = lean_box(0);
v___x_4140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4126_, v___x_4131_, v___x_4132_, v_numParams_4124_, v___x_4133_, v___x_4135_, v___x_4139_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_numNested_4126_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_dec_ref_known(v___x_4140_, 1);
v___y_4081_ = v___x_4117_;
v___y_4082_ = v_a_4114_;
v_a_4083_ = v___x_4139_;
goto v___jp_4080_;
}
else
{
lean_object* v_a_4141_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___y_4086_ = v___x_4117_;
v___y_4087_ = v_a_4114_;
v_a_4088_ = v_a_4141_;
goto v___jp_4085_;
}
}
}
else
{
lean_dec_ref(v___x_4133_);
lean_dec(v___x_4132_);
lean_dec(v___x_4131_);
lean_dec(v_numNested_4126_);
lean_dec(v_all_4125_);
lean_dec(v_numParams_4124_);
lean_dec(v_indName_3975_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4142_; 
v_a_4142_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4134_, 1);
v___y_4081_ = v___x_4117_;
v___y_4082_ = v_a_4114_;
v_a_4083_ = v_a_4142_;
goto v___jp_4080_;
}
else
{
lean_object* v_a_4143_; 
v_a_4143_ = lean_ctor_get(v___x_4134_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4134_, 1);
v___y_4086_ = v___x_4117_;
v___y_4087_ = v_a_4114_;
v_a_4088_ = v_a_4143_;
goto v___jp_4085_;
}
}
}
else
{
lean_object* v___x_4144_; 
lean_dec(v_numNested_4126_);
lean_dec(v_all_4125_);
lean_dec(v_numParams_4124_);
lean_dec(v_indName_3975_);
v___x_4144_ = lean_box(0);
v___y_4081_ = v___x_4117_;
v___y_4082_ = v_a_4114_;
v_a_4083_ = v___x_4144_;
goto v___jp_4080_;
}
}
else
{
lean_object* v_a_4145_; 
lean_dec(v_numNested_4126_);
lean_dec(v_all_4125_);
lean_dec(v_numParams_4124_);
lean_dec(v_indName_3975_);
v_a_4145_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4128_, 1);
v___y_4086_ = v___x_4117_;
v___y_4087_ = v_a_4114_;
v_a_4088_ = v_a_4145_;
goto v___jp_4085_;
}
}
}
else
{
lean_object* v___x_4146_; 
lean_dec(v_a_4119_);
lean_dec(v_indName_3975_);
v___x_4146_ = lean_box(0);
v___y_4081_ = v___x_4117_;
v___y_4082_ = v_a_4114_;
v_a_4083_ = v___x_4146_;
goto v___jp_4080_;
}
}
else
{
lean_object* v_a_4147_; 
lean_dec(v_indName_3975_);
v_a_4147_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4147_);
lean_dec_ref_known(v___x_4118_, 1);
v___y_4086_ = v___x_4117_;
v___y_4087_ = v_a_4114_;
v_a_4088_ = v_a_4147_;
goto v___jp_4085_;
}
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3975_);
v___x_4149_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref_known(v___x_4149_, 1);
if (lean_obj_tag(v_a_4150_) == 5)
{
lean_object* v_val_4151_; uint8_t v_isRec_4152_; 
v_val_4151_ = lean_ctor_get(v_a_4150_, 0);
lean_inc_ref(v_val_4151_);
lean_dec_ref_known(v_a_4150_, 1);
v_isRec_4152_ = lean_ctor_get_uint8(v_val_4151_, sizeof(void*)*6);
if (v_isRec_4152_ == 0)
{
lean_object* v___x_4153_; 
lean_dec_ref(v_val_4151_);
lean_dec(v_indName_3975_);
v___x_4153_ = lean_box(0);
v___y_4103_ = v_a_4114_;
v___y_4104_ = v___x_4148_;
v_a_4105_ = v___x_4153_;
goto v___jp_4102_;
}
else
{
lean_object* v_toConstantVal_4154_; lean_object* v_numParams_4155_; lean_object* v_all_4156_; lean_object* v_numNested_4157_; lean_object* v_type_4158_; lean_object* v___x_4159_; 
v_toConstantVal_4154_ = lean_ctor_get(v_val_4151_, 0);
lean_inc_ref(v_toConstantVal_4154_);
v_numParams_4155_ = lean_ctor_get(v_val_4151_, 1);
lean_inc(v_numParams_4155_);
v_all_4156_ = lean_ctor_get(v_val_4151_, 3);
lean_inc(v_all_4156_);
v_numNested_4157_ = lean_ctor_get(v_val_4151_, 5);
lean_inc(v_numNested_4157_);
lean_dec_ref(v_val_4151_);
v_type_4158_ = lean_ctor_get(v_toConstantVal_4154_, 2);
lean_inc_ref(v_type_4158_);
lean_dec_ref(v_toConstantVal_4154_);
v___x_4159_ = l_Lean_Meta_isPropFormerType(v_type_4158_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; uint8_t v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = lean_unbox(v_a_4160_);
lean_dec(v_a_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_inc_n(v_indName_3975_, 2);
v___x_4162_ = l_Lean_mkRecName(v_indName_3975_);
v___x_4163_ = l_Lean_mkBRecOnName(v_indName_3975_);
lean_inc(v_all_4156_);
v___x_4164_ = lean_array_mk(v_all_4156_);
lean_inc(v___x_4163_);
lean_inc_ref(v___x_4164_);
lean_inc(v_numParams_4155_);
lean_inc(v___x_4162_);
v___x_4165_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4162_, v_numParams_4155_, v___x_4164_, v___x_4163_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; 
lean_dec_ref_known(v___x_4165_, 1);
v___x_4166_ = lean_unsigned_to_nat(0u);
v___x_4167_ = l_List_get_x21Internal___redArg(v___x_3985_, v_all_4156_, v___x_4166_);
lean_dec(v_all_4156_);
v___x_4168_ = lean_name_eq(v___x_4167_, v_indName_3975_);
lean_dec(v_indName_3975_);
lean_dec(v___x_4167_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4169_; 
lean_dec_ref(v___x_4164_);
lean_dec(v___x_4163_);
lean_dec(v___x_4162_);
lean_dec(v_numNested_4157_);
lean_dec(v_numParams_4155_);
v___x_4169_ = lean_box(0);
v___y_4103_ = v_a_4114_;
v___y_4104_ = v___x_4148_;
v_a_4105_ = v___x_4169_;
goto v___jp_4102_;
}
else
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = lean_box(0);
v___x_4171_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4157_, v___x_4162_, v___x_4163_, v_numParams_4155_, v___x_4164_, v___x_4166_, v___x_4170_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
lean_dec(v_numNested_4157_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_dec_ref_known(v___x_4171_, 1);
v___y_4103_ = v_a_4114_;
v___y_4104_ = v___x_4148_;
v_a_4105_ = v___x_4170_;
goto v___jp_4102_;
}
else
{
lean_object* v_a_4172_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
v___y_4108_ = v_a_4114_;
v___y_4109_ = v___x_4148_;
v_a_4110_ = v_a_4172_;
goto v___jp_4107_;
}
}
}
else
{
lean_dec_ref(v___x_4164_);
lean_dec(v___x_4163_);
lean_dec(v___x_4162_);
lean_dec(v_numNested_4157_);
lean_dec(v_all_4156_);
lean_dec(v_numParams_4155_);
lean_dec(v_indName_3975_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4173_; 
v_a_4173_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4173_);
lean_dec_ref_known(v___x_4165_, 1);
v___y_4103_ = v_a_4114_;
v___y_4104_ = v___x_4148_;
v_a_4105_ = v_a_4173_;
goto v___jp_4102_;
}
else
{
lean_object* v_a_4174_; 
v_a_4174_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4165_, 1);
v___y_4108_ = v_a_4114_;
v___y_4109_ = v___x_4148_;
v_a_4110_ = v_a_4174_;
goto v___jp_4107_;
}
}
}
else
{
lean_object* v___x_4175_; 
lean_dec(v_numNested_4157_);
lean_dec(v_all_4156_);
lean_dec(v_numParams_4155_);
lean_dec(v_indName_3975_);
v___x_4175_ = lean_box(0);
v___y_4103_ = v_a_4114_;
v___y_4104_ = v___x_4148_;
v_a_4105_ = v___x_4175_;
goto v___jp_4102_;
}
}
else
{
lean_object* v_a_4176_; 
lean_dec(v_numNested_4157_);
lean_dec(v_all_4156_);
lean_dec(v_numParams_4155_);
lean_dec(v_indName_3975_);
v_a_4176_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4159_, 1);
v___y_4108_ = v_a_4114_;
v___y_4109_ = v___x_4148_;
v_a_4110_ = v_a_4176_;
goto v___jp_4107_;
}
}
}
else
{
lean_object* v___x_4177_; 
lean_dec(v_a_4150_);
lean_dec(v_indName_3975_);
v___x_4177_ = lean_box(0);
v___y_4103_ = v_a_4114_;
v___y_4104_ = v___x_4148_;
v_a_4105_ = v___x_4177_;
goto v___jp_4102_;
}
}
else
{
lean_object* v_a_4178_; 
lean_dec(v_indName_3975_);
v_a_4178_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4178_);
lean_dec_ref_known(v___x_4149_, 1);
v___y_4108_ = v_a_4114_;
v___y_4109_ = v___x_4148_;
v_a_4110_ = v_a_4178_;
goto v___jp_4107_;
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
