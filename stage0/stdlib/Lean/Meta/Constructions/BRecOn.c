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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
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
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
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
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkBelow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_mkBelow___closed__0 = (const lean_object*)&l_Lean_mkBelow___closed__0_value;
static const lean_string_object l_Lean_mkBelow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mkBelow"};
static const lean_object* l_Lean_mkBelow___closed__1 = (const lean_object*)&l_Lean_mkBelow___closed__1_value;
static const lean_ctor_object l_Lean_mkBelow___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkBelow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_mkBelow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkBelow___closed__2_value_aux_0),((lean_object*)&l_Lean_mkBelow___closed__1_value),LEAN_SCALAR_PTR_LITERAL(219, 145, 247, 215, 113, 151, 53, 217)}};
static const lean_object* l_Lean_mkBelow___closed__2 = (const lean_object*)&l_Lean_mkBelow___closed__2_value;
static const lean_string_object l_Lean_mkBelow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_mkBelow___closed__3 = (const lean_object*)&l_Lean_mkBelow___closed__3_value;
static lean_once_cell_t l_Lean_mkBelow___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_mkBelow___closed__4;
static const lean_string_object l_Lean_mkBelow___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_mkBelow___closed__5 = (const lean_object*)&l_Lean_mkBelow___closed__5_value;
static const lean_ctor_object l_Lean_mkBelow___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkBelow___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_mkBelow___closed__6 = (const lean_object*)&l_Lean_mkBelow___closed__6_value;
static lean_once_cell_t l_Lean_mkBelow___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkBelow___closed__7;
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_9179__boxed_555_; lean_object* v_res_556_; 
v___x_9179__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9179__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
lean_object* v___x_967_; lean_object* v_env_968_; uint8_t v___y_970_; uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___x_967_ = lean_st_ref_get(v___y_965_);
v_env_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_967_);
v___x_1026_ = l_Lean_Name_isAnonymous(v_declHint_964_);
v___x_1027_ = lean_bool_not(v___x_1026_);
if (v___x_1027_ == 0)
{
v___y_970_ = v___x_1027_;
goto v___jp_969_;
}
else
{
uint8_t v_isExporting_1028_; 
v_isExporting_1028_ = lean_ctor_get_uint8(v_env_968_, sizeof(void*)*8);
v___y_970_ = v_isExporting_1028_;
goto v___jp_969_;
}
v___jp_969_:
{
if (v___y_970_ == 0)
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
uint8_t v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = 0;
lean_inc_ref(v_env_968_);
v___x_973_ = l_Lean_Environment_setExporting(v_env_968_, v___x_972_);
lean_inc(v_declHint_964_);
lean_inc_ref(v___x_973_);
v___x_974_ = l_Lean_Environment_contains(v___x_973_, v_declHint_964_, v___y_970_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v___x_973_);
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_964_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_msg_963_);
return v___x_975_;
}
else
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v_c_981_; lean_object* v___x_982_; 
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2);
v___x_977_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5);
v___x_978_ = l_Lean_Options_empty;
v___x_979_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_979_, 0, v___x_973_);
lean_ctor_set(v___x_979_, 1, v___x_976_);
lean_ctor_set(v___x_979_, 2, v___x_977_);
lean_ctor_set(v___x_979_, 3, v___x_978_);
lean_inc(v_declHint_964_);
v___x_980_ = l_Lean_MessageData_ofConstName(v_declHint_964_, v___x_972_);
v_c_981_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_981_, 0, v___x_979_);
lean_ctor_set(v_c_981_, 1, v___x_980_);
v___x_982_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_968_, v_declHint_964_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref(v_env_968_);
lean_dec(v_declHint_964_);
v___x_983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_c_981_);
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9);
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
lean_object* v_val_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1025_; 
v_val_990_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_992_ = v___x_982_;
v_isShared_993_ = v_isSharedCheck_1025_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_val_990_);
lean_dec(v___x_982_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1025_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_mod_997_; uint8_t v___x_998_; 
v___x_994_ = lean_box(0);
v___x_995_ = l_Lean_Environment_header(v_env_968_);
lean_dec_ref(v_env_968_);
v___x_996_ = l_Lean_EnvironmentHeader_moduleNames(v___x_995_);
v_mod_997_ = lean_array_get(v___x_994_, v___x_996_, v_val_990_);
lean_dec(v_val_990_);
lean_dec_ref(v___x_996_);
v___x_998_ = l_Lean_isPrivateName(v_declHint_964_);
lean_dec(v_declHint_964_);
if (v___x_998_ == 0)
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_999_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_999_);
lean_ctor_set(v___x_1000_, 1, v_c_981_);
v___x_1001_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13);
v___x_1002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
v___x_1003_ = l_Lean_MessageData_ofName(v_mod_997_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = l_Lean_MessageData_note(v___x_1006_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v_msg_963_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 0, v___x_1008_);
v___x_1010_ = v___x_992_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7);
v___x_1013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
lean_ctor_set(v___x_1013_, 1, v_c_981_);
v___x_1014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17);
v___x_1015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1013_);
lean_ctor_set(v___x_1015_, 1, v___x_1014_);
v___x_1016_ = l_Lean_MessageData_ofName(v_mod_997_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19);
v___x_1019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
lean_ctor_set(v___x_1019_, 1, v___x_1018_);
v___x_1020_ = l_Lean_MessageData_note(v___x_1019_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_msg_963_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
if (v_isShared_993_ == 0)
{
lean_ctor_set_tag(v___x_992_, 0);
lean_ctor_set(v___x_992_, 0, v___x_1021_);
v___x_1023_ = v___x_992_;
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1029_, lean_object* v_declHint_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1029_, v_declHint_1030_, v___y_1031_);
lean_dec(v___y_1031_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1034_, lean_object* v_declHint_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v___x_1041_; lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v___x_1041_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1034_, v_declHint_1035_, v___y_1039_);
v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1041_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1044_ = v___x_1041_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_1041_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v___x_1046_ = l_Lean_unknownIdentifierMessageTag;
v___x_1047_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_a_1042_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 0, v___x_1047_);
v___x_1049_ = v___x_1044_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1052_, lean_object* v_declHint_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1052_, v_declHint_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1060_, lean_object* v_msg_1061_, lean_object* v_declHint_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v_a_1069_; lean_object* v___x_1070_; 
v___x_1068_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1061_, v_declHint_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1060_, v_a_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1071_, lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1071_, v_msg_1072_, v_declHint_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v_ref_1071_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1086_, lean_object* v_constName_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1093_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1094_ = 0;
lean_inc(v_constName_1087_);
v___x_1095_ = l_Lean_MessageData_ofConstName(v_constName_1087_, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1093_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1086_, v___x_1098_, v_constName_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1100_, lean_object* v_constName_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1100_, v_constName_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v_ref_1100_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_ref_1114_; lean_object* v___x_1115_; 
v_ref_1114_ = lean_ctor_get(v___y_1111_, 5);
v___x_1115_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1114_, v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v_env_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = lean_st_ref_get(v___y_1127_);
v_env_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc_ref(v_env_1130_);
lean_dec(v___x_1129_);
v___x_1131_ = 0;
lean_inc(v_constName_1123_);
v___x_1132_ = l_Lean_Environment_find_x3f(v_env_1130_, v_constName_1123_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1133_;
}
else
{
lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_constName_1123_);
v_val_1134_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_val_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1151_ = l_Lean_stringToMessageData(v___x_1150_);
return v___x_1151_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1153_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1154_ = l_Lean_stringToMessageData(v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1157_ = l_Lean_stringToMessageData(v___x_1156_);
return v___x_1157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1158_, lean_object* v_nParams_1159_, lean_object* v_belowName_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v___x_1166_; 
lean_inc(v_recName_1158_);
v___x_1166_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1158_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
if (lean_obj_tag(v_a_1167_) == 7)
{
lean_object* v_val_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1283_; 
v_val_1168_ = lean_ctor_get(v_a_1167_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1167_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1170_ = v_a_1167_;
v_isShared_1171_ = v_isSharedCheck_1283_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_val_1168_);
lean_dec(v_a_1167_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1283_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_toConstantVal_1172_; lean_object* v_numMotives_1173_; lean_object* v_numMinors_1174_; lean_object* v_levelParams_1175_; lean_object* v_type_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_toConstantVal_1172_ = lean_ctor_get(v_val_1168_, 0);
lean_inc_ref(v_toConstantVal_1172_);
v_numMotives_1173_ = lean_ctor_get(v_val_1168_, 4);
lean_inc(v_numMotives_1173_);
v_numMinors_1174_ = lean_ctor_get(v_val_1168_, 5);
lean_inc(v_numMinors_1174_);
lean_dec_ref(v_val_1168_);
v_levelParams_1175_ = lean_ctor_get(v_toConstantVal_1172_, 1);
lean_inc_n(v_levelParams_1175_, 2);
v_type_1176_ = lean_ctor_get(v_toConstantVal_1172_, 2);
lean_inc_ref(v_type_1176_);
lean_dec_ref(v_toConstantVal_1172_);
v___x_1177_ = lean_box(0);
v___x_1178_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1175_, v___x_1177_);
if (lean_obj_tag(v___x_1178_) == 1)
{
lean_object* v_head_1179_; lean_object* v_tail_1180_; lean_object* v___f_1181_; uint8_t v___x_1182_; lean_object* v___x_1183_; 
v_head_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_head_1179_);
v_tail_1180_ = lean_ctor_get(v___x_1178_, 1);
lean_inc(v_tail_1180_);
lean_dec_ref_known(v___x_1178_, 2);
v___f_1181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1181_, 0, v_nParams_1159_);
lean_closure_set(v___f_1181_, 1, v_numMotives_1173_);
lean_closure_set(v___f_1181_, 2, v_numMinors_1174_);
lean_closure_set(v___f_1181_, 3, v_head_1179_);
lean_closure_set(v___f_1181_, 4, v_tail_1180_);
lean_closure_set(v___f_1181_, 5, v_recName_1158_);
lean_closure_set(v___f_1181_, 6, v_belowName_1160_);
lean_closure_set(v___f_1181_, 7, v_levelParams_1175_);
v___x_1182_ = 0;
v___x_1183_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1176_, v___f_1181_, v___x_1182_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1186_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_n(v_a_1184_, 2);
lean_dec_ref_known(v___x_1183_, 1);
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 1);
lean_ctor_set(v___x_1170_, 0, v_a_1184_);
v___x_1186_ = v___x_1170_;
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
v___x_1187_ = l_Lean_addDecl(v___x_1186_, v___x_1182_, v_a_1163_, v_a_1164_);
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
v___x_1190_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1189_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
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
v___x_1194_ = lean_st_ref_take(v_a_1164_);
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
v___x_1210_ = lean_st_ref_set(v_a_1164_, v___x_1209_);
v___x_1211_ = lean_st_ref_take(v_a_1162_);
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
v___x_1222_ = lean_st_ref_set(v_a_1162_, v___x_1221_);
v___x_1223_ = lean_st_ref_take(v_a_1164_);
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
v___x_1238_ = lean_st_ref_set(v_a_1164_, v___x_1237_);
v___x_1239_ = lean_st_ref_take(v_a_1162_);
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
v___x_1249_ = lean_st_ref_set(v_a_1162_, v___x_1248_);
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
lean_del_object(v___x_1170_);
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
lean_dec(v___x_1178_);
lean_dec_ref(v_type_1176_);
lean_dec(v_levelParams_1175_);
lean_dec(v_numMinors_1174_);
lean_dec(v_numMotives_1173_);
lean_del_object(v___x_1170_);
lean_dec(v_belowName_1160_);
lean_dec(v_nParams_1159_);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1278_ = l_Lean_MessageData_ofName(v_recName_1158_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1281_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1282_;
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_a_1167_);
lean_dec(v_belowName_1160_);
lean_dec(v_nParams_1159_);
v___x_1284_ = l_Lean_MessageData_ofName(v_recName_1158_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1286_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_belowName_1160_);
lean_dec(v_nParams_1159_);
lean_dec(v_recName_1158_);
v_a_1288_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1166_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1166_);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__0(void){
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((size_t)5ULL);
v___x_1430_ = lean_unsigned_to_nat(0u);
v___x_1431_ = lean_unsigned_to_nat(32u);
v___x_1432_ = lean_mk_empty_array_with_capacity(v___x_1431_);
v___x_1433_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__0);
v___x_1434_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1432_);
lean_ctor_set(v___x_1434_, 2, v___x_1430_);
lean_ctor_set(v___x_1434_, 3, v___x_1430_);
lean_ctor_set_usize(v___x_1434_, 4, v___x_1429_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg(lean_object* v___y_1435_){
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
v___x_1457_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___closed__1);
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
v___x_1462_ = lean_st_ref_set(v___y_1435_, v___x_1461_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_traces_1439_);
return v___x_1463_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg(v___y_1469_);
lean_dec(v___y_1469_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0(lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg(v___y_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___boxed(lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0(v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1483_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__1(lean_object* v_opts_1484_, lean_object* v_opt_1485_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__1___boxed(lean_object* v_opts_1494_, lean_object* v_opt_1495_){
_start:
{
uint8_t v_res_1496_; lean_object* v_r_1497_; 
v_res_1496_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__1(v_opts_1494_, v_opt_1495_);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(lean_object* v_upperBound_1515_, lean_object* v___x_1516_, lean_object* v___x_1517_, lean_object* v___x_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
uint8_t v___x_1526_; 
v___x_1526_ = lean_nat_dec_lt(v_a_1519_, v_upperBound_1515_);
if (v___x_1526_ == 0)
{
lean_object* v___x_1527_; 
lean_dec(v_a_1519_);
lean_dec(v___x_1518_);
lean_dec(v___x_1517_);
lean_dec(v___x_1516_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v_b_1520_);
return v___x_1527_;
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1528_ = lean_unsigned_to_nat(1u);
v___x_1529_ = lean_nat_add(v_a_1519_, v___x_1528_);
lean_dec(v_a_1519_);
lean_inc_n(v___x_1529_, 2);
lean_inc(v___x_1516_);
v___x_1530_ = lean_name_append_index_after(v___x_1516_, v___x_1529_);
lean_inc(v___x_1517_);
v___x_1531_ = lean_name_append_index_after(v___x_1517_, v___x_1529_);
lean_inc(v___x_1518_);
v___x_1532_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1530_, v___x_1518_, v___x_1531_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1533_; 
lean_dec_ref_known(v___x_1532_, 1);
v___x_1533_ = lean_box(0);
v_a_1519_ = v___x_1529_;
v_b_1520_ = v___x_1533_;
goto _start;
}
else
{
lean_dec(v___x_1529_);
lean_dec(v___x_1518_);
lean_dec(v___x_1517_);
lean_dec(v___x_1516_);
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg___boxed(lean_object* v_upperBound_1535_, lean_object* v___x_1536_, lean_object* v___x_1537_, lean_object* v___x_1538_, lean_object* v_a_1539_, lean_object* v_b_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(v_upperBound_1535_, v___x_1536_, v___x_1537_, v___x_1538_, v_a_1539_, v_b_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v_upperBound_1535_);
return v_res_1546_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__4(lean_object* v_e_1547_){
_start:
{
if (lean_obj_tag(v_e_1547_) == 0)
{
uint8_t v___x_1548_; 
v___x_1548_ = 2;
return v___x_1548_;
}
else
{
uint8_t v___x_1549_; 
v___x_1549_ = 0;
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__4___boxed(lean_object* v_e_1550_){
_start:
{
uint8_t v_res_1551_; lean_object* v_r_1552_; 
v_res_1551_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__4(v_e_1550_);
lean_dec_ref(v_e_1550_);
v_r_1552_ = lean_box(v_res_1551_);
return v_r_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2_spec__3(size_t v_sz_1553_, size_t v_i_1554_, lean_object* v_bs_1555_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2_spec__3___boxed(lean_object* v_sz_1565_, lean_object* v_i_1566_, lean_object* v_bs_1567_){
_start:
{
size_t v_sz_boxed_1568_; size_t v_i_boxed_1569_; lean_object* v_res_1570_; 
v_sz_boxed_1568_ = lean_unbox_usize(v_sz_1565_);
lean_dec(v_sz_1565_);
v_i_boxed_1569_ = lean_unbox_usize(v_i_1566_);
lean_dec(v_i_1566_);
v_res_1570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2_spec__3(v_sz_boxed_1568_, v_i_boxed_1569_, v_bs_1567_);
return v_res_1570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2(lean_object* v_oldTraces_1571_, lean_object* v_data_1572_, lean_object* v_ref_1573_, lean_object* v_msg_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_fileName_1580_; lean_object* v_fileMap_1581_; lean_object* v_options_1582_; lean_object* v_currRecDepth_1583_; lean_object* v_maxRecDepth_1584_; lean_object* v_ref_1585_; lean_object* v_currNamespace_1586_; lean_object* v_openDecls_1587_; lean_object* v_initHeartbeats_1588_; lean_object* v_maxHeartbeats_1589_; lean_object* v_quotContext_1590_; lean_object* v_currMacroScope_1591_; uint8_t v_diag_1592_; lean_object* v_cancelTk_x3f_1593_; uint8_t v_suppressElabErrors_1594_; lean_object* v_inheritedTraceOptions_1595_; lean_object* v___x_1596_; lean_object* v_traceState_1597_; lean_object* v_traces_1598_; lean_object* v_ref_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; size_t v_sz_1602_; size_t v___x_1603_; lean_object* v___x_1604_; lean_object* v_msg_1605_; lean_object* v___x_1606_; lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1644_; 
v_fileName_1580_ = lean_ctor_get(v___y_1577_, 0);
v_fileMap_1581_ = lean_ctor_get(v___y_1577_, 1);
v_options_1582_ = lean_ctor_get(v___y_1577_, 2);
v_currRecDepth_1583_ = lean_ctor_get(v___y_1577_, 3);
v_maxRecDepth_1584_ = lean_ctor_get(v___y_1577_, 4);
v_ref_1585_ = lean_ctor_get(v___y_1577_, 5);
v_currNamespace_1586_ = lean_ctor_get(v___y_1577_, 6);
v_openDecls_1587_ = lean_ctor_get(v___y_1577_, 7);
v_initHeartbeats_1588_ = lean_ctor_get(v___y_1577_, 8);
v_maxHeartbeats_1589_ = lean_ctor_get(v___y_1577_, 9);
v_quotContext_1590_ = lean_ctor_get(v___y_1577_, 10);
v_currMacroScope_1591_ = lean_ctor_get(v___y_1577_, 11);
v_diag_1592_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*14);
v_cancelTk_x3f_1593_ = lean_ctor_get(v___y_1577_, 12);
v_suppressElabErrors_1594_ = lean_ctor_get_uint8(v___y_1577_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1595_ = lean_ctor_get(v___y_1577_, 13);
v___x_1596_ = lean_st_ref_get(v___y_1578_);
v_traceState_1597_ = lean_ctor_get(v___x_1596_, 4);
lean_inc_ref(v_traceState_1597_);
lean_dec(v___x_1596_);
v_traces_1598_ = lean_ctor_get(v_traceState_1597_, 0);
lean_inc_ref(v_traces_1598_);
lean_dec_ref(v_traceState_1597_);
v_ref_1599_ = l_Lean_replaceRef(v_ref_1573_, v_ref_1585_);
lean_inc_ref(v_inheritedTraceOptions_1595_);
lean_inc(v_cancelTk_x3f_1593_);
lean_inc(v_currMacroScope_1591_);
lean_inc(v_quotContext_1590_);
lean_inc(v_maxHeartbeats_1589_);
lean_inc(v_initHeartbeats_1588_);
lean_inc(v_openDecls_1587_);
lean_inc(v_currNamespace_1586_);
lean_inc(v_maxRecDepth_1584_);
lean_inc(v_currRecDepth_1583_);
lean_inc_ref(v_options_1582_);
lean_inc_ref(v_fileMap_1581_);
lean_inc_ref(v_fileName_1580_);
v___x_1600_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1600_, 0, v_fileName_1580_);
lean_ctor_set(v___x_1600_, 1, v_fileMap_1581_);
lean_ctor_set(v___x_1600_, 2, v_options_1582_);
lean_ctor_set(v___x_1600_, 3, v_currRecDepth_1583_);
lean_ctor_set(v___x_1600_, 4, v_maxRecDepth_1584_);
lean_ctor_set(v___x_1600_, 5, v_ref_1599_);
lean_ctor_set(v___x_1600_, 6, v_currNamespace_1586_);
lean_ctor_set(v___x_1600_, 7, v_openDecls_1587_);
lean_ctor_set(v___x_1600_, 8, v_initHeartbeats_1588_);
lean_ctor_set(v___x_1600_, 9, v_maxHeartbeats_1589_);
lean_ctor_set(v___x_1600_, 10, v_quotContext_1590_);
lean_ctor_set(v___x_1600_, 11, v_currMacroScope_1591_);
lean_ctor_set(v___x_1600_, 12, v_cancelTk_x3f_1593_);
lean_ctor_set(v___x_1600_, 13, v_inheritedTraceOptions_1595_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*14, v_diag_1592_);
lean_ctor_set_uint8(v___x_1600_, sizeof(void*)*14 + 1, v_suppressElabErrors_1594_);
v___x_1601_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1598_);
lean_dec_ref(v_traces_1598_);
v_sz_1602_ = lean_array_size(v___x_1601_);
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2_spec__3(v_sz_1602_, v___x_1603_, v___x_1601_);
v_msg_1605_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1605_, 0, v_data_1572_);
lean_ctor_set(v_msg_1605_, 1, v_msg_1574_);
lean_ctor_set(v_msg_1605_, 2, v___x_1604_);
v___x_1606_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1605_, v___y_1575_, v___y_1576_, v___x_1600_, v___y_1578_);
lean_dec_ref_known(v___x_1600_, 14);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1609_ = v___x_1606_;
v_isShared_1610_ = v_isSharedCheck_1644_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1606_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1644_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1611_; lean_object* v_traceState_1612_; lean_object* v_env_1613_; lean_object* v_nextMacroScope_1614_; lean_object* v_ngen_1615_; lean_object* v_auxDeclNGen_1616_; lean_object* v_cache_1617_; lean_object* v_messages_1618_; lean_object* v_infoState_1619_; lean_object* v_snapshotTasks_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1643_; 
v___x_1611_ = lean_st_ref_take(v___y_1578_);
v_traceState_1612_ = lean_ctor_get(v___x_1611_, 4);
v_env_1613_ = lean_ctor_get(v___x_1611_, 0);
v_nextMacroScope_1614_ = lean_ctor_get(v___x_1611_, 1);
v_ngen_1615_ = lean_ctor_get(v___x_1611_, 2);
v_auxDeclNGen_1616_ = lean_ctor_get(v___x_1611_, 3);
v_cache_1617_ = lean_ctor_get(v___x_1611_, 5);
v_messages_1618_ = lean_ctor_get(v___x_1611_, 6);
v_infoState_1619_ = lean_ctor_get(v___x_1611_, 7);
v_snapshotTasks_1620_ = lean_ctor_get(v___x_1611_, 8);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1622_ = v___x_1611_;
v_isShared_1623_ = v_isSharedCheck_1643_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_snapshotTasks_1620_);
lean_inc(v_infoState_1619_);
lean_inc(v_messages_1618_);
lean_inc(v_cache_1617_);
lean_inc(v_traceState_1612_);
lean_inc(v_auxDeclNGen_1616_);
lean_inc(v_ngen_1615_);
lean_inc(v_nextMacroScope_1614_);
lean_inc(v_env_1613_);
lean_dec(v___x_1611_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1643_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
uint64_t v_tid_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1641_; 
v_tid_1624_ = lean_ctor_get_uint64(v_traceState_1612_, sizeof(void*)*1);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_traceState_1612_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v_traceState_1612_, 0);
lean_dec(v_unused_1642_);
v___x_1626_ = v_traceState_1612_;
v_isShared_1627_ = v_isSharedCheck_1641_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v_traceState_1612_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1641_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1628_, 0, v_ref_1573_);
lean_ctor_set(v___x_1628_, 1, v_a_1607_);
v___x_1629_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1571_, v___x_1628_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 0, v___x_1629_);
v___x_1631_ = v___x_1626_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1629_);
lean_ctor_set_uint64(v_reuseFailAlloc_1640_, sizeof(void*)*1, v_tid_1624_);
v___x_1631_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v___x_1631_);
v___x_1633_ = v___x_1622_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_env_1613_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_nextMacroScope_1614_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_ngen_1615_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_auxDeclNGen_1616_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1639_, 5, v_cache_1617_);
lean_ctor_set(v_reuseFailAlloc_1639_, 6, v_messages_1618_);
lean_ctor_set(v_reuseFailAlloc_1639_, 7, v_infoState_1619_);
lean_ctor_set(v_reuseFailAlloc_1639_, 8, v_snapshotTasks_1620_);
v___x_1633_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1634_ = lean_st_ref_set(v___y_1578_, v___x_1633_);
v___x_1635_ = lean_box(0);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1635_);
v___x_1637_ = v___x_1609_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2___boxed(lean_object* v_oldTraces_1645_, lean_object* v_data_1646_, lean_object* v_ref_1647_, lean_object* v_msg_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2(v_oldTraces_1645_, v_data_1646_, v_ref_1647_, v_msg_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__5(lean_object* v_opts_1655_, lean_object* v_opt_1656_){
_start:
{
lean_object* v_name_1657_; lean_object* v_defValue_1658_; lean_object* v_map_1659_; lean_object* v___x_1660_; 
v_name_1657_ = lean_ctor_get(v_opt_1656_, 0);
v_defValue_1658_ = lean_ctor_get(v_opt_1656_, 1);
v_map_1659_ = lean_ctor_get(v_opts_1655_, 0);
v___x_1660_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1659_, v_name_1657_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_inc(v_defValue_1658_);
return v_defValue_1658_;
}
else
{
lean_object* v_val_1661_; 
v_val_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_val_1661_);
lean_dec_ref_known(v___x_1660_, 1);
if (lean_obj_tag(v_val_1661_) == 3)
{
lean_object* v_v_1662_; 
v_v_1662_ = lean_ctor_get(v_val_1661_, 0);
lean_inc(v_v_1662_);
lean_dec_ref_known(v_val_1661_, 1);
return v_v_1662_;
}
else
{
lean_dec(v_val_1661_);
lean_inc(v_defValue_1658_);
return v_defValue_1658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__5___boxed(lean_object* v_opts_1663_, lean_object* v_opt_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__5(v_opts_1663_, v_opt_1664_);
lean_dec_ref(v_opt_1664_);
lean_dec_ref(v_opts_1663_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg(lean_object* v_x_1666_){
_start:
{
if (lean_obj_tag(v_x_1666_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
v_a_1668_ = lean_ctor_get(v_x_1666_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v_x_1666_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v_x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 1);
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
else
{
lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1683_; 
v_a_1676_ = lean_ctor_get(v_x_1666_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_x_1666_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1678_ = v_x_1666_;
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_dec(v_x_1666_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1683_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1681_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set_tag(v___x_1678_, 0);
v___x_1681_ = v___x_1678_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_a_1676_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg___boxed(lean_object* v_x_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg(v_x_1684_);
return v_res_1686_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1687_; double v___x_1688_; 
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = lean_float_of_nat(v___x_1687_);
return v___x_1688_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1690_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__1));
v___x_1691_ = l_Lean_stringToMessageData(v___x_1690_);
return v___x_1691_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1692_; double v___x_1693_; 
v___x_1692_ = lean_unsigned_to_nat(1000u);
v___x_1693_ = lean_float_of_nat(v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2(lean_object* v_cls_1694_, uint8_t v_collapsed_1695_, lean_object* v_tag_1696_, lean_object* v_opts_1697_, uint8_t v_clsEnabled_1698_, lean_object* v_oldTraces_1699_, lean_object* v_msg_1700_, lean_object* v_resStartStop_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_fst_1707_; lean_object* v_snd_1708_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v_data_1712_; lean_object* v_fst_1715_; lean_object* v_snd_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; lean_object* v___y_1720_; lean_object* v_a_1721_; uint8_t v___y_1736_; double v___y_1767_; 
v_fst_1707_ = lean_ctor_get(v_resStartStop_1701_, 0);
lean_inc(v_fst_1707_);
v_snd_1708_ = lean_ctor_get(v_resStartStop_1701_, 1);
lean_inc(v_snd_1708_);
lean_dec_ref(v_resStartStop_1701_);
v_fst_1715_ = lean_ctor_get(v_snd_1708_, 0);
lean_inc(v_fst_1715_);
v_snd_1716_ = lean_ctor_get(v_snd_1708_, 1);
lean_inc(v_snd_1716_);
lean_dec(v_snd_1708_);
v___x_1717_ = l_Lean_trace_profiler;
v___x_1718_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__1(v_opts_1697_, v___x_1717_);
if (v___x_1718_ == 0)
{
v___y_1736_ = v___x_1718_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1772_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1773_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__1(v_opts_1697_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; double v___x_1776_; double v___x_1777_; double v___x_1778_; 
v___x_1774_ = l_Lean_trace_profiler_threshold;
v___x_1775_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__5(v_opts_1697_, v___x_1774_);
v___x_1776_ = lean_float_of_nat(v___x_1775_);
v___x_1777_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__3);
v___x_1778_ = lean_float_div(v___x_1776_, v___x_1777_);
v___y_1767_ = v___x_1778_;
goto v___jp_1766_;
}
else
{
lean_object* v___x_1779_; lean_object* v___x_1780_; double v___x_1781_; 
v___x_1779_ = l_Lean_trace_profiler_threshold;
v___x_1780_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__5(v_opts_1697_, v___x_1779_);
v___x_1781_ = lean_float_of_nat(v___x_1780_);
v___y_1767_ = v___x_1781_;
goto v___jp_1766_;
}
}
v___jp_1709_:
{
lean_object* v___x_1713_; 
lean_inc(v___y_1710_);
v___x_1713_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__2(v_oldTraces_1699_, v_data_1712_, v___y_1710_, v___y_1711_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v___x_1714_; 
lean_dec_ref_known(v___x_1713_, 1);
v___x_1714_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg(v_fst_1707_);
return v___x_1714_;
}
else
{
lean_dec(v_fst_1707_);
return v___x_1713_;
}
}
v___jp_1719_:
{
uint8_t v_result_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; double v___x_1725_; lean_object* v_data_1726_; 
v_result_1722_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__4(v_fst_1707_);
v___x_1723_ = lean_box(v_result_1722_);
v___x_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1723_);
v___x_1725_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__0);
lean_inc_ref(v_tag_1696_);
lean_inc_ref(v___x_1724_);
lean_inc(v_cls_1694_);
v_data_1726_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1726_, 0, v_cls_1694_);
lean_ctor_set(v_data_1726_, 1, v___x_1724_);
lean_ctor_set(v_data_1726_, 2, v_tag_1696_);
lean_ctor_set_float(v_data_1726_, sizeof(void*)*3, v___x_1725_);
lean_ctor_set_float(v_data_1726_, sizeof(void*)*3 + 8, v___x_1725_);
lean_ctor_set_uint8(v_data_1726_, sizeof(void*)*3 + 16, v_collapsed_1695_);
if (v___x_1718_ == 0)
{
lean_dec_ref_known(v___x_1724_, 1);
lean_dec(v_snd_1716_);
lean_dec(v_fst_1715_);
lean_dec_ref(v_tag_1696_);
lean_dec(v_cls_1694_);
v___y_1710_ = v___y_1720_;
v___y_1711_ = v_a_1721_;
v_data_1712_ = v_data_1726_;
goto v___jp_1709_;
}
else
{
lean_object* v_data_1727_; double v___x_1728_; double v___x_1729_; 
lean_dec_ref_known(v_data_1726_, 3);
v_data_1727_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1727_, 0, v_cls_1694_);
lean_ctor_set(v_data_1727_, 1, v___x_1724_);
lean_ctor_set(v_data_1727_, 2, v_tag_1696_);
v___x_1728_ = lean_unbox_float(v_fst_1715_);
lean_dec(v_fst_1715_);
lean_ctor_set_float(v_data_1727_, sizeof(void*)*3, v___x_1728_);
v___x_1729_ = lean_unbox_float(v_snd_1716_);
lean_dec(v_snd_1716_);
lean_ctor_set_float(v_data_1727_, sizeof(void*)*3 + 8, v___x_1729_);
lean_ctor_set_uint8(v_data_1727_, sizeof(void*)*3 + 16, v_collapsed_1695_);
v___y_1710_ = v___y_1720_;
v___y_1711_ = v_a_1721_;
v_data_1712_ = v_data_1727_;
goto v___jp_1709_;
}
}
v___jp_1730_:
{
lean_object* v_ref_1731_; lean_object* v___x_1732_; 
v_ref_1731_ = lean_ctor_get(v___y_1704_, 5);
lean_inc(v___y_1705_);
lean_inc_ref(v___y_1704_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v_fst_1707_);
v___x_1732_ = lean_apply_6(v_msg_1700_, v_fst_1707_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, lean_box(0));
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v___y_1720_ = v_ref_1731_;
v_a_1721_ = v_a_1733_;
goto v___jp_1719_;
}
else
{
lean_object* v___x_1734_; 
lean_dec_ref_known(v___x_1732_, 1);
v___x_1734_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___closed__2);
v___y_1720_ = v_ref_1731_;
v_a_1721_ = v___x_1734_;
goto v___jp_1719_;
}
}
v___jp_1735_:
{
if (v_clsEnabled_1698_ == 0)
{
if (v___y_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v_traceState_1738_; lean_object* v_env_1739_; lean_object* v_nextMacroScope_1740_; lean_object* v_ngen_1741_; lean_object* v_auxDeclNGen_1742_; lean_object* v_cache_1743_; lean_object* v_messages_1744_; lean_object* v_infoState_1745_; lean_object* v_snapshotTasks_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1765_; 
lean_dec(v_snd_1716_);
lean_dec(v_fst_1715_);
lean_dec_ref(v_msg_1700_);
lean_dec_ref(v_tag_1696_);
lean_dec(v_cls_1694_);
v___x_1737_ = lean_st_ref_take(v___y_1705_);
v_traceState_1738_ = lean_ctor_get(v___x_1737_, 4);
v_env_1739_ = lean_ctor_get(v___x_1737_, 0);
v_nextMacroScope_1740_ = lean_ctor_get(v___x_1737_, 1);
v_ngen_1741_ = lean_ctor_get(v___x_1737_, 2);
v_auxDeclNGen_1742_ = lean_ctor_get(v___x_1737_, 3);
v_cache_1743_ = lean_ctor_get(v___x_1737_, 5);
v_messages_1744_ = lean_ctor_get(v___x_1737_, 6);
v_infoState_1745_ = lean_ctor_get(v___x_1737_, 7);
v_snapshotTasks_1746_ = lean_ctor_get(v___x_1737_, 8);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1748_ = v___x_1737_;
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_snapshotTasks_1746_);
lean_inc(v_infoState_1745_);
lean_inc(v_messages_1744_);
lean_inc(v_cache_1743_);
lean_inc(v_traceState_1738_);
lean_inc(v_auxDeclNGen_1742_);
lean_inc(v_ngen_1741_);
lean_inc(v_nextMacroScope_1740_);
lean_inc(v_env_1739_);
lean_dec(v___x_1737_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1765_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
uint64_t v_tid_1750_; lean_object* v_traces_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1764_; 
v_tid_1750_ = lean_ctor_get_uint64(v_traceState_1738_, sizeof(void*)*1);
v_traces_1751_ = lean_ctor_get(v_traceState_1738_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_traceState_1738_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1753_ = v_traceState_1738_;
v_isShared_1754_ = v_isSharedCheck_1764_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_traces_1751_);
lean_dec(v_traceState_1738_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1764_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1699_, v_traces_1751_);
lean_dec_ref(v_traces_1751_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1755_);
v___x_1757_ = v___x_1753_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1755_);
lean_ctor_set_uint64(v_reuseFailAlloc_1763_, sizeof(void*)*1, v_tid_1750_);
v___x_1757_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 4, v___x_1757_);
v___x_1759_ = v___x_1748_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_env_1739_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_nextMacroScope_1740_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_ngen_1741_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_auxDeclNGen_1742_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1762_, 5, v_cache_1743_);
lean_ctor_set(v_reuseFailAlloc_1762_, 6, v_messages_1744_);
lean_ctor_set(v_reuseFailAlloc_1762_, 7, v_infoState_1745_);
lean_ctor_set(v_reuseFailAlloc_1762_, 8, v_snapshotTasks_1746_);
v___x_1759_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_st_ref_set(v___y_1705_, v___x_1759_);
v___x_1761_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg(v_fst_1707_);
return v___x_1761_;
}
}
}
}
}
else
{
goto v___jp_1730_;
}
}
else
{
goto v___jp_1730_;
}
}
v___jp_1766_:
{
double v___x_1768_; double v___x_1769_; double v___x_1770_; uint8_t v___x_1771_; 
v___x_1768_ = lean_unbox_float(v_snd_1716_);
v___x_1769_ = lean_unbox_float(v_fst_1715_);
v___x_1770_ = lean_float_sub(v___x_1768_, v___x_1769_);
v___x_1771_ = lean_float_decLt(v___y_1767_, v___x_1770_);
v___y_1736_ = v___x_1771_;
goto v___jp_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_cls_1782_, lean_object* v_collapsed_1783_, lean_object* v_tag_1784_, lean_object* v_opts_1785_, lean_object* v_clsEnabled_1786_, lean_object* v_oldTraces_1787_, lean_object* v_msg_1788_, lean_object* v_resStartStop_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v_collapsed_boxed_1795_; uint8_t v_clsEnabled_boxed_1796_; lean_object* v_res_1797_; 
v_collapsed_boxed_1795_ = lean_unbox(v_collapsed_1783_);
v_clsEnabled_boxed_1796_ = lean_unbox(v_clsEnabled_1786_);
v_res_1797_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2(v_cls_1782_, v_collapsed_boxed_1795_, v_tag_1784_, v_opts_1785_, v_clsEnabled_boxed_1796_, v_oldTraces_1787_, v_msg_1788_, v_resStartStop_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
lean_dec_ref(v_opts_1785_);
return v_res_1797_;
}
}
static double _init_l_Lean_mkBelow___closed__4(void){
_start:
{
lean_object* v___x_1804_; double v___x_1805_; 
v___x_1804_ = lean_unsigned_to_nat(1000000000u);
v___x_1805_ = lean_float_of_nat(v___x_1804_);
return v___x_1805_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1810_ = ((lean_object*)(l_Lean_mkBelow___closed__6));
v___x_1811_ = l_Lean_Name_append(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_options_1818_; lean_object* v_inheritedTraceOptions_1819_; uint8_t v_hasTrace_1820_; uint8_t v___x_1821_; 
v_options_1818_ = lean_ctor_get(v_a_1815_, 2);
v_inheritedTraceOptions_1819_ = lean_ctor_get(v_a_1815_, 13);
v_hasTrace_1820_ = lean_ctor_get_uint8(v_options_1818_, sizeof(void*)*1);
v___x_1821_ = lean_bool_not(v_hasTrace_1820_);
if (v___x_1821_ == 0)
{
lean_object* v___f_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___y_1827_; uint8_t v___y_1828_; lean_object* v___y_1829_; lean_object* v_a_1830_; lean_object* v___y_1843_; uint8_t v___y_1844_; lean_object* v___y_1845_; lean_object* v_a_1846_; lean_object* v___y_1849_; uint8_t v___y_1850_; lean_object* v___y_1851_; lean_object* v_a_1852_; lean_object* v___y_1855_; uint8_t v___y_1856_; lean_object* v___y_1857_; lean_object* v_a_1858_; lean_object* v___y_1868_; uint8_t v___y_1869_; lean_object* v___y_1870_; lean_object* v_a_1871_; lean_object* v___y_1874_; uint8_t v___y_1875_; lean_object* v___y_1876_; lean_object* v_a_1877_; uint8_t v___y_1880_; uint8_t v_a_1948_; 
lean_inc(v_indName_1812_);
v___f_1822_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1822_, 0, v_indName_1812_);
v___x_1823_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1824_ = 1;
v___x_1825_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
if (v_hasTrace_1820_ == 0)
{
v_a_1948_ = v_hasTrace_1820_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = lean_obj_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_2026_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1819_, v_options_1818_, v___x_2025_);
if (v___x_2026_ == 0)
{
v_a_1948_ = v___x_2026_;
goto v___jp_1947_;
}
else
{
v___y_1880_ = v___x_2026_;
goto v___jp_1879_;
}
}
v___jp_1826_:
{
lean_object* v___x_1831_; double v___x_1832_; double v___x_1833_; double v___x_1834_; double v___x_1835_; double v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1831_ = lean_io_mono_nanos_now();
v___x_1832_ = lean_float_of_nat(v___y_1827_);
v___x_1833_ = lean_float_once(&l_Lean_mkBelow___closed__4, &l_Lean_mkBelow___closed__4_once, _init_l_Lean_mkBelow___closed__4);
v___x_1834_ = lean_float_div(v___x_1832_, v___x_1833_);
v___x_1835_ = lean_float_of_nat(v___x_1831_);
v___x_1836_ = lean_float_div(v___x_1835_, v___x_1833_);
v___x_1837_ = lean_box_float(v___x_1834_);
v___x_1838_ = lean_box_float(v___x_1836_);
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_a_1830_);
lean_ctor_set(v___x_1840_, 1, v___x_1839_);
v___x_1841_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2(v___x_1823_, v___x_1824_, v___x_1825_, v_options_1818_, v___y_1828_, v___y_1829_, v___f_1822_, v___x_1840_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
return v___x_1841_;
}
v___jp_1842_:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_a_1846_);
v___y_1827_ = v___y_1843_;
v___y_1828_ = v___y_1844_;
v___y_1829_ = v___y_1845_;
v_a_1830_ = v___x_1847_;
goto v___jp_1826_;
}
v___jp_1848_:
{
lean_object* v___x_1853_; 
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_a_1852_);
v___y_1827_ = v___y_1849_;
v___y_1828_ = v___y_1850_;
v___y_1829_ = v___y_1851_;
v_a_1830_ = v___x_1853_;
goto v___jp_1826_;
}
v___jp_1854_:
{
lean_object* v___x_1859_; double v___x_1860_; double v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1859_ = lean_io_get_num_heartbeats();
v___x_1860_ = lean_float_of_nat(v___y_1855_);
v___x_1861_ = lean_float_of_nat(v___x_1859_);
v___x_1862_ = lean_box_float(v___x_1860_);
v___x_1863_ = lean_box_float(v___x_1861_);
v___x_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v_a_1858_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2(v___x_1823_, v___x_1824_, v___x_1825_, v_options_1818_, v___y_1856_, v___y_1857_, v___f_1822_, v___x_1865_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
return v___x_1866_;
}
v___jp_1867_:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1871_);
v___y_1855_ = v___y_1868_;
v___y_1856_ = v___y_1869_;
v___y_1857_ = v___y_1870_;
v_a_1858_ = v___x_1872_;
goto v___jp_1854_;
}
v___jp_1873_:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_a_1877_);
v___y_1855_ = v___y_1874_;
v___y_1856_ = v___y_1875_;
v___y_1857_ = v___y_1876_;
v_a_1858_ = v___x_1878_;
goto v___jp_1854_;
}
v___jp_1879_:
{
lean_object* v___x_1881_; lean_object* v_a_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v___x_1881_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg(v_a_1816_);
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1884_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__1(v_options_1818_, v___x_1883_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1812_);
v___x_1886_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_a_1887_; 
v_a_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1886_, 1);
if (lean_obj_tag(v_a_1887_) == 5)
{
lean_object* v_val_1888_; uint8_t v_isRec_1889_; 
v_val_1888_ = lean_ctor_get(v_a_1887_, 0);
lean_inc_ref(v_val_1888_);
lean_dec_ref_known(v_a_1887_, 1);
v_isRec_1889_ = lean_ctor_get_uint8(v_val_1888_, sizeof(void*)*6);
if (v_isRec_1889_ == 0)
{
lean_object* v___x_1890_; 
lean_dec_ref(v_val_1888_);
lean_dec(v_indName_1812_);
v___x_1890_ = lean_box(0);
v___y_1849_ = v___x_1885_;
v___y_1850_ = v___y_1880_;
v___y_1851_ = v_a_1882_;
v_a_1852_ = v___x_1890_;
goto v___jp_1848_;
}
else
{
lean_object* v_toConstantVal_1891_; lean_object* v_numParams_1892_; lean_object* v_all_1893_; lean_object* v_numNested_1894_; lean_object* v_type_1895_; lean_object* v___x_1896_; 
v_toConstantVal_1891_ = lean_ctor_get(v_val_1888_, 0);
lean_inc_ref(v_toConstantVal_1891_);
v_numParams_1892_ = lean_ctor_get(v_val_1888_, 1);
lean_inc(v_numParams_1892_);
v_all_1893_ = lean_ctor_get(v_val_1888_, 3);
lean_inc(v_all_1893_);
v_numNested_1894_ = lean_ctor_get(v_val_1888_, 5);
lean_inc(v_numNested_1894_);
lean_dec_ref(v_val_1888_);
v_type_1895_ = lean_ctor_get(v_toConstantVal_1891_, 2);
lean_inc_ref(v_type_1895_);
lean_dec_ref(v_toConstantVal_1891_);
v___x_1896_ = l_Lean_Meta_isPropFormerType(v_type_1895_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; uint8_t v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = lean_unbox(v_a_1897_);
lean_dec(v_a_1897_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_inc_n(v_indName_1812_, 2);
v___x_1899_ = l_Lean_mkRecName(v_indName_1812_);
v___x_1900_ = l_Lean_mkBelowName(v_indName_1812_);
lean_inc(v___x_1900_);
lean_inc(v_numParams_1892_);
lean_inc(v___x_1899_);
v___x_1901_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1899_, v_numParams_1892_, v___x_1900_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; 
lean_dec_ref_known(v___x_1901_, 1);
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_unsigned_to_nat(0u);
v___x_1904_ = l_List_get_x21Internal___redArg(v___x_1902_, v_all_1893_, v___x_1903_);
lean_dec(v_all_1893_);
v___x_1905_ = lean_name_eq(v___x_1904_, v_indName_1812_);
lean_dec(v_indName_1812_);
lean_dec(v___x_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___x_1906_; 
lean_dec(v___x_1900_);
lean_dec(v___x_1899_);
lean_dec(v_numNested_1894_);
lean_dec(v_numParams_1892_);
v___x_1906_ = lean_box(0);
v___y_1849_ = v___x_1885_;
v___y_1850_ = v___y_1880_;
v___y_1851_ = v_a_1882_;
v_a_1852_ = v___x_1906_;
goto v___jp_1848_;
}
else
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_box(0);
v___x_1908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(v_numNested_1894_, v___x_1899_, v___x_1900_, v_numParams_1892_, v___x_1903_, v___x_1907_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_numNested_1894_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_dec_ref_known(v___x_1908_, 1);
v___y_1849_ = v___x_1885_;
v___y_1850_ = v___y_1880_;
v___y_1851_ = v_a_1882_;
v_a_1852_ = v___x_1907_;
goto v___jp_1848_;
}
else
{
lean_object* v_a_1909_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref_known(v___x_1908_, 1);
v___y_1843_ = v___x_1885_;
v___y_1844_ = v___y_1880_;
v___y_1845_ = v_a_1882_;
v_a_1846_ = v_a_1909_;
goto v___jp_1842_;
}
}
}
else
{
lean_dec(v___x_1900_);
lean_dec(v___x_1899_);
lean_dec(v_numNested_1894_);
lean_dec(v_all_1893_);
lean_dec(v_numParams_1892_);
lean_dec(v_indName_1812_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1910_; 
v_a_1910_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1910_);
lean_dec_ref_known(v___x_1901_, 1);
v___y_1849_ = v___x_1885_;
v___y_1850_ = v___y_1880_;
v___y_1851_ = v_a_1882_;
v_a_1852_ = v_a_1910_;
goto v___jp_1848_;
}
else
{
lean_object* v_a_1911_; 
v_a_1911_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1911_);
lean_dec_ref_known(v___x_1901_, 1);
v___y_1843_ = v___x_1885_;
v___y_1844_ = v___y_1880_;
v___y_1845_ = v_a_1882_;
v_a_1846_ = v_a_1911_;
goto v___jp_1842_;
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec(v_numNested_1894_);
lean_dec(v_all_1893_);
lean_dec(v_numParams_1892_);
lean_dec(v_indName_1812_);
v___x_1912_ = lean_box(0);
v___y_1849_ = v___x_1885_;
v___y_1850_ = v___y_1880_;
v___y_1851_ = v_a_1882_;
v_a_1852_ = v___x_1912_;
goto v___jp_1848_;
}
}
else
{
lean_object* v_a_1913_; 
lean_dec(v_numNested_1894_);
lean_dec(v_all_1893_);
lean_dec(v_numParams_1892_);
lean_dec(v_indName_1812_);
v_a_1913_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1896_, 1);
v___y_1843_ = v___x_1885_;
v___y_1844_ = v___y_1880_;
v___y_1845_ = v_a_1882_;
v_a_1846_ = v_a_1913_;
goto v___jp_1842_;
}
}
}
else
{
lean_object* v___x_1914_; 
lean_dec(v_a_1887_);
lean_dec(v_indName_1812_);
v___x_1914_ = lean_box(0);
v___y_1849_ = v___x_1885_;
v___y_1850_ = v___y_1880_;
v___y_1851_ = v_a_1882_;
v_a_1852_ = v___x_1914_;
goto v___jp_1848_;
}
}
else
{
lean_object* v_a_1915_; 
lean_dec(v_indName_1812_);
v_a_1915_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___x_1886_, 1);
v___y_1843_ = v___x_1885_;
v___y_1844_ = v___y_1880_;
v___y_1845_ = v_a_1882_;
v_a_1846_ = v_a_1915_;
goto v___jp_1842_;
}
}
else
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1812_);
v___x_1917_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
if (lean_obj_tag(v_a_1918_) == 5)
{
lean_object* v_val_1919_; uint8_t v_isRec_1920_; 
v_val_1919_ = lean_ctor_get(v_a_1918_, 0);
lean_inc_ref(v_val_1919_);
lean_dec_ref_known(v_a_1918_, 1);
v_isRec_1920_ = lean_ctor_get_uint8(v_val_1919_, sizeof(void*)*6);
if (v_isRec_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_dec_ref(v_val_1919_);
lean_dec(v_indName_1812_);
v___x_1921_ = lean_box(0);
v___y_1874_ = v___x_1916_;
v___y_1875_ = v___y_1880_;
v___y_1876_ = v_a_1882_;
v_a_1877_ = v___x_1921_;
goto v___jp_1873_;
}
else
{
lean_object* v_toConstantVal_1922_; lean_object* v_numParams_1923_; lean_object* v_all_1924_; lean_object* v_numNested_1925_; lean_object* v_type_1926_; lean_object* v___x_1927_; 
v_toConstantVal_1922_ = lean_ctor_get(v_val_1919_, 0);
lean_inc_ref(v_toConstantVal_1922_);
v_numParams_1923_ = lean_ctor_get(v_val_1919_, 1);
lean_inc(v_numParams_1923_);
v_all_1924_ = lean_ctor_get(v_val_1919_, 3);
lean_inc(v_all_1924_);
v_numNested_1925_ = lean_ctor_get(v_val_1919_, 5);
lean_inc(v_numNested_1925_);
lean_dec_ref(v_val_1919_);
v_type_1926_ = lean_ctor_get(v_toConstantVal_1922_, 2);
lean_inc_ref(v_type_1926_);
lean_dec_ref(v_toConstantVal_1922_);
v___x_1927_ = l_Lean_Meta_isPropFormerType(v_type_1926_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; uint8_t v___x_1929_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref_known(v___x_1927_, 1);
v___x_1929_ = lean_unbox(v_a_1928_);
lean_dec(v_a_1928_);
if (v___x_1929_ == 0)
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
lean_inc_n(v_indName_1812_, 2);
v___x_1930_ = l_Lean_mkRecName(v_indName_1812_);
v___x_1931_ = l_Lean_mkBelowName(v_indName_1812_);
lean_inc(v___x_1931_);
lean_inc(v_numParams_1923_);
lean_inc(v___x_1930_);
v___x_1932_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1930_, v_numParams_1923_, v___x_1931_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
lean_dec_ref_known(v___x_1932_, 1);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = l_List_get_x21Internal___redArg(v___x_1933_, v_all_1924_, v___x_1934_);
lean_dec(v_all_1924_);
v___x_1936_ = lean_name_eq(v___x_1935_, v_indName_1812_);
lean_dec(v_indName_1812_);
lean_dec(v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; 
lean_dec(v___x_1931_);
lean_dec(v___x_1930_);
lean_dec(v_numNested_1925_);
lean_dec(v_numParams_1923_);
v___x_1937_ = lean_box(0);
v___y_1874_ = v___x_1916_;
v___y_1875_ = v___y_1880_;
v___y_1876_ = v_a_1882_;
v_a_1877_ = v___x_1937_;
goto v___jp_1873_;
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_box(0);
v___x_1939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(v_numNested_1925_, v___x_1930_, v___x_1931_, v_numParams_1923_, v___x_1934_, v___x_1938_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_numNested_1925_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_dec_ref_known(v___x_1939_, 1);
v___y_1874_ = v___x_1916_;
v___y_1875_ = v___y_1880_;
v___y_1876_ = v_a_1882_;
v_a_1877_ = v___x_1938_;
goto v___jp_1873_;
}
else
{
lean_object* v_a_1940_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___y_1868_ = v___x_1916_;
v___y_1869_ = v___y_1880_;
v___y_1870_ = v_a_1882_;
v_a_1871_ = v_a_1940_;
goto v___jp_1867_;
}
}
}
else
{
lean_dec(v___x_1931_);
lean_dec(v___x_1930_);
lean_dec(v_numNested_1925_);
lean_dec(v_all_1924_);
lean_dec(v_numParams_1923_);
lean_dec(v_indName_1812_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1941_; 
v_a_1941_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1932_, 1);
v___y_1874_ = v___x_1916_;
v___y_1875_ = v___y_1880_;
v___y_1876_ = v_a_1882_;
v_a_1877_ = v_a_1941_;
goto v___jp_1873_;
}
else
{
lean_object* v_a_1942_; 
v_a_1942_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1942_);
lean_dec_ref_known(v___x_1932_, 1);
v___y_1868_ = v___x_1916_;
v___y_1869_ = v___y_1880_;
v___y_1870_ = v_a_1882_;
v_a_1871_ = v_a_1942_;
goto v___jp_1867_;
}
}
}
else
{
lean_object* v___x_1943_; 
lean_dec(v_numNested_1925_);
lean_dec(v_all_1924_);
lean_dec(v_numParams_1923_);
lean_dec(v_indName_1812_);
v___x_1943_ = lean_box(0);
v___y_1874_ = v___x_1916_;
v___y_1875_ = v___y_1880_;
v___y_1876_ = v_a_1882_;
v_a_1877_ = v___x_1943_;
goto v___jp_1873_;
}
}
else
{
lean_object* v_a_1944_; 
lean_dec(v_numNested_1925_);
lean_dec(v_all_1924_);
lean_dec(v_numParams_1923_);
lean_dec(v_indName_1812_);
v_a_1944_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1927_, 1);
v___y_1868_ = v___x_1916_;
v___y_1869_ = v___y_1880_;
v___y_1870_ = v_a_1882_;
v_a_1871_ = v_a_1944_;
goto v___jp_1867_;
}
}
}
else
{
lean_object* v___x_1945_; 
lean_dec(v_a_1918_);
lean_dec(v_indName_1812_);
v___x_1945_ = lean_box(0);
v___y_1874_ = v___x_1916_;
v___y_1875_ = v___y_1880_;
v___y_1876_ = v_a_1882_;
v_a_1877_ = v___x_1945_;
goto v___jp_1873_;
}
}
else
{
lean_object* v_a_1946_; 
lean_dec(v_indName_1812_);
v_a_1946_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1917_, 1);
v___y_1868_ = v___x_1916_;
v___y_1869_ = v___y_1880_;
v___y_1870_ = v_a_1882_;
v_a_1871_ = v_a_1946_;
goto v___jp_1867_;
}
}
}
v___jp_1947_:
{
lean_object* v___x_1949_; uint8_t v___x_1950_; 
v___x_1949_ = l_Lean_trace_profiler;
v___x_1950_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__1(v_options_1818_, v___x_1949_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec_ref(v___f_1822_);
lean_inc(v_indName_1812_);
v___x_1951_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_2016_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1954_ = v___x_1951_;
v_isShared_1955_ = v_isSharedCheck_2016_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_2016_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
if (lean_obj_tag(v_a_1952_) == 5)
{
lean_object* v_val_1956_; uint8_t v_isRec_1957_; 
v_val_1956_ = lean_ctor_get(v_a_1952_, 0);
lean_inc_ref(v_val_1956_);
lean_dec_ref_known(v_a_1952_, 1);
v_isRec_1957_ = lean_ctor_get_uint8(v_val_1956_, sizeof(void*)*6);
if (v_isRec_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_dec_ref(v_val_1956_);
lean_dec(v_indName_1812_);
v___x_1958_ = lean_box(0);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_1958_);
v___x_1960_ = v___x_1954_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
else
{
lean_object* v_toConstantVal_1962_; lean_object* v_numParams_1963_; lean_object* v_all_1964_; lean_object* v_numNested_1965_; lean_object* v_type_1966_; lean_object* v___x_1967_; 
lean_del_object(v___x_1954_);
v_toConstantVal_1962_ = lean_ctor_get(v_val_1956_, 0);
lean_inc_ref(v_toConstantVal_1962_);
v_numParams_1963_ = lean_ctor_get(v_val_1956_, 1);
lean_inc(v_numParams_1963_);
v_all_1964_ = lean_ctor_get(v_val_1956_, 3);
lean_inc(v_all_1964_);
v_numNested_1965_ = lean_ctor_get(v_val_1956_, 5);
lean_inc(v_numNested_1965_);
lean_dec_ref(v_val_1956_);
v_type_1966_ = lean_ctor_get(v_toConstantVal_1962_, 2);
lean_inc_ref(v_type_1966_);
lean_dec_ref(v_toConstantVal_1962_);
v___x_1967_ = l_Lean_Meta_isPropFormerType(v_type_1966_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_2003_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1970_ = v___x_1967_;
v_isShared_1971_ = v_isSharedCheck_2003_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1967_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_2003_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_unbox(v_a_1968_);
lean_dec(v_a_1968_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1970_);
lean_inc_n(v_indName_1812_, 2);
v___x_1973_ = l_Lean_mkRecName(v_indName_1812_);
v___x_1974_ = l_Lean_mkBelowName(v_indName_1812_);
lean_inc(v___x_1974_);
lean_inc(v_numParams_1963_);
lean_inc(v___x_1973_);
v___x_1975_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1973_, v_numParams_1963_, v___x_1974_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1997_; 
v_isSharedCheck_1997_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; 
v_unused_1998_ = lean_ctor_get(v___x_1975_, 0);
lean_dec(v_unused_1998_);
v___x_1977_ = v___x_1975_;
v_isShared_1978_ = v_isSharedCheck_1997_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v___x_1975_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1997_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_unsigned_to_nat(0u);
v___x_1981_ = l_List_get_x21Internal___redArg(v___x_1979_, v_all_1964_, v___x_1980_);
lean_dec(v_all_1964_);
v___x_1982_ = lean_name_eq(v___x_1981_, v_indName_1812_);
lean_dec(v_indName_1812_);
lean_dec(v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; lean_object* v___x_1985_; 
lean_dec(v___x_1974_);
lean_dec(v___x_1973_);
lean_dec(v_numNested_1965_);
lean_dec(v_numParams_1963_);
v___x_1983_ = lean_box(0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1983_);
v___x_1985_ = v___x_1977_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
else
{
lean_object* v___x_1987_; lean_object* v___x_1988_; 
lean_del_object(v___x_1977_);
v___x_1987_ = lean_box(0);
v___x_1988_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(v_numNested_1965_, v___x_1973_, v___x_1974_, v_numParams_1963_, v___x_1980_, v___x_1987_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_numNested_1965_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_1995_ == 0)
{
lean_object* v_unused_1996_; 
v_unused_1996_ = lean_ctor_get(v___x_1988_, 0);
lean_dec(v_unused_1996_);
v___x_1990_ = v___x_1988_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_dec(v___x_1988_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1987_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
return v___x_1988_;
}
}
}
}
else
{
lean_dec(v___x_1974_);
lean_dec(v___x_1973_);
lean_dec(v_numNested_1965_);
lean_dec(v_all_1964_);
lean_dec(v_numParams_1963_);
lean_dec(v_indName_1812_);
return v___x_1975_;
}
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_dec(v_numNested_1965_);
lean_dec(v_all_1964_);
lean_dec(v_numParams_1963_);
lean_dec(v_indName_1812_);
v___x_1999_ = lean_box(0);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1999_);
v___x_2001_ = v___x_1970_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
else
{
lean_object* v_a_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2011_; 
lean_dec(v_numNested_1965_);
lean_dec(v_all_1964_);
lean_dec(v_numParams_1963_);
lean_dec(v_indName_1812_);
v_a_2004_ = lean_ctor_get(v___x_1967_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1967_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2006_ = v___x_1967_;
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_a_2004_);
lean_dec(v___x_1967_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2011_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2009_; 
if (v_isShared_2007_ == 0)
{
v___x_2009_ = v___x_2006_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2014_; 
lean_dec(v_a_1952_);
lean_dec(v_indName_1812_);
v___x_2012_ = lean_box(0);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 0, v___x_2012_);
v___x_2014_ = v___x_1954_;
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
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec(v_indName_1812_);
v_a_2017_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1951_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1951_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
else
{
v___y_1880_ = v_a_1948_;
goto v___jp_1879_;
}
}
}
else
{
lean_object* v___x_2027_; 
lean_inc(v_indName_1812_);
v___x_2027_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2092_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2092_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2092_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2092_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
if (lean_obj_tag(v_a_2028_) == 5)
{
lean_object* v_val_2032_; uint8_t v_isRec_2033_; 
v_val_2032_ = lean_ctor_get(v_a_2028_, 0);
lean_inc_ref(v_val_2032_);
lean_dec_ref_known(v_a_2028_, 1);
v_isRec_2033_ = lean_ctor_get_uint8(v_val_2032_, sizeof(void*)*6);
if (v_isRec_2033_ == 0)
{
lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_dec_ref(v_val_2032_);
lean_dec(v_indName_1812_);
v___x_2034_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2034_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
else
{
lean_object* v_toConstantVal_2038_; lean_object* v_numParams_2039_; lean_object* v_all_2040_; lean_object* v_numNested_2041_; lean_object* v_type_2042_; lean_object* v___x_2043_; 
lean_del_object(v___x_2030_);
v_toConstantVal_2038_ = lean_ctor_get(v_val_2032_, 0);
lean_inc_ref(v_toConstantVal_2038_);
v_numParams_2039_ = lean_ctor_get(v_val_2032_, 1);
lean_inc(v_numParams_2039_);
v_all_2040_ = lean_ctor_get(v_val_2032_, 3);
lean_inc(v_all_2040_);
v_numNested_2041_ = lean_ctor_get(v_val_2032_, 5);
lean_inc(v_numNested_2041_);
lean_dec_ref(v_val_2032_);
v_type_2042_ = lean_ctor_get(v_toConstantVal_2038_, 2);
lean_inc_ref(v_type_2042_);
lean_dec_ref(v_toConstantVal_2038_);
v___x_2043_ = l_Lean_Meta_isPropFormerType(v_type_2042_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2079_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2046_ = v___x_2043_;
v_isShared_2047_ = v_isSharedCheck_2079_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2043_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2079_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_unbox(v_a_2044_);
lean_dec(v_a_2044_);
if (v___x_2048_ == 0)
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
lean_del_object(v___x_2046_);
lean_inc_n(v_indName_1812_, 2);
v___x_2049_ = l_Lean_mkRecName(v_indName_1812_);
v___x_2050_ = l_Lean_mkBelowName(v_indName_1812_);
lean_inc(v___x_2050_);
lean_inc(v_numParams_2039_);
lean_inc(v___x_2049_);
v___x_2051_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2049_, v_numParams_2039_, v___x_2050_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2073_; 
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2073_ == 0)
{
lean_object* v_unused_2074_; 
v_unused_2074_ = lean_ctor_get(v___x_2051_, 0);
lean_dec(v_unused_2074_);
v___x_2053_ = v___x_2051_;
v_isShared_2054_ = v_isSharedCheck_2073_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v___x_2051_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2073_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2055_ = lean_box(0);
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = l_List_get_x21Internal___redArg(v___x_2055_, v_all_2040_, v___x_2056_);
lean_dec(v_all_2040_);
v___x_2058_ = lean_name_eq(v___x_2057_, v_indName_1812_);
lean_dec(v_indName_1812_);
lean_dec(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_dec(v___x_2050_);
lean_dec(v___x_2049_);
lean_dec(v_numNested_2041_);
lean_dec(v_numParams_2039_);
v___x_2059_ = lean_box(0);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2059_);
v___x_2061_ = v___x_2053_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; 
lean_del_object(v___x_2053_);
v___x_2063_ = lean_box(0);
v___x_2064_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(v_numNested_2041_, v___x_2049_, v___x_2050_, v_numParams_2039_, v___x_2056_, v___x_2063_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_numNested_2041_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2064_, 0);
lean_dec(v_unused_2072_);
v___x_2066_ = v___x_2064_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_dec(v___x_2064_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 0, v___x_2063_);
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2063_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
else
{
return v___x_2064_;
}
}
}
}
else
{
lean_dec(v___x_2050_);
lean_dec(v___x_2049_);
lean_dec(v_numNested_2041_);
lean_dec(v_all_2040_);
lean_dec(v_numParams_2039_);
lean_dec(v_indName_1812_);
return v___x_2051_;
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_dec(v_numNested_2041_);
lean_dec(v_all_2040_);
lean_dec(v_numParams_2039_);
lean_dec(v_indName_1812_);
v___x_2075_ = lean_box(0);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2075_);
v___x_2077_ = v___x_2046_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
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
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_numNested_2041_);
lean_dec(v_all_2040_);
lean_dec(v_numParams_2039_);
lean_dec(v_indName_1812_);
v_a_2080_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2043_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2043_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
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
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2090_; 
lean_dec(v_a_2028_);
lean_dec(v_indName_1812_);
v___x_2088_ = lean_box(0);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2088_);
v___x_2090_ = v___x_2030_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
return v___x_2090_;
}
}
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec(v_indName_1812_);
v_a_2093_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2027_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2027_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Lean_mkBelow(v_indName_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3(lean_object* v_00_u03b1_2108_, lean_object* v_x_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___redArg(v_x_2109_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_x_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2_spec__3(v_00_u03b1_2116_, v_x_2117_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3(lean_object* v_upperBound_2124_, lean_object* v___x_2125_, lean_object* v___x_2126_, lean_object* v___x_2127_, lean_object* v_inst_2128_, lean_object* v_R_2129_, lean_object* v_a_2130_, lean_object* v_b_2131_, lean_object* v_c_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___redArg(v_upperBound_2124_, v___x_2125_, v___x_2126_, v___x_2127_, v_a_2130_, v_b_2131_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_upperBound_2139_, lean_object* v___x_2140_, lean_object* v___x_2141_, lean_object* v___x_2142_, lean_object* v_inst_2143_, lean_object* v_R_2144_, lean_object* v_a_2145_, lean_object* v_b_2146_, lean_object* v_c_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__3(v_upperBound_2139_, v___x_2140_, v___x_2141_, v___x_2142_, v_inst_2143_, v_R_2144_, v_a_2145_, v_b_2146_, v_c_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v_upperBound_2139_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
if (lean_obj_tag(v_a_2154_) == 0)
{
lean_object* v___x_2156_; 
v___x_2156_ = l_List_reverse___redArg(v_a_2155_);
return v___x_2156_;
}
else
{
lean_object* v_head_2157_; lean_object* v_tail_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2167_; 
v_head_2157_ = lean_ctor_get(v_a_2154_, 0);
v_tail_2158_ = lean_ctor_get(v_a_2154_, 1);
v_isSharedCheck_2167_ = !lean_is_exclusive(v_a_2154_);
if (v_isSharedCheck_2167_ == 0)
{
v___x_2160_ = v_a_2154_;
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_tail_2158_);
lean_inc(v_head_2157_);
lean_dec(v_a_2154_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2167_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2162_ = l_Lean_MessageData_ofExpr(v_head_2157_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 1, v_a_2155_);
lean_ctor_set(v___x_2160_, 0, v___x_2162_);
v___x_2164_ = v___x_2160_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2166_, 1, v_a_2155_);
v___x_2164_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
v_a_2154_ = v_tail_2158_;
v_a_2155_ = v___x_2164_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2168_, lean_object* v_v_2169_, lean_object* v_i_2170_){
_start:
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = lean_array_get_size(v_xs_2168_);
v___x_2172_ = lean_nat_dec_lt(v_i_2170_, v___x_2171_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
lean_dec(v_i_2170_);
v___x_2173_ = lean_box(0);
return v___x_2173_;
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = lean_array_fget_borrowed(v_xs_2168_, v_i_2170_);
v___x_2175_ = lean_expr_eqv(v___x_2174_, v_v_2169_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_unsigned_to_nat(1u);
v___x_2177_ = lean_nat_add(v_i_2170_, v___x_2176_);
lean_dec(v_i_2170_);
v_i_2170_ = v___x_2177_;
goto _start;
}
else
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_i_2170_);
return v___x_2179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2180_, lean_object* v_v_2181_, lean_object* v_i_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2180_, v_v_2181_, v_i_2182_);
lean_dec_ref(v_v_2181_);
lean_dec_ref(v_xs_2180_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2184_, lean_object* v_v_2185_){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_unsigned_to_nat(0u);
v___x_2187_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2184_, v_v_2185_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2188_, lean_object* v_v_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2188_, v_v_2189_);
lean_dec_ref(v_v_2189_);
lean_dec_ref(v_xs_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2191_, lean_object* v_v_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2191_, v_v_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_box(0);
return v___x_2194_;
}
else
{
lean_object* v_val_2195_; lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2202_; 
v_val_2195_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2197_ = v___x_2193_;
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
else
{
lean_inc(v_val_2195_);
lean_dec(v___x_2193_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2202_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2200_; 
if (v_isShared_2198_ == 0)
{
v___x_2200_ = v___x_2197_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v_val_2195_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2203_, lean_object* v_v_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2203_, v_v_2204_);
lean_dec_ref(v_v_2204_);
lean_dec_ref(v_xs_2203_);
return v_res_2205_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2208_ = l_Lean_stringToMessageData(v___x_2207_);
return v___x_2208_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2210_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2211_ = l_Lean_stringToMessageData(v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2212_, lean_object* v_prods_2213_, lean_object* v_motives_2214_, lean_object* v_fs_2215_, lean_object* v_minor__type_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_x_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
if (lean_obj_tag(v_x_2217_) == 5)
{
lean_object* v_fn_2225_; lean_object* v_arg_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_fn_2225_ = lean_ctor_get(v_x_2217_, 0);
lean_inc_ref(v_fn_2225_);
v_arg_2226_ = lean_ctor_get(v_x_2217_, 1);
lean_inc_ref(v_arg_2226_);
lean_dec_ref_known(v_x_2217_, 2);
v___x_2227_ = lean_array_set(v_x_2218_, v_x_2219_, v_arg_2226_);
v___x_2228_ = lean_unsigned_to_nat(1u);
v___x_2229_ = lean_nat_sub(v_x_2219_, v___x_2228_);
lean_dec(v_x_2219_);
v_x_2217_ = v_fn_2225_;
v_x_2218_ = v___x_2227_;
v_x_2219_ = v___x_2229_;
goto _start;
}
else
{
lean_object* v___x_2231_; 
lean_dec(v_x_2219_);
v___x_2231_ = l_Lean_Meta_PProdN_mk(v_rlvl_2212_, v_prods_2213_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2233_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref_known(v___x_2231_, 1);
v___x_2233_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2214_, v_x_2217_);
lean_dec_ref(v_x_2217_);
if (lean_obj_tag(v___x_2233_) == 1)
{
lean_object* v_val_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v_minor__type_2216_);
lean_dec_ref(v_motives_2214_);
v_val_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_val_2234_);
lean_dec_ref_known(v___x_2233_, 1);
v___x_2235_ = l_Lean_instInhabitedExpr;
v___x_2236_ = lean_array_get_borrowed(v___x_2235_, v_fs_2215_, v_val_2234_);
lean_dec(v_val_2234_);
lean_inc(v_a_2232_);
v___x_2237_ = lean_array_push(v_x_2218_, v_a_2232_);
lean_inc(v___x_2236_);
v___x_2238_ = l_Lean_mkAppN(v___x_2236_, v___x_2237_);
lean_dec_ref(v___x_2237_);
v___x_2239_ = l_Lean_Meta_mkPProdMk(v___x_2238_, v_a_2232_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2239_;
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_dec(v___x_2233_);
lean_dec(v_a_2232_);
lean_dec_ref(v_x_2218_);
v___x_2240_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2241_ = l_Lean_MessageData_ofExpr(v_minor__type_2216_);
v___x_2242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2244_, 0, v___x_2242_);
lean_ctor_set(v___x_2244_, 1, v___x_2243_);
v___x_2245_ = lean_array_to_list(v_motives_2214_);
v___x_2246_ = lean_box(0);
v___x_2247_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2245_, v___x_2246_);
v___x_2248_ = l_Lean_MessageData_ofList(v___x_2247_);
v___x_2249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2244_);
lean_ctor_set(v___x_2249_, 1, v___x_2248_);
v___x_2250_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2249_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
return v___x_2250_;
}
}
else
{
lean_dec_ref(v_x_2218_);
lean_dec_ref(v_x_2217_);
lean_dec_ref(v_minor__type_2216_);
lean_dec_ref(v_motives_2214_);
return v___x_2231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2251_, lean_object* v_prods_2252_, lean_object* v_motives_2253_, lean_object* v_fs_2254_, lean_object* v_minor__type_2255_, lean_object* v_x_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2251_, v_prods_2252_, v_motives_2253_, v_fs_2254_, v_minor__type_2255_, v_x_2256_, v_x_2257_, v_x_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_fs_2254_);
return v_res_2264_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2265_; lean_object* v_dummy_2266_; 
v___x_2265_ = lean_box(0);
v_dummy_2266_ = l_Lean_Expr_sort___override(v___x_2265_);
return v_dummy_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2267_, lean_object* v_head_2268_, lean_object* v_belows_2269_, lean_object* v_prods_2270_, lean_object* v_rlvl_2271_, lean_object* v_fs_2272_, lean_object* v_minor__type_2273_, lean_object* v_tail_2274_, lean_object* v_arg__args_2275_, lean_object* v_arg__type_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2267_, v_head_2268_, v_belows_2269_, v_prods_2270_, v_rlvl_2271_, v_fs_2272_, v_minor__type_2273_, v_tail_2274_, v_arg__args_2275_, v_arg__type_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v_arg__args_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2283_, lean_object* v_motives_2284_, lean_object* v_belows_2285_, lean_object* v_fs_2286_, lean_object* v_minor__type_2287_, lean_object* v_prods_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_){
_start:
{
if (lean_obj_tag(v_a_2289_) == 0)
{
lean_object* v_dummy_2295_; lean_object* v_nargs_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec_ref(v_belows_2285_);
v_dummy_2295_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2296_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2287_);
lean_inc(v_nargs_2296_);
v___x_2297_ = lean_mk_array(v_nargs_2296_, v_dummy_2295_);
v___x_2298_ = lean_unsigned_to_nat(1u);
v___x_2299_ = lean_nat_sub(v_nargs_2296_, v___x_2298_);
lean_dec(v_nargs_2296_);
lean_inc_ref(v_minor__type_2287_);
v___x_2300_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2283_, v_prods_2288_, v_motives_2284_, v_fs_2286_, v_minor__type_2287_, v_minor__type_2287_, v___x_2297_, v___x_2299_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
lean_dec_ref(v_fs_2286_);
return v___x_2300_;
}
else
{
lean_object* v_head_2301_; lean_object* v_tail_2302_; lean_object* v___x_2303_; 
v_head_2301_ = lean_ctor_get(v_a_2289_, 0);
lean_inc_n(v_head_2301_, 2);
v_tail_2302_ = lean_ctor_get(v_a_2289_, 1);
lean_inc(v_tail_2302_);
lean_dec_ref_known(v_a_2289_, 2);
lean_inc(v_a_2293_);
lean_inc_ref(v_a_2292_);
lean_inc(v_a_2291_);
lean_inc_ref(v_a_2290_);
v___x_2303_ = lean_infer_type(v_head_2301_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___f_2305_; uint8_t v___x_2306_; lean_object* v___x_2307_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
v___f_2305_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2305_, 0, v_motives_2284_);
lean_closure_set(v___f_2305_, 1, v_head_2301_);
lean_closure_set(v___f_2305_, 2, v_belows_2285_);
lean_closure_set(v___f_2305_, 3, v_prods_2288_);
lean_closure_set(v___f_2305_, 4, v_rlvl_2283_);
lean_closure_set(v___f_2305_, 5, v_fs_2286_);
lean_closure_set(v___f_2305_, 6, v_minor__type_2287_);
lean_closure_set(v___f_2305_, 7, v_tail_2302_);
v___x_2306_ = 0;
v___x_2307_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2304_, v___f_2305_, v___x_2306_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_);
return v___x_2307_;
}
else
{
lean_dec(v_tail_2302_);
lean_dec(v_head_2301_);
lean_dec_ref(v_prods_2288_);
lean_dec_ref(v_minor__type_2287_);
lean_dec_ref(v_fs_2286_);
lean_dec_ref(v_belows_2285_);
lean_dec_ref(v_motives_2284_);
lean_dec(v_rlvl_2283_);
return v___x_2303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2308_, lean_object* v_rlvl_2309_, lean_object* v_motives_2310_, lean_object* v_belows_2311_, lean_object* v_fs_2312_, lean_object* v_minor__type_2313_, lean_object* v_tail_2314_, uint8_t v___x_2315_, uint8_t v___x_2316_, uint8_t v___x_2317_, lean_object* v_arg_x27_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_inc_ref(v_arg_x27_2318_);
v___x_2324_ = lean_array_push(v_prods_2308_, v_arg_x27_2318_);
v___x_2325_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2309_, v_motives_2310_, v_belows_2311_, v_fs_2312_, v_minor__type_2313_, v___x_2324_, v_tail_2314_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = lean_mk_empty_array_with_capacity(v___x_2327_);
v___x_2329_ = lean_array_push(v___x_2328_, v_arg_x27_2318_);
v___x_2330_ = l_Lean_Meta_mkLambdaFVars(v___x_2329_, v_a_2326_, v___x_2315_, v___x_2316_, v___x_2315_, v___x_2316_, v___x_2317_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec_ref(v___x_2329_);
return v___x_2330_;
}
else
{
lean_dec_ref(v_arg_x27_2318_);
return v___x_2325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2331_, lean_object* v_rlvl_2332_, lean_object* v_motives_2333_, lean_object* v_belows_2334_, lean_object* v_fs_2335_, lean_object* v_minor__type_2336_, lean_object* v_tail_2337_, lean_object* v___x_2338_, lean_object* v___x_2339_, lean_object* v___x_2340_, lean_object* v_arg_x27_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
uint8_t v___x_1774__boxed_2347_; uint8_t v___x_1775__boxed_2348_; uint8_t v___x_1776__boxed_2349_; lean_object* v_res_2350_; 
v___x_1774__boxed_2347_ = lean_unbox(v___x_2338_);
v___x_1775__boxed_2348_ = lean_unbox(v___x_2339_);
v___x_1776__boxed_2349_ = lean_unbox(v___x_2340_);
v_res_2350_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2331_, v_rlvl_2332_, v_motives_2333_, v_belows_2334_, v_fs_2335_, v_minor__type_2336_, v_tail_2337_, v___x_1774__boxed_2347_, v___x_1775__boxed_2348_, v___x_1776__boxed_2349_, v_arg_x27_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2351_, lean_object* v_head_2352_, lean_object* v_belows_2353_, lean_object* v_arg__type_2354_, lean_object* v_prods_2355_, lean_object* v_rlvl_2356_, lean_object* v_fs_2357_, lean_object* v_minor__type_2358_, lean_object* v_tail_2359_, lean_object* v_arg__args_2360_, lean_object* v_x_2361_, lean_object* v_x_2362_, lean_object* v_x_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
if (lean_obj_tag(v_x_2361_) == 5)
{
lean_object* v_fn_2369_; lean_object* v_arg_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_fn_2369_ = lean_ctor_get(v_x_2361_, 0);
lean_inc_ref(v_fn_2369_);
v_arg_2370_ = lean_ctor_get(v_x_2361_, 1);
lean_inc_ref(v_arg_2370_);
lean_dec_ref_known(v_x_2361_, 2);
v___x_2371_ = lean_array_set(v_x_2362_, v_x_2363_, v_arg_2370_);
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = lean_nat_sub(v_x_2363_, v___x_2372_);
lean_dec(v_x_2363_);
v_x_2361_ = v_fn_2369_;
v_x_2362_ = v___x_2371_;
v_x_2363_ = v___x_2373_;
goto _start;
}
else
{
lean_object* v___x_2375_; 
lean_dec(v_x_2363_);
v___x_2375_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2351_, v_x_2361_);
lean_dec_ref(v_x_2361_);
if (lean_obj_tag(v___x_2375_) == 1)
{
lean_object* v_val_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v_val_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_val_2376_);
lean_dec_ref_known(v___x_2375_, 1);
v___x_2377_ = l_Lean_Expr_fvarId_x21(v_head_2352_);
lean_dec_ref(v_head_2352_);
v___x_2378_ = l_Lean_FVarId_getUserName___redArg(v___x_2377_, v___y_2364_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v___x_2380_ = l_Lean_instInhabitedExpr;
v___x_2381_ = lean_array_get_borrowed(v___x_2380_, v_belows_2353_, v_val_2376_);
lean_dec(v_val_2376_);
lean_inc(v___x_2381_);
v___x_2382_ = l_Lean_mkAppN(v___x_2381_, v_x_2362_);
lean_dec_ref(v_x_2362_);
v___x_2383_ = l_Lean_Meta_mkPProd(v_arg__type_2354_, v___x_2382_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; uint8_t v___x_2385_; uint8_t v___x_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
lean_inc(v_a_2384_);
lean_dec_ref_known(v___x_2383_, 1);
v___x_2385_ = 0;
v___x_2386_ = 1;
v___x_2387_ = 1;
v___x_2388_ = l_Lean_Meta_mkForallFVars(v_arg__args_2360_, v_a_2384_, v___x_2385_, v___x_2386_, v___x_2386_, v___x_2387_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___f_2393_; lean_object* v___x_2394_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = lean_box(v___x_2385_);
v___x_2391_ = lean_box(v___x_2386_);
v___x_2392_ = lean_box(v___x_2387_);
v___f_2393_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2393_, 0, v_prods_2355_);
lean_closure_set(v___f_2393_, 1, v_rlvl_2356_);
lean_closure_set(v___f_2393_, 2, v_motives_2351_);
lean_closure_set(v___f_2393_, 3, v_belows_2353_);
lean_closure_set(v___f_2393_, 4, v_fs_2357_);
lean_closure_set(v___f_2393_, 5, v_minor__type_2358_);
lean_closure_set(v___f_2393_, 6, v_tail_2359_);
lean_closure_set(v___f_2393_, 7, v___x_2390_);
lean_closure_set(v___f_2393_, 8, v___x_2391_);
lean_closure_set(v___f_2393_, 9, v___x_2392_);
v___x_2394_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2379_, v_a_2389_, v___f_2393_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2394_;
}
else
{
lean_dec(v_a_2379_);
lean_dec(v_tail_2359_);
lean_dec_ref(v_minor__type_2358_);
lean_dec_ref(v_fs_2357_);
lean_dec(v_rlvl_2356_);
lean_dec_ref(v_prods_2355_);
lean_dec_ref(v_belows_2353_);
lean_dec_ref(v_motives_2351_);
return v___x_2388_;
}
}
else
{
lean_dec(v_a_2379_);
lean_dec(v_tail_2359_);
lean_dec_ref(v_minor__type_2358_);
lean_dec_ref(v_fs_2357_);
lean_dec(v_rlvl_2356_);
lean_dec_ref(v_prods_2355_);
lean_dec_ref(v_belows_2353_);
lean_dec_ref(v_motives_2351_);
return v___x_2383_;
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_val_2376_);
lean_dec_ref(v_x_2362_);
lean_dec(v_tail_2359_);
lean_dec_ref(v_minor__type_2358_);
lean_dec_ref(v_fs_2357_);
lean_dec(v_rlvl_2356_);
lean_dec_ref(v_prods_2355_);
lean_dec_ref(v_arg__type_2354_);
lean_dec_ref(v_belows_2353_);
lean_dec_ref(v_motives_2351_);
v_a_2395_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2378_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2378_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
else
{
lean_object* v___x_2403_; 
lean_dec(v___x_2375_);
lean_dec_ref(v_x_2362_);
lean_dec_ref(v_arg__type_2354_);
v___x_2403_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2356_, v_motives_2351_, v_belows_2353_, v_fs_2357_, v_minor__type_2358_, v_prods_2355_, v_tail_2359_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; uint8_t v___x_2409_; uint8_t v___x_2410_; lean_object* v___x_2411_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_mk_empty_array_with_capacity(v___x_2405_);
v___x_2407_ = lean_array_push(v___x_2406_, v_head_2352_);
v___x_2408_ = 0;
v___x_2409_ = 1;
v___x_2410_ = 1;
v___x_2411_ = l_Lean_Meta_mkLambdaFVars(v___x_2407_, v_a_2404_, v___x_2408_, v___x_2409_, v___x_2408_, v___x_2409_, v___x_2410_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec_ref(v___x_2407_);
return v___x_2411_;
}
else
{
lean_dec_ref(v_head_2352_);
return v___x_2403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2412_, lean_object* v_head_2413_, lean_object* v_belows_2414_, lean_object* v_prods_2415_, lean_object* v_rlvl_2416_, lean_object* v_fs_2417_, lean_object* v_minor__type_2418_, lean_object* v_tail_2419_, lean_object* v_arg__args_2420_, lean_object* v_arg__type_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_dummy_2427_; lean_object* v_nargs_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_dummy_2427_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2428_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2421_);
lean_inc(v_nargs_2428_);
v___x_2429_ = lean_mk_array(v_nargs_2428_, v_dummy_2427_);
v___x_2430_ = lean_unsigned_to_nat(1u);
v___x_2431_ = lean_nat_sub(v_nargs_2428_, v___x_2430_);
lean_dec(v_nargs_2428_);
lean_inc_ref(v_arg__type_2421_);
v___x_2432_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2412_, v_head_2413_, v_belows_2414_, v_arg__type_2421_, v_prods_2415_, v_rlvl_2416_, v_fs_2417_, v_minor__type_2418_, v_tail_2419_, v_arg__args_2420_, v_arg__type_2421_, v___x_2429_, v___x_2431_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2433_, lean_object* v_motives_2434_, lean_object* v_belows_2435_, lean_object* v_fs_2436_, lean_object* v_minor__type_2437_, lean_object* v_prods_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2433_, v_motives_2434_, v_belows_2435_, v_fs_2436_, v_minor__type_2437_, v_prods_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
lean_dec(v_a_2441_);
lean_dec_ref(v_a_2440_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2446_ = _args[0];
lean_object* v_head_2447_ = _args[1];
lean_object* v_belows_2448_ = _args[2];
lean_object* v_arg__type_2449_ = _args[3];
lean_object* v_prods_2450_ = _args[4];
lean_object* v_rlvl_2451_ = _args[5];
lean_object* v_fs_2452_ = _args[6];
lean_object* v_minor__type_2453_ = _args[7];
lean_object* v_tail_2454_ = _args[8];
lean_object* v_arg__args_2455_ = _args[9];
lean_object* v_x_2456_ = _args[10];
lean_object* v_x_2457_ = _args[11];
lean_object* v_x_2458_ = _args[12];
lean_object* v___y_2459_ = _args[13];
lean_object* v___y_2460_ = _args[14];
lean_object* v___y_2461_ = _args[15];
lean_object* v___y_2462_ = _args[16];
lean_object* v___y_2463_ = _args[17];
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2446_, v_head_2447_, v_belows_2448_, v_arg__type_2449_, v_prods_2450_, v_rlvl_2451_, v_fs_2452_, v_minor__type_2453_, v_tail_2454_, v_arg__args_2455_, v_x_2456_, v_x_2457_, v_x_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec_ref(v_arg__args_2455_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2465_, lean_object* v_motives_2466_, lean_object* v_belows_2467_, lean_object* v_fs_2468_, lean_object* v_minor__args_2469_, lean_object* v_minor__type_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2477_ = lean_array_to_list(v_minor__args_2469_);
v___x_2478_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2465_, v_motives_2466_, v_belows_2467_, v_fs_2468_, v_minor__type_2470_, v___x_2476_, v___x_2477_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2479_, lean_object* v_motives_2480_, lean_object* v_belows_2481_, lean_object* v_fs_2482_, lean_object* v_minor__args_2483_, lean_object* v_minor__type_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2479_, v_motives_2480_, v_belows_2481_, v_fs_2482_, v_minor__args_2483_, v_minor__type_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2491_, lean_object* v_motives_2492_, lean_object* v_belows_2493_, lean_object* v_fs_2494_, lean_object* v_minorType_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v___f_2501_; uint8_t v___x_2502_; lean_object* v___x_2503_; 
v___f_2501_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2501_, 0, v_rlvl_2491_);
lean_closure_set(v___f_2501_, 1, v_motives_2492_);
lean_closure_set(v___f_2501_, 2, v_belows_2493_);
lean_closure_set(v___f_2501_, 3, v_fs_2494_);
v___x_2502_ = 0;
v___x_2503_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2495_, v___f_2501_, v___x_2502_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2504_, lean_object* v_motives_2505_, lean_object* v_belows_2506_, lean_object* v_fs_2507_, lean_object* v_minorType_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2504_, v_motives_2505_, v_belows_2506_, v_fs_2507_, v_minorType_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_){
_start:
{
lean_object* v___f_2521_; lean_object* v___x_27349__overap_2522_; lean_object* v___x_2523_; 
v___f_2521_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27349__overap_2522_ = lean_panic_fn_borrowed(v___f_2521_, v_msg_2515_);
lean_inc(v___y_2519_);
lean_inc_ref(v___y_2518_);
lean_inc(v___y_2517_);
lean_inc_ref(v___y_2516_);
v___x_2523_ = lean_apply_5(v___x_27349__overap_2522_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, lean_box(0));
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___y_2526_);
lean_dec_ref(v___y_2525_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = l_Lean_Expr_hasMVar(v_e_2531_);
v___x_2535_ = lean_bool_not(v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v_mctx_2537_; lean_object* v___x_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; lean_object* v___x_2541_; lean_object* v_cache_2542_; lean_object* v_zetaDeltaFVarIds_2543_; lean_object* v_postponed_2544_; lean_object* v_diag_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2554_; 
v___x_2536_ = lean_st_ref_get(v___y_2532_);
v_mctx_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_mctx_2537_);
lean_dec(v___x_2536_);
v___x_2538_ = l_Lean_instantiateMVarsCore(v_mctx_2537_, v_e_2531_);
v_fst_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_fst_2539_);
v_snd_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_snd_2540_);
lean_dec_ref(v___x_2538_);
v___x_2541_ = lean_st_ref_take(v___y_2532_);
v_cache_2542_ = lean_ctor_get(v___x_2541_, 1);
v_zetaDeltaFVarIds_2543_ = lean_ctor_get(v___x_2541_, 2);
v_postponed_2544_ = lean_ctor_get(v___x_2541_, 3);
v_diag_2545_ = lean_ctor_get(v___x_2541_, 4);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2554_ == 0)
{
lean_object* v_unused_2555_; 
v_unused_2555_ = lean_ctor_get(v___x_2541_, 0);
lean_dec(v_unused_2555_);
v___x_2547_ = v___x_2541_;
v_isShared_2548_ = v_isSharedCheck_2554_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_diag_2545_);
lean_inc(v_postponed_2544_);
lean_inc(v_zetaDeltaFVarIds_2543_);
lean_inc(v_cache_2542_);
lean_dec(v___x_2541_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2554_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v_snd_2540_);
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_snd_2540_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v_cache_2542_);
lean_ctor_set(v_reuseFailAlloc_2553_, 2, v_zetaDeltaFVarIds_2543_);
lean_ctor_set(v_reuseFailAlloc_2553_, 3, v_postponed_2544_);
lean_ctor_set(v_reuseFailAlloc_2553_, 4, v_diag_2545_);
v___x_2550_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_st_ref_set(v___y_2532_, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v_fst_2539_);
return v___x_2552_;
}
}
}
else
{
lean_object* v___x_2556_; 
v___x_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2556_, 0, v_e_2531_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2557_, v___y_2558_);
lean_dec(v___y_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
v___x_2567_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2561_, v___y_2563_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; lean_object* v_env_2579_; lean_object* v_toConstantVal_2580_; lean_object* v_value_2581_; lean_object* v_all_2582_; uint8_t v___y_2584_; lean_object* v_type_2592_; uint8_t v___x_2593_; 
v___x_2578_ = lean_st_ref_get(v___y_2576_);
v_env_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc_ref_n(v_env_2579_, 2);
lean_dec(v___x_2578_);
v_toConstantVal_2580_ = lean_ctor_get(v_thm_2575_, 0);
v_value_2581_ = lean_ctor_get(v_thm_2575_, 1);
v_all_2582_ = lean_ctor_get(v_thm_2575_, 2);
v_type_2592_ = lean_ctor_get(v_toConstantVal_2580_, 2);
v___x_2593_ = l_Lean_Environment_hasUnsafe(v_env_2579_, v_type_2592_);
if (v___x_2593_ == 0)
{
uint8_t v___x_2594_; 
v___x_2594_ = l_Lean_Environment_hasUnsafe(v_env_2579_, v_value_2581_);
v___y_2584_ = v___x_2594_;
goto v___jp_2583_;
}
else
{
lean_dec_ref(v_env_2579_);
v___y_2584_ = v___x_2593_;
goto v___jp_2583_;
}
v___jp_2583_:
{
if (v___y_2584_ == 0)
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2585_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_thm_2575_);
v___x_2586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_inc(v_all_2582_);
lean_inc_ref(v_value_2581_);
lean_inc_ref(v_toConstantVal_2580_);
lean_dec_ref(v_thm_2575_);
v___x_2587_ = lean_box(0);
v___x_2588_ = 0;
v___x_2589_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2589_, 0, v_toConstantVal_2580_);
lean_ctor_set(v___x_2589_, 1, v_value_2581_);
lean_ctor_set(v___x_2589_, 2, v___x_2587_);
lean_ctor_set(v___x_2589_, 3, v_all_2582_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*4, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2595_, v___y_2596_);
lean_dec(v___y_2596_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2599_, v___y_2603_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2614_, lean_object* v___x_2615_, lean_object* v___x_2616_, lean_object* v_all_2617_, lean_object* v___x_2618_, lean_object* v___x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v___y_2622_; lean_object* v___x_2626_; uint8_t v___x_2627_; 
v___x_2626_ = lean_array_get_size(v_all_2617_);
v___x_2627_ = lean_nat_dec_lt(v_x_2620_, v___x_2626_);
if (v___x_2627_ == 0)
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2628_ = lean_box(0);
v___x_2629_ = lean_array_get_borrowed(v___x_2628_, v_all_2617_, v___x_2618_);
v___x_2630_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2631_ = lean_nat_sub(v_x_2620_, v___x_2626_);
v___x_2632_ = lean_nat_add(v___x_2631_, v___x_2619_);
lean_dec(v___x_2631_);
v___x_2633_ = l_Nat_reprFast(v___x_2632_);
v___x_2634_ = lean_string_append(v___x_2630_, v___x_2633_);
lean_dec_ref(v___x_2633_);
lean_inc(v___x_2629_);
v___x_2635_ = l_Lean_Name_str___override(v___x_2629_, v___x_2634_);
v___y_2622_ = v___x_2635_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = lean_array_fget_borrowed(v_all_2617_, v_x_2620_);
lean_inc(v___x_2636_);
v___x_2637_ = l_Lean_mkBelowName(v___x_2636_);
v___y_2622_ = v___x_2637_;
goto v___jp_2621_;
}
v___jp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = l_Lean_Expr_const___override(v___y_2622_, v___x_2614_);
v___x_2624_ = l_Array_append___redArg(v___x_2615_, v___x_2616_);
v___x_2625_ = l_Lean_mkAppN(v___x_2623_, v___x_2624_);
lean_dec_ref(v___x_2624_);
return v___x_2625_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2638_, lean_object* v___x_2639_, lean_object* v___x_2640_, lean_object* v_all_2641_, lean_object* v___x_2642_, lean_object* v___x_2643_, lean_object* v_x_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2638_, v___x_2639_, v___x_2640_, v_all_2641_, v___x_2642_, v___x_2643_, v_x_2644_);
lean_dec(v_x_2644_);
lean_dec(v___x_2643_);
lean_dec(v___x_2642_);
lean_dec_ref(v_all_2641_);
lean_dec_ref(v___x_2640_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2646_, lean_object* v___x_2647_, uint8_t v___x_2648_, lean_object* v_targs_2649_, lean_object* v_x_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2656_ = l_Lean_mkAppN(v_a_2646_, v_targs_2649_);
v___x_2657_ = l_Lean_mkAppN(v___x_2647_, v_targs_2649_);
v___x_2658_ = l_Lean_Meta_mkPProd(v___x_2656_, v___x_2657_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; uint8_t v___x_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = 0;
v___x_2661_ = 1;
v___x_2662_ = l_Lean_Meta_mkLambdaFVars(v_targs_2649_, v_a_2659_, v___x_2660_, v___x_2648_, v___x_2660_, v___x_2648_, v___x_2661_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
return v___x_2662_;
}
else
{
return v___x_2658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2663_, lean_object* v___x_2664_, lean_object* v___x_2665_, lean_object* v_targs_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
uint8_t v___x_30515__boxed_2673_; lean_object* v_res_2674_; 
v___x_30515__boxed_2673_ = lean_unbox(v___x_2665_);
v_res_2674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2663_, v___x_2664_, v___x_30515__boxed_2673_, v_targs_2666_, v_x_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec_ref(v_x_2667_);
lean_dec_ref(v_targs_2666_);
return v_res_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v_as_2675_, size_t v_sz_2676_, size_t v_i_2677_, lean_object* v_b_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v___x_2684_; 
v___x_2684_ = lean_usize_dec_lt(v_i_2677_, v_sz_2676_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_b_2678_);
return v___x_2685_;
}
else
{
lean_object* v_snd_2686_; lean_object* v_fst_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2743_; 
v_snd_2686_ = lean_ctor_get(v_b_2678_, 1);
v_fst_2687_ = lean_ctor_get(v_b_2678_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_b_2678_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2689_ = v_b_2678_;
v_isShared_2690_ = v_isSharedCheck_2743_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_snd_2686_);
lean_inc(v_fst_2687_);
lean_dec(v_b_2678_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2743_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v_array_2691_; lean_object* v_start_2692_; lean_object* v_stop_2693_; uint8_t v___x_2694_; 
v_array_2691_ = lean_ctor_get(v_snd_2686_, 0);
v_start_2692_ = lean_ctor_get(v_snd_2686_, 1);
v_stop_2693_ = lean_ctor_get(v_snd_2686_, 2);
v___x_2694_ = lean_nat_dec_lt(v_start_2692_, v_stop_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2696_; 
if (v_isShared_2690_ == 0)
{
v___x_2696_ = v___x_2689_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_fst_2687_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_snd_2686_);
v___x_2696_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
return v___x_2697_;
}
}
else
{
lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2739_; 
lean_inc(v_stop_2693_);
lean_inc(v_start_2692_);
lean_inc_ref(v_array_2691_);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_snd_2686_);
if (v_isSharedCheck_2739_ == 0)
{
lean_object* v_unused_2740_; lean_object* v_unused_2741_; lean_object* v_unused_2742_; 
v_unused_2740_ = lean_ctor_get(v_snd_2686_, 2);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_snd_2686_, 1);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_snd_2686_, 0);
lean_dec(v_unused_2742_);
v___x_2700_ = v_snd_2686_;
v_isShared_2701_ = v_isSharedCheck_2739_;
goto v_resetjp_2699_;
}
else
{
lean_dec(v_snd_2686_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2739_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_a_2702_; lean_object* v___x_2703_; 
v_a_2702_ = lean_array_uget_borrowed(v_as_2675_, v_i_2677_);
lean_inc(v___y_2682_);
lean_inc_ref(v___y_2681_);
lean_inc(v___y_2680_);
lean_inc_ref(v___y_2679_);
lean_inc(v_a_2702_);
v___x_2703_ = lean_infer_type(v_a_2702_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___f_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v___x_2705_ = lean_array_fget_borrowed(v_array_2691_, v_start_2692_);
v___x_2706_ = lean_box(v___x_2694_);
lean_inc(v___x_2705_);
lean_inc(v_a_2702_);
v___f_2707_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2707_, 0, v_a_2702_);
lean_closure_set(v___f_2707_, 1, v___x_2705_);
lean_closure_set(v___f_2707_, 2, v___x_2706_);
v___x_2708_ = 0;
v___x_2709_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2704_, v___f_2707_, v___x_2708_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v_a_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2709_, 1);
v___x_2711_ = lean_unsigned_to_nat(1u);
v___x_2712_ = lean_nat_add(v_start_2692_, v___x_2711_);
lean_dec(v_start_2692_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2712_);
v___x_2714_ = v___x_2700_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_array_2691_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v_stop_2693_);
v___x_2714_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = l_Lean_Expr_app___override(v_fst_2687_, v_a_2710_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 1, v___x_2714_);
lean_ctor_set(v___x_2689_, 0, v___x_2715_);
v___x_2717_ = v___x_2689_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2714_);
v___x_2717_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
size_t v___x_2718_; size_t v___x_2719_; 
v___x_2718_ = ((size_t)1ULL);
v___x_2719_ = lean_usize_add(v_i_2677_, v___x_2718_);
v_i_2677_ = v___x_2719_;
v_b_2678_ = v___x_2717_;
goto _start;
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_del_object(v___x_2700_);
lean_dec(v_stop_2693_);
lean_dec(v_start_2692_);
lean_dec_ref(v_array_2691_);
lean_del_object(v___x_2689_);
lean_dec(v_fst_2687_);
v_a_2723_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2709_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2709_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_del_object(v___x_2700_);
lean_dec(v_stop_2693_);
lean_dec(v_start_2692_);
lean_dec_ref(v_array_2691_);
lean_del_object(v___x_2689_);
lean_dec(v_fst_2687_);
v_a_2731_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2703_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2703_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v_as_2744_, lean_object* v_sz_2745_, lean_object* v_i_2746_, lean_object* v_b_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
size_t v_sz_boxed_2753_; size_t v_i_boxed_2754_; lean_object* v_res_2755_; 
v_sz_boxed_2753_ = lean_unbox_usize(v_sz_2745_);
lean_dec(v_sz_2745_);
v_i_boxed_2754_ = lean_unbox_usize(v_i_2746_);
lean_dec(v_i_2746_);
v_res_2755_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v_as_2744_, v_sz_boxed_2753_, v_i_boxed_2754_, v_b_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec_ref(v_as_2744_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2756_, size_t v_sz_2757_, size_t v_i_2758_, lean_object* v_b_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_usize_dec_lt(v_i_2758_, v_sz_2757_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_b_2759_);
return v___x_2766_;
}
else
{
lean_object* v_a_2767_; lean_object* v_toInductionSubgoal_2768_; lean_object* v_mvarId_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; 
v_a_2767_ = lean_array_uget_borrowed(v_as_2756_, v_i_2758_);
v_toInductionSubgoal_2768_ = lean_ctor_get(v_a_2767_, 0);
v_mvarId_2769_ = lean_ctor_get(v_toInductionSubgoal_2768_, 0);
v___x_2770_ = 0;
lean_inc(v_mvarId_2769_);
v___x_2771_ = l_Lean_MVarId_refl(v_mvarId_2769_, v___x_2770_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v___x_2772_; size_t v___x_2773_; size_t v___x_2774_; 
lean_dec_ref_known(v___x_2771_, 1);
v___x_2772_ = lean_box(0);
v___x_2773_ = ((size_t)1ULL);
v___x_2774_ = lean_usize_add(v_i_2758_, v___x_2773_);
v_i_2758_ = v___x_2774_;
v_b_2759_ = v___x_2772_;
goto _start;
}
else
{
return v___x_2771_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2776_, lean_object* v_sz_2777_, lean_object* v_i_2778_, lean_object* v_b_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
size_t v_sz_boxed_2785_; size_t v_i_boxed_2786_; lean_object* v_res_2787_; 
v_sz_boxed_2785_ = lean_unbox_usize(v_sz_2777_);
lean_dec(v_sz_2777_);
v_i_boxed_2786_ = lean_unbox_usize(v_i_2778_);
lean_dec(v_i_2778_);
v_res_2787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2776_, v_sz_boxed_2785_, v_i_boxed_2786_, v_b_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
lean_dec_ref(v_as_2776_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2788_, lean_object* v___x_2789_, lean_object* v___x_2790_, lean_object* v_fs_2791_, lean_object* v_as_2792_, size_t v_sz_2793_, size_t v_i_2794_, lean_object* v_b_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
uint8_t v___x_2801_; 
v___x_2801_ = lean_usize_dec_lt(v_i_2794_, v_sz_2793_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; 
lean_dec_ref(v_fs_2791_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v___x_2789_);
lean_dec(v___x_2788_);
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_b_2795_);
return v___x_2802_;
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2804_; 
v_a_2803_ = lean_array_uget_borrowed(v_as_2792_, v_i_2794_);
lean_inc(v___y_2799_);
lean_inc_ref(v___y_2798_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v_a_2803_);
v___x_2804_ = lean_infer_type(v_a_2803_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
lean_inc_ref(v_fs_2791_);
lean_inc_ref(v___x_2790_);
lean_inc_ref(v___x_2789_);
lean_inc(v___x_2788_);
v___x_2806_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2788_, v___x_2789_, v___x_2790_, v_fs_2791_, v_a_2805_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = l_Lean_Expr_app___override(v_b_2795_, v_a_2807_);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_add(v_i_2794_, v___x_2809_);
v_i_2794_ = v___x_2810_;
v_b_2795_ = v___x_2808_;
goto _start;
}
else
{
lean_dec_ref(v_b_2795_);
lean_dec_ref(v_fs_2791_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v___x_2789_);
lean_dec(v___x_2788_);
return v___x_2806_;
}
}
else
{
lean_dec_ref(v_b_2795_);
lean_dec_ref(v_fs_2791_);
lean_dec_ref(v___x_2790_);
lean_dec_ref(v___x_2789_);
lean_dec(v___x_2788_);
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v___x_2814_, lean_object* v_fs_2815_, lean_object* v_as_2816_, lean_object* v_sz_2817_, lean_object* v_i_2818_, lean_object* v_b_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
size_t v_sz_boxed_2825_; size_t v_i_boxed_2826_; lean_object* v_res_2827_; 
v_sz_boxed_2825_ = lean_unbox_usize(v_sz_2817_);
lean_dec(v_sz_2817_);
v_i_boxed_2826_ = lean_unbox_usize(v_i_2818_);
lean_dec(v_i_2818_);
v_res_2827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2812_, v___x_2813_, v___x_2814_, v_fs_2815_, v_as_2816_, v_sz_boxed_2825_, v_i_boxed_2826_, v_b_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec_ref(v_as_2816_);
return v_res_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2828_, lean_object* v_tail_2829_, lean_object* v_recName_2830_, lean_object* v___x_2831_, lean_object* v___x_2832_, lean_object* v___x_2833_, size_t v_sz_2834_, size_t v___x_2835_, lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v___x_2838_, lean_object* v___x_2839_, lean_object* v___x_2840_, lean_object* v___x_2841_, lean_object* v_val_2842_, uint8_t v___x_2843_, lean_object* v_brecOnGoName_2844_, lean_object* v_levelParams_2845_, lean_object* v___x_2846_, lean_object* v_brecOnName_2847_, lean_object* v___x_2848_, lean_object* v_brecOnEqName_2849_, lean_object* v_fs_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_inc(v___x_2828_);
v___x_2856_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2828_);
lean_ctor_set(v___x_2856_, 1, v_tail_2829_);
v___x_2857_ = l_Lean_Expr_const___override(v_recName_2830_, v___x_2856_);
v___x_2858_ = l_Lean_mkAppN(v___x_2857_, v___x_2831_);
v___x_2859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
lean_ctor_set(v___x_2859_, 1, v___x_2832_);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2833_, v_sz_2834_, v___x_2835_, v___x_2859_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v_fst_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_3223_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v_fst_2862_ = lean_ctor_get(v_a_2861_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v_a_2861_);
if (v_isSharedCheck_3223_ == 0)
{
lean_object* v_unused_3224_; 
v_unused_3224_ = lean_ctor_get(v_a_2861_, 1);
lean_dec(v_unused_3224_);
v___x_2864_ = v_a_2861_;
v_isShared_2865_ = v_isSharedCheck_3223_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_fst_2862_);
lean_dec(v_a_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_3223_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
size_t v_sz_2866_; lean_object* v___x_2867_; 
v_sz_2866_ = lean_array_size(v___x_2836_);
lean_inc_ref(v_fs_2850_);
lean_inc_ref(v___x_2837_);
lean_inc_ref(v___x_2833_);
v___x_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2828_, v___x_2833_, v___x_2837_, v_fs_2850_, v___x_2836_, v_sz_2866_, v___x_2835_, v_fst_2862_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
v___x_2869_ = l_Lean_mkAppN(v_a_2868_, v___x_2838_);
lean_inc_ref_n(v___x_2839_, 3);
v___x_2870_ = l_Lean_Expr_app___override(v___x_2869_, v___x_2839_);
v___x_2871_ = l_Array_append___redArg(v___x_2831_, v___x_2833_);
v___x_2872_ = l_Array_append___redArg(v___x_2871_, v___x_2838_);
v___x_2873_ = lean_mk_empty_array_with_capacity(v___x_2840_);
v___x_2874_ = lean_array_push(v___x_2873_, v___x_2839_);
v___x_2875_ = lean_array_get(v___x_2841_, v___x_2833_, v_val_2842_);
lean_dec_ref(v___x_2833_);
v___x_2876_ = lean_array_push(v___x_2838_, v___x_2839_);
v___x_2877_ = l_Lean_mkAppN(v___x_2875_, v___x_2876_);
v___x_2878_ = lean_array_get(v___x_2841_, v___x_2837_, v_val_2842_);
lean_dec_ref(v___x_2837_);
v___x_2879_ = l_Lean_mkAppN(v___x_2878_, v___x_2876_);
lean_inc_ref(v___x_2877_);
v___x_2880_ = l_Lean_Meta_mkPProd(v___x_2877_, v___x_2879_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; uint8_t v___x_2885_; lean_object* v___x_2886_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
v___x_2882_ = l_Array_append___redArg(v___x_2872_, v___x_2874_);
lean_dec_ref(v___x_2874_);
v___x_2883_ = l_Array_append___redArg(v___x_2882_, v_fs_2850_);
v___x_2884_ = 0;
v___x_2885_ = 1;
v___x_2886_ = l_Lean_Meta_mkForallFVars(v___x_2883_, v_a_2881_, v___x_2884_, v___x_2843_, v___x_2843_, v___x_2885_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; lean_object* v___x_2888_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
v___x_2888_ = l_Lean_Meta_mkLambdaFVars(v___x_2883_, v___x_2870_, v___x_2884_, v___x_2843_, v___x_2884_, v___x_2843_, v___x_2885_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_3190_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
v___x_2890_ = lean_box(1);
lean_inc(v_levelParams_2845_);
lean_inc(v_brecOnGoName_2844_);
v___x_2891_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2844_, v_levelParams_2845_, v_a_2887_, v_a_2889_, v___x_2890_, v___y_2854_);
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_3190_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_3190_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
lean_inc(v_a_2892_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set_tag(v___x_2894_, 1);
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_3189_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean_addDecl(v___x_2897_, v___x_2884_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_toConstantVal_2899_; lean_object* v_name_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref_known(v___x_2898_, 1);
v_toConstantVal_2899_ = lean_ctor_get(v_a_2892_, 0);
lean_inc_ref(v_toConstantVal_2899_);
lean_dec(v_a_2892_);
v_name_2900_ = lean_ctor_get(v_toConstantVal_2899_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_toConstantVal_2899_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; lean_object* v_unused_3188_; 
v_unused_3187_ = lean_ctor_get(v_toConstantVal_2899_, 2);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_toConstantVal_2899_, 1);
lean_dec(v_unused_3188_);
v___x_2902_ = v_toConstantVal_2899_;
v_isShared_2903_ = v_isSharedCheck_3186_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_name_2900_);
lean_dec(v_toConstantVal_2899_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_3186_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v_env_2906_; lean_object* v_nextMacroScope_2907_; lean_object* v_ngen_2908_; lean_object* v_auxDeclNGen_2909_; lean_object* v_traceState_2910_; lean_object* v_messages_2911_; lean_object* v_infoState_2912_; lean_object* v_snapshotTasks_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_3184_; 
lean_inc(v_name_2900_);
v___x_2904_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2900_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v___x_2904_);
v___x_2905_ = lean_st_ref_take(v___y_2854_);
v_env_2906_ = lean_ctor_get(v___x_2905_, 0);
v_nextMacroScope_2907_ = lean_ctor_get(v___x_2905_, 1);
v_ngen_2908_ = lean_ctor_get(v___x_2905_, 2);
v_auxDeclNGen_2909_ = lean_ctor_get(v___x_2905_, 3);
v_traceState_2910_ = lean_ctor_get(v___x_2905_, 4);
v_messages_2911_ = lean_ctor_get(v___x_2905_, 6);
v_infoState_2912_ = lean_ctor_get(v___x_2905_, 7);
v_snapshotTasks_2913_ = lean_ctor_get(v___x_2905_, 8);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; 
v_unused_3185_ = lean_ctor_get(v___x_2905_, 5);
lean_dec(v_unused_3185_);
v___x_2915_ = v___x_2905_;
v_isShared_2916_ = v_isSharedCheck_3184_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_snapshotTasks_2913_);
lean_inc(v_infoState_2912_);
lean_inc(v_messages_2911_);
lean_inc(v_traceState_2910_);
lean_inc(v_auxDeclNGen_2909_);
lean_inc(v_ngen_2908_);
lean_inc(v_nextMacroScope_2907_);
lean_inc(v_env_2906_);
lean_dec(v___x_2905_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_3184_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
v___x_2917_ = l_Lean_addProtected(v_env_2906_, v_name_2900_);
v___x_2918_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 5, v___x_2918_);
lean_ctor_set(v___x_2915_, 0, v___x_2917_);
v___x_2920_ = v___x_2915_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_nextMacroScope_2907_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_ngen_2908_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_auxDeclNGen_2909_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_traceState_2910_);
lean_ctor_set(v_reuseFailAlloc_3183_, 5, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3183_, 6, v_messages_2911_);
lean_ctor_set(v_reuseFailAlloc_3183_, 7, v_infoState_2912_);
lean_ctor_set(v_reuseFailAlloc_3183_, 8, v_snapshotTasks_2913_);
v___x_2920_ = v_reuseFailAlloc_3183_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v_mctx_2923_; lean_object* v_zetaDeltaFVarIds_2924_; lean_object* v_postponed_2925_; lean_object* v_diag_2926_; lean_object* v___x_2928_; uint8_t v_isShared_2929_; uint8_t v_isSharedCheck_3181_; 
v___x_2921_ = lean_st_ref_set(v___y_2854_, v___x_2920_);
v___x_2922_ = lean_st_ref_take(v___y_2852_);
v_mctx_2923_ = lean_ctor_get(v___x_2922_, 0);
v_zetaDeltaFVarIds_2924_ = lean_ctor_get(v___x_2922_, 2);
v_postponed_2925_ = lean_ctor_get(v___x_2922_, 3);
v_diag_2926_ = lean_ctor_get(v___x_2922_, 4);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; 
v_unused_3182_ = lean_ctor_get(v___x_2922_, 1);
lean_dec(v_unused_3182_);
v___x_2928_ = v___x_2922_;
v_isShared_2929_ = v_isSharedCheck_3181_;
goto v_resetjp_2927_;
}
else
{
lean_inc(v_diag_2926_);
lean_inc(v_postponed_2925_);
lean_inc(v_zetaDeltaFVarIds_2924_);
lean_inc(v_mctx_2923_);
lean_dec(v___x_2922_);
v___x_2928_ = lean_box(0);
v_isShared_2929_ = v_isSharedCheck_3181_;
goto v_resetjp_2927_;
}
v_resetjp_2927_:
{
lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2930_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2929_ == 0)
{
lean_ctor_set(v___x_2928_, 1, v___x_2930_);
v___x_2932_ = v___x_2928_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_mctx_2923_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v_zetaDeltaFVarIds_2924_);
lean_ctor_set(v_reuseFailAlloc_3180_, 3, v_postponed_2925_);
lean_ctor_set(v_reuseFailAlloc_3180_, 4, v_diag_2926_);
v___x_2932_ = v_reuseFailAlloc_3180_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2933_ = lean_st_ref_set(v___y_2852_, v___x_2932_);
lean_inc(v___x_2846_);
v___x_2934_ = l_Lean_Expr_const___override(v_brecOnGoName_2844_, v___x_2846_);
v___x_2935_ = l_Lean_mkAppN(v___x_2934_, v___x_2883_);
lean_inc_ref(v___x_2935_);
v___x_2936_ = l_Lean_Meta_mkPProdFstM(v___x_2935_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = l_Lean_Meta_mkLambdaFVars(v___x_2883_, v_a_2937_, v___x_2884_, v___x_2843_, v___x_2884_, v___x_2843_, v___x_2885_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v___x_2940_ = l_Lean_Meta_mkForallFVars(v___x_2883_, v___x_2877_, v___x_2884_, v___x_2843_, v___x_2843_, v___x_2885_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2942_; lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3155_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
lean_inc(v_levelParams_2845_);
v___x_2942_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2847_, v_levelParams_2845_, v_a_2941_, v_a_2939_, v___x_2890_, v___y_2854_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_3155_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3155_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
lean_inc(v_a_2943_);
if (v_isShared_2946_ == 0)
{
lean_ctor_set_tag(v___x_2945_, 1);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_3154_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_addDecl(v___x_2948_, v___x_2884_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_toConstantVal_2950_; lean_object* v_name_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref_known(v___x_2949_, 1);
v_toConstantVal_2950_ = lean_ctor_get(v_a_2943_, 0);
lean_inc_ref(v_toConstantVal_2950_);
lean_dec(v_a_2943_);
v_name_2951_ = lean_ctor_get(v_toConstantVal_2950_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_toConstantVal_2950_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; lean_object* v_unused_3153_; 
v_unused_3152_ = lean_ctor_get(v_toConstantVal_2950_, 2);
lean_dec(v_unused_3152_);
v_unused_3153_ = lean_ctor_get(v_toConstantVal_2950_, 1);
lean_dec(v_unused_3153_);
v___x_2953_ = v_toConstantVal_2950_;
v_isShared_2954_ = v_isSharedCheck_3151_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_name_2951_);
lean_dec(v_toConstantVal_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3151_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v_env_2957_; lean_object* v_nextMacroScope_2958_; lean_object* v_ngen_2959_; lean_object* v_auxDeclNGen_2960_; lean_object* v_traceState_2961_; lean_object* v_messages_2962_; lean_object* v_infoState_2963_; lean_object* v_snapshotTasks_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_3149_; 
lean_inc(v_name_2951_);
v___x_2955_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2951_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v___x_2955_);
v___x_2956_ = lean_st_ref_take(v___y_2854_);
v_env_2957_ = lean_ctor_get(v___x_2956_, 0);
v_nextMacroScope_2958_ = lean_ctor_get(v___x_2956_, 1);
v_ngen_2959_ = lean_ctor_get(v___x_2956_, 2);
v_auxDeclNGen_2960_ = lean_ctor_get(v___x_2956_, 3);
v_traceState_2961_ = lean_ctor_get(v___x_2956_, 4);
v_messages_2962_ = lean_ctor_get(v___x_2956_, 6);
v_infoState_2963_ = lean_ctor_get(v___x_2956_, 7);
v_snapshotTasks_2964_ = lean_ctor_get(v___x_2956_, 8);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v___x_2956_, 5);
lean_dec(v_unused_3150_);
v___x_2966_ = v___x_2956_;
v_isShared_2967_ = v_isSharedCheck_3149_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_snapshotTasks_2964_);
lean_inc(v_infoState_2963_);
lean_inc(v_messages_2962_);
lean_inc(v_traceState_2961_);
lean_inc(v_auxDeclNGen_2960_);
lean_inc(v_ngen_2959_);
lean_inc(v_nextMacroScope_2958_);
lean_inc(v_env_2957_);
lean_dec(v___x_2956_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_3149_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
lean_inc(v_name_2951_);
v___x_2968_ = l_Lean_markAuxRecursor(v_env_2957_, v_name_2951_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 5, v___x_2918_);
lean_ctor_set(v___x_2966_, 0, v___x_2968_);
v___x_2970_ = v___x_2966_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_nextMacroScope_2958_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_ngen_2959_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_auxDeclNGen_2960_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_traceState_2961_);
lean_ctor_set(v_reuseFailAlloc_3148_, 5, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3148_, 6, v_messages_2962_);
lean_ctor_set(v_reuseFailAlloc_3148_, 7, v_infoState_2963_);
lean_ctor_set(v_reuseFailAlloc_3148_, 8, v_snapshotTasks_2964_);
v___x_2970_ = v_reuseFailAlloc_3148_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v_mctx_2973_; lean_object* v_zetaDeltaFVarIds_2974_; lean_object* v_postponed_2975_; lean_object* v_diag_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3146_; 
v___x_2971_ = lean_st_ref_set(v___y_2854_, v___x_2970_);
v___x_2972_ = lean_st_ref_take(v___y_2852_);
v_mctx_2973_ = lean_ctor_get(v___x_2972_, 0);
v_zetaDeltaFVarIds_2974_ = lean_ctor_get(v___x_2972_, 2);
v_postponed_2975_ = lean_ctor_get(v___x_2972_, 3);
v_diag_2976_ = lean_ctor_get(v___x_2972_, 4);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v___x_2972_, 1);
lean_dec(v_unused_3147_);
v___x_2978_ = v___x_2972_;
v_isShared_2979_ = v_isSharedCheck_3146_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_diag_2976_);
lean_inc(v_postponed_2975_);
lean_inc(v_zetaDeltaFVarIds_2974_);
lean_inc(v_mctx_2973_);
lean_dec(v___x_2972_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3146_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v___x_2930_);
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_mctx_2973_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3145_, 2, v_zetaDeltaFVarIds_2974_);
lean_ctor_set(v_reuseFailAlloc_3145_, 3, v_postponed_2975_);
lean_ctor_set(v_reuseFailAlloc_3145_, 4, v_diag_2976_);
v___x_2981_ = v_reuseFailAlloc_3145_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_env_2984_; lean_object* v_nextMacroScope_2985_; lean_object* v_ngen_2986_; lean_object* v_auxDeclNGen_2987_; lean_object* v_traceState_2988_; lean_object* v_messages_2989_; lean_object* v_infoState_2990_; lean_object* v_snapshotTasks_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3143_; 
v___x_2982_ = lean_st_ref_set(v___y_2852_, v___x_2981_);
v___x_2983_ = lean_st_ref_take(v___y_2854_);
v_env_2984_ = lean_ctor_get(v___x_2983_, 0);
v_nextMacroScope_2985_ = lean_ctor_get(v___x_2983_, 1);
v_ngen_2986_ = lean_ctor_get(v___x_2983_, 2);
v_auxDeclNGen_2987_ = lean_ctor_get(v___x_2983_, 3);
v_traceState_2988_ = lean_ctor_get(v___x_2983_, 4);
v_messages_2989_ = lean_ctor_get(v___x_2983_, 6);
v_infoState_2990_ = lean_ctor_get(v___x_2983_, 7);
v_snapshotTasks_2991_ = lean_ctor_get(v___x_2983_, 8);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; 
v_unused_3144_ = lean_ctor_get(v___x_2983_, 5);
lean_dec(v_unused_3144_);
v___x_2993_ = v___x_2983_;
v_isShared_2994_ = v_isSharedCheck_3143_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_snapshotTasks_2991_);
lean_inc(v_infoState_2990_);
lean_inc(v_messages_2989_);
lean_inc(v_traceState_2988_);
lean_inc(v_auxDeclNGen_2987_);
lean_inc(v_ngen_2986_);
lean_inc(v_nextMacroScope_2985_);
lean_inc(v_env_2984_);
lean_dec(v___x_2983_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3143_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
lean_inc(v_name_2951_);
v___x_2995_ = l_Lean_addProtected(v_env_2984_, v_name_2951_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 5, v___x_2918_);
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2997_ = v___x_2993_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_nextMacroScope_2985_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_ngen_2986_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_auxDeclNGen_2987_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v_traceState_2988_);
lean_ctor_set(v_reuseFailAlloc_3142_, 5, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3142_, 6, v_messages_2989_);
lean_ctor_set(v_reuseFailAlloc_3142_, 7, v_infoState_2990_);
lean_ctor_set(v_reuseFailAlloc_3142_, 8, v_snapshotTasks_2991_);
v___x_2997_ = v_reuseFailAlloc_3142_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v_mctx_3000_; lean_object* v_zetaDeltaFVarIds_3001_; lean_object* v_postponed_3002_; lean_object* v_diag_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3140_; 
v___x_2998_ = lean_st_ref_set(v___y_2854_, v___x_2997_);
v___x_2999_ = lean_st_ref_take(v___y_2852_);
v_mctx_3000_ = lean_ctor_get(v___x_2999_, 0);
v_zetaDeltaFVarIds_3001_ = lean_ctor_get(v___x_2999_, 2);
v_postponed_3002_ = lean_ctor_get(v___x_2999_, 3);
v_diag_3003_ = lean_ctor_get(v___x_2999_, 4);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3140_ == 0)
{
lean_object* v_unused_3141_; 
v_unused_3141_ = lean_ctor_get(v___x_2999_, 1);
lean_dec(v_unused_3141_);
v___x_3005_ = v___x_2999_;
v_isShared_3006_ = v_isSharedCheck_3140_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_diag_3003_);
lean_inc(v_postponed_3002_);
lean_inc(v_zetaDeltaFVarIds_3001_);
lean_inc(v_mctx_3000_);
lean_dec(v___x_2999_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3140_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 1, v___x_2930_);
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_mctx_3000_);
lean_ctor_set(v_reuseFailAlloc_3139_, 1, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3139_, 2, v_zetaDeltaFVarIds_3001_);
lean_ctor_set(v_reuseFailAlloc_3139_, 3, v_postponed_3002_);
lean_ctor_set(v_reuseFailAlloc_3139_, 4, v_diag_3003_);
v___x_3008_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = lean_st_ref_set(v___y_2852_, v___x_3008_);
v___x_3010_ = l_Lean_Meta_mkPProdSndM(v___x_2935_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___x_3012_ = l_Lean_Expr_const___override(v_name_2951_, v___x_2846_);
v___x_3013_ = l_Lean_mkAppN(v___x_3012_, v___x_2883_);
v___x_3014_ = lean_array_get(v___x_2841_, v_fs_2850_, v_val_2842_);
lean_dec_ref(v_fs_2850_);
v___x_3015_ = l_Lean_mkAppN(v___x_3014_, v___x_2876_);
lean_dec_ref(v___x_2876_);
v___x_3016_ = l_Lean_Expr_app___override(v___x_3015_, v_a_3011_);
v___x_3017_ = l_Lean_Meta_mkEq(v___x_3013_, v___x_3016_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc_n(v_a_3018_, 2);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = lean_box(0);
v___x_3020_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3018_, v___x_3019_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___x_3022_ = l_Lean_Expr_mvarId_x21(v_a_3021_);
v___x_3023_ = l_Lean_Expr_fvarId_x21(v___x_2839_);
lean_dec_ref(v___x_2839_);
v___x_3024_ = lean_mk_empty_array_with_capacity(v___x_2848_);
v___x_3025_ = lean_box(0);
v___x_3026_ = l_Lean_MVarId_cases(v___x_3022_, v___x_3023_, v___x_3024_, v___x_2884_, v___x_3025_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_object* v_a_3027_; lean_object* v___x_3028_; size_t v_sz_3029_; lean_object* v___x_3030_; 
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___x_3028_ = lean_box(0);
v_sz_3029_ = lean_array_size(v_a_3027_);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3027_, v_sz_3029_, v___x_2835_, v___x_3028_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v_a_3027_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v___x_3031_; lean_object* v_a_3032_; lean_object* v___x_3033_; 
lean_dec_ref_known(v___x_3030_, 1);
v___x_3031_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_3021_, v___y_2852_);
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
v___x_3033_ = l_Lean_Meta_mkForallFVars(v___x_2883_, v_a_3018_, v___x_2884_, v___x_2843_, v___x_2843_, v___x_2885_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = l_Lean_Meta_mkLambdaFVars(v___x_2883_, v_a_3032_, v___x_2884_, v___x_2843_, v___x_2884_, v___x_2843_, v___x_2885_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec_ref(v___x_2883_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
lean_inc(v_brecOnEqName_2849_);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 2, v_a_3034_);
lean_ctor_set(v___x_2953_, 1, v_levelParams_2845_);
lean_ctor_set(v___x_2953_, 0, v_brecOnEqName_2849_);
v___x_3038_ = v___x_2953_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_brecOnEqName_2849_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_levelParams_2845_);
lean_ctor_set(v_reuseFailAlloc_3090_, 2, v_a_3034_);
v___x_3038_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3039_ = lean_box(0);
lean_inc(v_brecOnEqName_2849_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set_tag(v___x_2864_, 1);
lean_ctor_set(v___x_2864_, 1, v___x_3039_);
lean_ctor_set(v___x_2864_, 0, v_brecOnEqName_2849_);
v___x_3041_ = v___x_2864_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_brecOnEqName_2849_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
if (v_isShared_2903_ == 0)
{
lean_ctor_set(v___x_2902_, 2, v___x_3041_);
lean_ctor_set(v___x_2902_, 1, v_a_3036_);
lean_ctor_set(v___x_2902_, 0, v___x_3038_);
v___x_3043_ = v___x_2902_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3038_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_a_3036_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v_a_3045_; lean_object* v___x_3046_; 
v___x_3044_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3043_, v___y_2854_);
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref(v___x_3044_);
v___x_3046_ = l_Lean_addDecl(v_a_3045_, v___x_2884_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3086_; 
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v___x_3046_, 0);
lean_dec(v_unused_3087_);
v___x_3048_ = v___x_3046_;
v_isShared_3049_ = v_isSharedCheck_3086_;
goto v_resetjp_3047_;
}
else
{
lean_dec(v___x_3046_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3086_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3050_; lean_object* v_env_3051_; lean_object* v_nextMacroScope_3052_; lean_object* v_ngen_3053_; lean_object* v_auxDeclNGen_3054_; lean_object* v_traceState_3055_; lean_object* v_messages_3056_; lean_object* v_infoState_3057_; lean_object* v_snapshotTasks_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3084_; 
v___x_3050_ = lean_st_ref_take(v___y_2854_);
v_env_3051_ = lean_ctor_get(v___x_3050_, 0);
v_nextMacroScope_3052_ = lean_ctor_get(v___x_3050_, 1);
v_ngen_3053_ = lean_ctor_get(v___x_3050_, 2);
v_auxDeclNGen_3054_ = lean_ctor_get(v___x_3050_, 3);
v_traceState_3055_ = lean_ctor_get(v___x_3050_, 4);
v_messages_3056_ = lean_ctor_get(v___x_3050_, 6);
v_infoState_3057_ = lean_ctor_get(v___x_3050_, 7);
v_snapshotTasks_3058_ = lean_ctor_get(v___x_3050_, 8);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3084_ == 0)
{
lean_object* v_unused_3085_; 
v_unused_3085_ = lean_ctor_get(v___x_3050_, 5);
lean_dec(v_unused_3085_);
v___x_3060_ = v___x_3050_;
v_isShared_3061_ = v_isSharedCheck_3084_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_snapshotTasks_3058_);
lean_inc(v_infoState_3057_);
lean_inc(v_messages_3056_);
lean_inc(v_traceState_3055_);
lean_inc(v_auxDeclNGen_3054_);
lean_inc(v_ngen_3053_);
lean_inc(v_nextMacroScope_3052_);
lean_inc(v_env_3051_);
lean_dec(v___x_3050_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3084_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = l_Lean_addProtected(v_env_3051_, v_brecOnEqName_2849_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 5, v___x_2918_);
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v_nextMacroScope_3052_);
lean_ctor_set(v_reuseFailAlloc_3083_, 2, v_ngen_3053_);
lean_ctor_set(v_reuseFailAlloc_3083_, 3, v_auxDeclNGen_3054_);
lean_ctor_set(v_reuseFailAlloc_3083_, 4, v_traceState_3055_);
lean_ctor_set(v_reuseFailAlloc_3083_, 5, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_3083_, 6, v_messages_3056_);
lean_ctor_set(v_reuseFailAlloc_3083_, 7, v_infoState_3057_);
lean_ctor_set(v_reuseFailAlloc_3083_, 8, v_snapshotTasks_3058_);
v___x_3064_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v_mctx_3067_; lean_object* v_zetaDeltaFVarIds_3068_; lean_object* v_postponed_3069_; lean_object* v_diag_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3081_; 
v___x_3065_ = lean_st_ref_set(v___y_2854_, v___x_3064_);
v___x_3066_ = lean_st_ref_take(v___y_2852_);
v_mctx_3067_ = lean_ctor_get(v___x_3066_, 0);
v_zetaDeltaFVarIds_3068_ = lean_ctor_get(v___x_3066_, 2);
v_postponed_3069_ = lean_ctor_get(v___x_3066_, 3);
v_diag_3070_ = lean_ctor_get(v___x_3066_, 4);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3066_, 1);
lean_dec(v_unused_3082_);
v___x_3072_ = v___x_3066_;
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_diag_3070_);
lean_inc(v_postponed_3069_);
lean_inc(v_zetaDeltaFVarIds_3068_);
lean_inc(v_mctx_3067_);
lean_dec(v___x_3066_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3081_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v___x_2930_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_mctx_3067_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3080_, 2, v_zetaDeltaFVarIds_3068_);
lean_ctor_set(v_reuseFailAlloc_3080_, 3, v_postponed_3069_);
lean_ctor_set(v_reuseFailAlloc_3080_, 4, v_diag_3070_);
v___x_3075_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3076_ = lean_st_ref_set(v___y_2852_, v___x_3075_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v___x_3028_);
v___x_3078_ = v___x_3048_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3028_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
}
}
else
{
lean_dec(v_brecOnEqName_2849_);
return v___x_3046_;
}
}
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v_a_3034_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2902_);
lean_del_object(v___x_2864_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_levelParams_2845_);
v_a_3091_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3035_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3035_);
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
lean_dec(v_a_3032_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2864_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_levelParams_2845_);
v_a_3099_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___x_3033_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___x_3033_);
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
lean_dec(v_a_3021_);
lean_dec(v_a_3018_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2864_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_levelParams_2845_);
return v___x_3030_;
}
}
else
{
lean_object* v_a_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3114_; 
lean_dec(v_a_3021_);
lean_dec(v_a_3018_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2864_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_levelParams_2845_);
v_a_3107_ = lean_ctor_get(v___x_3026_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3026_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3109_ = v___x_3026_;
v_isShared_3110_ = v_isSharedCheck_3114_;
goto v_resetjp_3108_;
}
else
{
lean_inc(v_a_3107_);
lean_dec(v___x_3026_);
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
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_a_3018_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2864_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_levelParams_2845_);
lean_dec_ref(v___x_2839_);
v_a_3115_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3020_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3020_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_del_object(v___x_2953_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_del_object(v___x_2864_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_levelParams_2845_);
lean_dec_ref(v___x_2839_);
v_a_3123_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3017_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3017_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_del_object(v___x_2953_);
lean_dec(v_name_2951_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec_ref(v___x_2839_);
v_a_3131_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3010_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3010_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
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
lean_dec(v_a_2943_);
lean_dec_ref(v___x_2935_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec_ref(v___x_2839_);
return v___x_2949_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_a_2939_);
lean_dec_ref(v___x_2935_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec_ref(v___x_2839_);
v_a_3156_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_2940_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_2940_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v___x_2935_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec_ref(v___x_2839_);
v_a_3164_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_2938_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_2938_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec_ref(v___x_2935_);
lean_del_object(v___x_2902_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec_ref(v___x_2839_);
v_a_3172_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_2936_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_2936_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
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
lean_dec(v_a_2892_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec(v_brecOnGoName_2844_);
lean_dec_ref(v___x_2839_);
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
lean_dec(v_a_2887_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2876_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec(v_brecOnGoName_2844_);
lean_dec_ref(v___x_2839_);
v_a_3191_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3193_ = v___x_2888_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___x_2888_);
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
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2876_);
lean_dec_ref(v___x_2870_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec(v_brecOnGoName_2844_);
lean_dec_ref(v___x_2839_);
v_a_3199_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_2886_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_2886_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec_ref(v___x_2877_);
lean_dec_ref(v___x_2876_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2872_);
lean_dec_ref(v___x_2870_);
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec(v_brecOnGoName_2844_);
lean_dec_ref(v___x_2839_);
v_a_3207_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_2880_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_2880_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_del_object(v___x_2864_);
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec(v_brecOnGoName_2844_);
lean_dec_ref(v___x_2839_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v___x_2833_);
lean_dec_ref(v___x_2831_);
v_a_3215_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_2867_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_2867_);
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
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref(v_fs_2850_);
lean_dec(v_brecOnEqName_2849_);
lean_dec(v_brecOnName_2847_);
lean_dec(v___x_2846_);
lean_dec(v_levelParams_2845_);
lean_dec(v_brecOnGoName_2844_);
lean_dec_ref(v___x_2839_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v___x_2837_);
lean_dec_ref(v___x_2833_);
lean_dec_ref(v___x_2831_);
lean_dec(v___x_2828_);
v_a_3225_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_2860_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_2860_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3230_; 
if (v_isShared_3228_ == 0)
{
v___x_3230_ = v___x_3227_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_a_3225_);
v___x_3230_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
return v___x_3230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3233_ = _args[0];
lean_object* v_tail_3234_ = _args[1];
lean_object* v_recName_3235_ = _args[2];
lean_object* v___x_3236_ = _args[3];
lean_object* v___x_3237_ = _args[4];
lean_object* v___x_3238_ = _args[5];
lean_object* v_sz_3239_ = _args[6];
lean_object* v___x_3240_ = _args[7];
lean_object* v___x_3241_ = _args[8];
lean_object* v___x_3242_ = _args[9];
lean_object* v___x_3243_ = _args[10];
lean_object* v___x_3244_ = _args[11];
lean_object* v___x_3245_ = _args[12];
lean_object* v___x_3246_ = _args[13];
lean_object* v_val_3247_ = _args[14];
lean_object* v___x_3248_ = _args[15];
lean_object* v_brecOnGoName_3249_ = _args[16];
lean_object* v_levelParams_3250_ = _args[17];
lean_object* v___x_3251_ = _args[18];
lean_object* v_brecOnName_3252_ = _args[19];
lean_object* v___x_3253_ = _args[20];
lean_object* v_brecOnEqName_3254_ = _args[21];
lean_object* v_fs_3255_ = _args[22];
lean_object* v___y_3256_ = _args[23];
lean_object* v___y_3257_ = _args[24];
lean_object* v___y_3258_ = _args[25];
lean_object* v___y_3259_ = _args[26];
lean_object* v___y_3260_ = _args[27];
_start:
{
size_t v_sz_boxed_3261_; size_t v___x_30773__boxed_3262_; uint8_t v___x_30781__boxed_3263_; lean_object* v_res_3264_; 
v_sz_boxed_3261_ = lean_unbox_usize(v_sz_3239_);
lean_dec(v_sz_3239_);
v___x_30773__boxed_3262_ = lean_unbox_usize(v___x_3240_);
lean_dec(v___x_3240_);
v___x_30781__boxed_3263_ = lean_unbox(v___x_3248_);
v_res_3264_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3233_, v_tail_3234_, v_recName_3235_, v___x_3236_, v___x_3237_, v___x_3238_, v_sz_boxed_3261_, v___x_30773__boxed_3262_, v___x_3241_, v___x_3242_, v___x_3243_, v___x_3244_, v___x_3245_, v___x_3246_, v_val_3247_, v___x_30781__boxed_3263_, v_brecOnGoName_3249_, v_levelParams_3250_, v___x_3251_, v_brecOnName_3252_, v___x_3253_, v_brecOnEqName_3254_, v_fs_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
lean_dec(v___y_3259_);
lean_dec_ref(v___y_3258_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___x_3253_);
lean_dec(v_val_3247_);
lean_dec_ref(v___x_3246_);
lean_dec(v___x_3245_);
lean_dec_ref(v___x_3241_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3265_, lean_object* v_a_3266_, uint8_t v___x_3267_, lean_object* v_f_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; 
lean_inc_ref(v_targs_3265_);
v___x_3274_ = lean_array_push(v_targs_3265_, v_f_3268_);
v___x_3275_ = l_Lean_mkAppN(v_a_3266_, v_targs_3265_);
lean_dec_ref(v_targs_3265_);
v___x_3276_ = 0;
v___x_3277_ = 1;
v___x_3278_ = l_Lean_Meta_mkForallFVars(v___x_3274_, v___x_3275_, v___x_3276_, v___x_3267_, v___x_3267_, v___x_3277_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec_ref(v___x_3274_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3279_, lean_object* v_a_3280_, lean_object* v___x_3281_, lean_object* v_f_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
uint8_t v___x_31491__boxed_3288_; lean_object* v_res_3289_; 
v___x_31491__boxed_3288_ = lean_unbox(v___x_3281_);
v_res_3289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3279_, v_a_3280_, v___x_31491__boxed_3288_, v_f_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3293_, uint8_t v___x_3294_, lean_object* v___x_3295_, lean_object* v_targs_3296_, lean_object* v_x_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; lean_object* v___f_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3303_ = lean_box(v___x_3294_);
lean_inc_ref(v_targs_3296_);
v___f_3304_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3304_, 0, v_targs_3296_);
lean_closure_set(v___f_3304_, 1, v_a_3293_);
lean_closure_set(v___f_3304_, 2, v___x_3303_);
v___x_3305_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3306_ = l_Lean_mkAppN(v___x_3295_, v_targs_3296_);
lean_dec_ref(v_targs_3296_);
v___x_3307_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3305_, v___x_3306_, v___f_3304_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3308_, lean_object* v___x_3309_, lean_object* v___x_3310_, lean_object* v_targs_3311_, lean_object* v_x_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
uint8_t v___x_31525__boxed_3318_; lean_object* v_res_3319_; 
v___x_31525__boxed_3318_ = lean_unbox(v___x_3309_);
v_res_3319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3308_, v___x_31525__boxed_3318_, v___x_3310_, v_targs_3311_, v_x_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
lean_dec_ref(v_x_3312_);
return v_res_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3320_, lean_object* v_x_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v___x_3327_; 
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_a_3320_);
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3328_, lean_object* v_x_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3328_, v_x_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec_ref(v_x_3329_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v_as_3337_, size_t v_sz_3338_, size_t v_i_3339_, lean_object* v_b_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
uint8_t v___x_3346_; 
v___x_3346_ = lean_usize_dec_lt(v_i_3339_, v_sz_3338_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_b_3340_);
return v___x_3347_;
}
else
{
lean_object* v_snd_3348_; lean_object* v_fst_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3445_; 
v_snd_3348_ = lean_ctor_get(v_b_3340_, 1);
v_fst_3349_ = lean_ctor_get(v_b_3340_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_b_3340_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3351_ = v_b_3340_;
v_isShared_3352_ = v_isSharedCheck_3445_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_snd_3348_);
lean_inc(v_fst_3349_);
lean_dec(v_b_3340_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3445_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v_fst_3353_; lean_object* v_snd_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3444_; 
v_fst_3353_ = lean_ctor_get(v_snd_3348_, 0);
v_snd_3354_ = lean_ctor_get(v_snd_3348_, 1);
v_isSharedCheck_3444_ = !lean_is_exclusive(v_snd_3348_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3356_ = v_snd_3348_;
v_isShared_3357_ = v_isSharedCheck_3444_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_snd_3354_);
lean_inc(v_fst_3353_);
lean_dec(v_snd_3348_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3444_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v_next_3366_; 
v_next_3366_ = lean_ctor_get(v_snd_3354_, 0);
lean_inc(v_next_3366_);
if (lean_obj_tag(v_next_3366_) == 0)
{
goto v___jp_3358_;
}
else
{
lean_object* v_upperBound_3367_; lean_object* v_val_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3443_; 
v_upperBound_3367_ = lean_ctor_get(v_snd_3354_, 1);
v_val_3368_ = lean_ctor_get(v_next_3366_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v_next_3366_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3370_ = v_next_3366_;
v_isShared_3371_ = v_isSharedCheck_3443_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_val_3368_);
lean_dec(v_next_3366_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3443_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
uint8_t v___x_3372_; 
v___x_3372_ = lean_nat_dec_lt(v_val_3368_, v_upperBound_3367_);
if (v___x_3372_ == 0)
{
lean_del_object(v___x_3370_);
lean_dec(v_val_3368_);
goto v___jp_3358_;
}
else
{
lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3440_; 
lean_inc(v_upperBound_3367_);
lean_del_object(v___x_3356_);
lean_del_object(v___x_3351_);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_snd_3354_);
if (v_isSharedCheck_3440_ == 0)
{
lean_object* v_unused_3441_; lean_object* v_unused_3442_; 
v_unused_3441_ = lean_ctor_get(v_snd_3354_, 1);
lean_dec(v_unused_3441_);
v_unused_3442_ = lean_ctor_get(v_snd_3354_, 0);
lean_dec(v_unused_3442_);
v___x_3374_ = v_snd_3354_;
v_isShared_3375_ = v_isSharedCheck_3440_;
goto v_resetjp_3373_;
}
else
{
lean_dec(v_snd_3354_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3440_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v_array_3376_; lean_object* v_start_3377_; lean_object* v_stop_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3382_; 
v_array_3376_ = lean_ctor_get(v_fst_3353_, 0);
v_start_3377_ = lean_ctor_get(v_fst_3353_, 1);
v_stop_3378_ = lean_ctor_get(v_fst_3353_, 2);
v___x_3379_ = lean_unsigned_to_nat(1u);
v___x_3380_ = lean_nat_add(v_val_3368_, v___x_3379_);
lean_dec(v_val_3368_);
lean_inc(v___x_3380_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3380_);
v___x_3382_ = v___x_3370_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
lean_object* v___x_3384_; 
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3382_);
v___x_3384_ = v___x_3374_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3382_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_upperBound_3367_);
v___x_3384_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
uint8_t v___x_3385_; 
v___x_3385_ = lean_nat_dec_lt(v_start_3377_, v_stop_3378_);
if (v___x_3385_ == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
lean_dec(v___x_3380_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_fst_3353_);
lean_ctor_set(v___x_3386_, 1, v___x_3384_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v_fst_3349_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
return v___x_3388_;
}
else
{
lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3434_; 
lean_inc(v_stop_3378_);
lean_inc(v_start_3377_);
lean_inc_ref(v_array_3376_);
v_isSharedCheck_3434_ = !lean_is_exclusive(v_fst_3353_);
if (v_isSharedCheck_3434_ == 0)
{
lean_object* v_unused_3435_; lean_object* v_unused_3436_; lean_object* v_unused_3437_; 
v_unused_3435_ = lean_ctor_get(v_fst_3353_, 2);
lean_dec(v_unused_3435_);
v_unused_3436_ = lean_ctor_get(v_fst_3353_, 1);
lean_dec(v_unused_3436_);
v_unused_3437_ = lean_ctor_get(v_fst_3353_, 0);
lean_dec(v_unused_3437_);
v___x_3390_ = v_fst_3353_;
v_isShared_3391_ = v_isSharedCheck_3434_;
goto v_resetjp_3389_;
}
else
{
lean_dec(v_fst_3353_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3434_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v_a_3392_; lean_object* v___x_3393_; 
v_a_3392_ = lean_array_uget_borrowed(v_as_3337_, v_i_3339_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
lean_inc(v_a_3392_);
v___x_3393_ = lean_infer_type(v_a_3392_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___f_3397_; uint8_t v___x_3398_; lean_object* v___x_3399_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref_known(v___x_3393_, 1);
v___x_3395_ = lean_array_fget_borrowed(v_array_3376_, v_start_3377_);
v___x_3396_ = lean_box(v___x_3385_);
lean_inc(v___x_3395_);
lean_inc(v_a_3392_);
v___f_3397_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3397_, 0, v_a_3392_);
lean_closure_set(v___f_3397_, 1, v___x_3396_);
lean_closure_set(v___f_3397_, 2, v___x_3395_);
v___x_3398_ = 0;
v___x_3399_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3394_, v___f_3397_, v___x_3398_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v___f_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3399_, 1);
v___f_3401_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3401_, 0, v_a_3400_);
v___x_3402_ = lean_nat_add(v_start_3377_, v___x_3379_);
lean_dec(v_start_3377_);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 1, v___x_3402_);
v___x_3404_ = v___x_3390_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_array_3376_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_stop_3378_);
v___x_3404_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; size_t v___x_3414_; size_t v___x_3415_; 
v___x_3405_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3406_ = l_Nat_reprFast(v___x_3380_);
v___x_3407_ = lean_string_append(v___x_3405_, v___x_3406_);
lean_dec_ref(v___x_3406_);
v___x_3408_ = lean_box(0);
v___x_3409_ = l_Lean_Name_str___override(v___x_3408_, v___x_3407_);
v___x_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
lean_ctor_set(v___x_3410_, 1, v___f_3401_);
v___x_3411_ = lean_array_push(v_fst_3349_, v___x_3410_);
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v___x_3404_);
lean_ctor_set(v___x_3412_, 1, v___x_3384_);
v___x_3413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = ((size_t)1ULL);
v___x_3415_ = lean_usize_add(v_i_3339_, v___x_3414_);
v_i_3339_ = v___x_3415_;
v_b_3340_ = v___x_3413_;
goto _start;
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_del_object(v___x_3390_);
lean_dec_ref(v___x_3384_);
lean_dec(v___x_3380_);
lean_dec(v_stop_3378_);
lean_dec(v_start_3377_);
lean_dec_ref(v_array_3376_);
lean_dec(v_fst_3349_);
v_a_3418_ = lean_ctor_get(v___x_3399_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3399_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3399_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_del_object(v___x_3390_);
lean_dec_ref(v___x_3384_);
lean_dec(v___x_3380_);
lean_dec(v_stop_3378_);
lean_dec(v_start_3377_);
lean_dec_ref(v_array_3376_);
lean_dec(v_fst_3349_);
v_a_3426_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3393_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3393_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
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
v___jp_3358_:
{
lean_object* v___x_3360_; 
if (v_isShared_3357_ == 0)
{
v___x_3360_ = v___x_3356_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_fst_3353_);
lean_ctor_set(v_reuseFailAlloc_3365_, 1, v_snd_3354_);
v___x_3360_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
lean_object* v___x_3362_; 
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 1, v___x_3360_);
v___x_3362_ = v___x_3351_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_fst_3349_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; 
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
return v___x_3363_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v_as_3446_, lean_object* v_sz_3447_, lean_object* v_i_3448_, lean_object* v_b_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
size_t v_sz_boxed_3455_; size_t v_i_boxed_3456_; lean_object* v_res_3457_; 
v_sz_boxed_3455_ = lean_unbox_usize(v_sz_3447_);
lean_dec(v_sz_3447_);
v_i_boxed_3456_ = lean_unbox_usize(v_i_3448_);
lean_dec(v_i_3448_);
v_res_3457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v_as_3446_, v_sz_boxed_3455_, v_i_boxed_3456_, v_b_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_as_3446_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3458_, size_t v_i_3459_, lean_object* v_bs_3460_){
_start:
{
uint8_t v___x_3461_; 
v___x_3461_ = lean_usize_dec_lt(v_i_3459_, v_sz_3458_);
if (v___x_3461_ == 0)
{
return v_bs_3460_;
}
else
{
lean_object* v_v_3462_; lean_object* v_fst_3463_; lean_object* v_snd_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3480_; 
v_v_3462_ = lean_array_uget(v_bs_3460_, v_i_3459_);
v_fst_3463_ = lean_ctor_get(v_v_3462_, 0);
v_snd_3464_ = lean_ctor_get(v_v_3462_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_v_3462_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3466_ = v_v_3462_;
v_isShared_3467_ = v_isSharedCheck_3480_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_snd_3464_);
lean_inc(v_fst_3463_);
lean_dec(v_v_3462_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3480_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v_bs_x27_3469_; uint8_t v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3468_ = lean_unsigned_to_nat(0u);
v_bs_x27_3469_ = lean_array_uset(v_bs_3460_, v_i_3459_, v___x_3468_);
v___x_3470_ = 0;
v___x_3471_ = lean_box(v___x_3470_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3471_);
v___x_3473_ = v___x_3466_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_snd_3464_);
v___x_3473_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; size_t v___x_3475_; size_t v___x_3476_; lean_object* v___x_3477_; 
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v_fst_3463_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = ((size_t)1ULL);
v___x_3476_ = lean_usize_add(v_i_3459_, v___x_3475_);
v___x_3477_ = lean_array_uset(v_bs_x27_3469_, v_i_3459_, v___x_3474_);
v_i_3459_ = v___x_3476_;
v_bs_3460_ = v___x_3477_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3481_, lean_object* v_i_3482_, lean_object* v_bs_3483_){
_start:
{
size_t v_sz_boxed_3484_; size_t v_i_boxed_3485_; lean_object* v_res_3486_; 
v_sz_boxed_3484_ = lean_unbox_usize(v_sz_3481_);
lean_dec(v_sz_3481_);
v_i_boxed_3485_ = lean_unbox_usize(v_i_3482_);
lean_dec(v_i_3482_);
v_res_3486_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3484_, v_i_boxed_3485_, v_bs_3483_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3487_, lean_object* v_a_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_30332__overap_3495_; lean_object* v___x_3496_; 
v___x_3494_ = l_Lean_instInhabitedExpr;
v___x_30332__overap_3495_ = l_instInhabitedOfMonad___redArg(v___x_3487_, v___x_3494_);
lean_inc(v___y_3492_);
lean_inc_ref(v___y_3491_);
lean_inc(v___y_3490_);
lean_inc_ref(v___y_3489_);
v___x_3496_ = lean_apply_5(v___x_30332__overap_3495_, v___y_3489_, v___y_3490_, v___y_3491_, v___y_3492_, lean_box(0));
return v___x_3496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3497_, lean_object* v_a_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3497_, v_a_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec_ref(v_a_3498_);
return v_res_3504_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l_instMonadEIO(lean_box(0));
return v___x_3505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3506_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3507_ = l_StateRefT_x27_instMonad___redArg(v___x_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3512_, lean_object* v_declInfos_3513_, lean_object* v_k_3514_, lean_object* v_kind_3515_, lean_object* v_b_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
uint8_t v_kind_boxed_3522_; lean_object* v_res_3523_; 
v_kind_boxed_3522_ = lean_unbox(v_kind_3515_);
v_res_3523_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3512_, v_declInfos_3513_, v_k_3514_, v_kind_boxed_3522_, v_b_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3524_, lean_object* v_declInfos_3525_, lean_object* v_k_3526_, uint8_t v_kind_3527_, lean_object* v_name_3528_, uint8_t v_bi_3529_, lean_object* v_type_3530_, uint8_t v_kind_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v___x_3537_; lean_object* v___f_3538_; lean_object* v___x_3539_; 
v___x_3537_ = lean_box(v_kind_3527_);
v___f_3538_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3538_, 0, v_acc_3524_);
lean_closure_set(v___f_3538_, 1, v_declInfos_3525_);
lean_closure_set(v___f_3538_, 2, v_k_3526_);
lean_closure_set(v___f_3538_, 3, v___x_3537_);
v___x_3539_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3528_, v_bi_3529_, v_type_3530_, v___f_3538_, v_kind_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3539_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3539_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
v_a_3548_ = lean_ctor_get(v___x_3539_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3539_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3539_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3539_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3556_, lean_object* v_k_3557_, uint8_t v_kind_3558_, lean_object* v_acc_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___x_3565_; lean_object* v_toApplicative_3566_; lean_object* v_toFunctor_3567_; lean_object* v_toSeq_3568_; lean_object* v_toSeqLeft_3569_; lean_object* v_toSeqRight_3570_; lean_object* v___f_3571_; lean_object* v___f_3572_; lean_object* v___f_3573_; lean_object* v___f_3574_; lean_object* v___x_3575_; lean_object* v___f_3576_; lean_object* v___f_3577_; lean_object* v___f_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v_toApplicative_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3637_; 
v___x_3565_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3566_ = lean_ctor_get(v___x_3565_, 0);
v_toFunctor_3567_ = lean_ctor_get(v_toApplicative_3566_, 0);
v_toSeq_3568_ = lean_ctor_get(v_toApplicative_3566_, 2);
v_toSeqLeft_3569_ = lean_ctor_get(v_toApplicative_3566_, 3);
v_toSeqRight_3570_ = lean_ctor_get(v_toApplicative_3566_, 4);
v___f_3571_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3572_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3567_, 2);
v___f_3573_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3573_, 0, v_toFunctor_3567_);
v___f_3574_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3574_, 0, v_toFunctor_3567_);
v___x_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___f_3573_);
lean_ctor_set(v___x_3575_, 1, v___f_3574_);
lean_inc(v_toSeqRight_3570_);
v___f_3576_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3576_, 0, v_toSeqRight_3570_);
lean_inc(v_toSeqLeft_3569_);
v___f_3577_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3577_, 0, v_toSeqLeft_3569_);
lean_inc(v_toSeq_3568_);
v___f_3578_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3578_, 0, v_toSeq_3568_);
v___x_3579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3575_);
lean_ctor_set(v___x_3579_, 1, v___f_3571_);
lean_ctor_set(v___x_3579_, 2, v___f_3578_);
lean_ctor_set(v___x_3579_, 3, v___f_3577_);
lean_ctor_set(v___x_3579_, 4, v___f_3576_);
v___x_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v___f_3572_);
v___x_3581_ = l_StateRefT_x27_instMonad___redArg(v___x_3580_);
v_toApplicative_3582_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v___x_3581_, 1);
lean_dec(v_unused_3638_);
v___x_3584_ = v___x_3581_;
v_isShared_3585_ = v_isSharedCheck_3637_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_toApplicative_3582_);
lean_dec(v___x_3581_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3637_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v_toFunctor_3586_; lean_object* v_toSeq_3587_; lean_object* v_toSeqLeft_3588_; lean_object* v_toSeqRight_3589_; lean_object* v___x_3591_; uint8_t v_isShared_3592_; uint8_t v_isSharedCheck_3635_; 
v_toFunctor_3586_ = lean_ctor_get(v_toApplicative_3582_, 0);
v_toSeq_3587_ = lean_ctor_get(v_toApplicative_3582_, 2);
v_toSeqLeft_3588_ = lean_ctor_get(v_toApplicative_3582_, 3);
v_toSeqRight_3589_ = lean_ctor_get(v_toApplicative_3582_, 4);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_toApplicative_3582_);
if (v_isSharedCheck_3635_ == 0)
{
lean_object* v_unused_3636_; 
v_unused_3636_ = lean_ctor_get(v_toApplicative_3582_, 1);
lean_dec(v_unused_3636_);
v___x_3591_ = v_toApplicative_3582_;
v_isShared_3592_ = v_isSharedCheck_3635_;
goto v_resetjp_3590_;
}
else
{
lean_inc(v_toSeqRight_3589_);
lean_inc(v_toSeqLeft_3588_);
lean_inc(v_toSeq_3587_);
lean_inc(v_toFunctor_3586_);
lean_dec(v_toApplicative_3582_);
v___x_3591_ = lean_box(0);
v_isShared_3592_ = v_isSharedCheck_3635_;
goto v_resetjp_3590_;
}
v_resetjp_3590_:
{
lean_object* v___f_3593_; lean_object* v___f_3594_; lean_object* v___f_3595_; lean_object* v___f_3596_; lean_object* v___x_3597_; lean_object* v___f_3598_; lean_object* v___f_3599_; lean_object* v___f_3600_; lean_object* v___x_3602_; 
v___f_3593_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3594_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3586_);
v___f_3595_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3595_, 0, v_toFunctor_3586_);
v___f_3596_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3596_, 0, v_toFunctor_3586_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___f_3595_);
lean_ctor_set(v___x_3597_, 1, v___f_3596_);
v___f_3598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3598_, 0, v_toSeqRight_3589_);
v___f_3599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3599_, 0, v_toSeqLeft_3588_);
v___f_3600_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3600_, 0, v_toSeq_3587_);
if (v_isShared_3592_ == 0)
{
lean_ctor_set(v___x_3591_, 4, v___f_3598_);
lean_ctor_set(v___x_3591_, 3, v___f_3599_);
lean_ctor_set(v___x_3591_, 2, v___f_3600_);
lean_ctor_set(v___x_3591_, 1, v___f_3593_);
lean_ctor_set(v___x_3591_, 0, v___x_3597_);
v___x_3602_ = v___x_3591_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3597_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v___f_3593_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v___f_3600_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v___f_3599_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v___f_3598_);
v___x_3602_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3604_; 
if (v_isShared_3585_ == 0)
{
lean_ctor_set(v___x_3584_, 1, v___f_3594_);
lean_ctor_set(v___x_3584_, 0, v___x_3602_);
v___x_3604_ = v___x_3584_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3633_, 1, v___f_3594_);
v___x_3604_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3605_ = lean_array_get_size(v_acc_3559_);
v___x_3606_ = lean_array_get_size(v_declInfos_3556_);
v___x_3607_ = lean_nat_dec_lt(v___x_3605_, v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; 
lean_dec_ref(v___x_3604_);
lean_dec_ref(v_declInfos_3556_);
lean_inc(v___y_3563_);
lean_inc_ref(v___y_3562_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
v___x_3608_ = lean_apply_6(v_k_3557_, v_acc_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, lean_box(0));
return v___x_3608_;
}
else
{
lean_object* v___f_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; lean_object* v___f_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v_snd_3617_; lean_object* v_fst_3618_; lean_object* v_fst_3619_; lean_object* v_snd_3620_; lean_object* v___x_3621_; 
v___f_3609_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3609_, 0, v___x_3604_);
v___x_3610_ = lean_box(0);
v___x_3611_ = 0;
v___f_3612_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3612_, 0, v___f_3609_);
v___x_3613_ = lean_box(v___x_3611_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3613_);
lean_ctor_set(v___x_3614_, 1, v___f_3612_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3610_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_array_get(v___x_3615_, v_declInfos_3556_, v___x_3605_);
lean_dec_ref_known(v___x_3615_, 2);
v_snd_3617_ = lean_ctor_get(v___x_3616_, 1);
lean_inc(v_snd_3617_);
v_fst_3618_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_fst_3618_);
lean_dec(v___x_3616_);
v_fst_3619_ = lean_ctor_get(v_snd_3617_, 0);
lean_inc(v_fst_3619_);
v_snd_3620_ = lean_ctor_get(v_snd_3617_, 1);
lean_inc(v_snd_3620_);
lean_dec(v_snd_3617_);
lean_inc(v___y_3563_);
lean_inc_ref(v___y_3562_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc_ref(v_acc_3559_);
v___x_3621_ = lean_apply_6(v_snd_3620_, v_acc_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, lean_box(0));
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; uint8_t v___x_3623_; lean_object* v___x_3624_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
lean_dec_ref_known(v___x_3621_, 1);
v___x_3623_ = lean_unbox(v_fst_3619_);
lean_dec(v_fst_3619_);
v___x_3624_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3559_, v_declInfos_3556_, v_k_3557_, v_kind_3558_, v_fst_3618_, v___x_3623_, v_a_3622_, v_kind_3558_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
return v___x_3624_;
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec(v_fst_3619_);
lean_dec(v_fst_3618_);
lean_dec_ref(v_acc_3559_);
lean_dec_ref(v_k_3557_);
lean_dec_ref(v_declInfos_3556_);
v_a_3625_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3621_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3621_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3639_, lean_object* v_declInfos_3640_, lean_object* v_k_3641_, uint8_t v_kind_3642_, lean_object* v_b_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = lean_array_push(v_acc_3639_, v_b_3643_);
v___x_3650_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3640_, v_k_3641_, v_kind_3642_, v___x_3649_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3651_, lean_object* v_declInfos_3652_, lean_object* v_k_3653_, lean_object* v_kind_3654_, lean_object* v_name_3655_, lean_object* v_bi_3656_, lean_object* v_type_3657_, lean_object* v_kind_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_){
_start:
{
uint8_t v_kind_boxed_3664_; uint8_t v_bi_boxed_3665_; uint8_t v_kind_boxed_3666_; lean_object* v_res_3667_; 
v_kind_boxed_3664_ = lean_unbox(v_kind_3654_);
v_bi_boxed_3665_ = lean_unbox(v_bi_3656_);
v_kind_boxed_3666_ = lean_unbox(v_kind_3658_);
v_res_3667_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3651_, v_declInfos_3652_, v_k_3653_, v_kind_boxed_3664_, v_name_3655_, v_bi_boxed_3665_, v_type_3657_, v_kind_boxed_3666_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3668_, lean_object* v_k_3669_, lean_object* v_kind_3670_, lean_object* v_acc_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
uint8_t v_kind_boxed_3677_; lean_object* v_res_3678_; 
v_kind_boxed_3677_ = lean_unbox(v_kind_3670_);
v_res_3678_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3668_, v_k_3669_, v_kind_boxed_3677_, v_acc_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3679_, lean_object* v_k_3680_, uint8_t v_kind_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3687_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3688_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3679_, v_k_3680_, v_kind_3681_, v___x_3687_, v___y_3682_, v___y_3683_, v___y_3684_, v___y_3685_);
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3689_, lean_object* v_k_3690_, lean_object* v_kind_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
uint8_t v_kind_boxed_3697_; lean_object* v_res_3698_; 
v_kind_boxed_3697_ = lean_unbox(v_kind_3691_);
v_res_3698_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3689_, v_k_3690_, v_kind_boxed_3697_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3699_, lean_object* v_k_3700_, uint8_t v_kind_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
size_t v_sz_3707_; size_t v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v_sz_3707_ = lean_array_size(v_declInfos_3699_);
v___x_3708_ = ((size_t)0ULL);
v___x_3709_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3707_, v___x_3708_, v_declInfos_3699_);
v___x_3710_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3709_, v_k_3700_, v_kind_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3711_, lean_object* v_k_3712_, lean_object* v_kind_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v_kind_boxed_3719_; lean_object* v_res_3720_; 
v_kind_boxed_3719_ = lean_unbox(v_kind_3713_);
v_res_3720_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3711_, v_k_3712_, v_kind_boxed_3719_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
return v_res_3720_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3722_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3723_ = lean_unsigned_to_nat(4u);
v___x_3724_ = lean_unsigned_to_nat(202u);
v___x_3725_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3726_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3727_ = l_mkPanicMessageWithDecl(v___x_3726_, v___x_3725_, v___x_3724_, v___x_3723_, v___x_3722_);
return v___x_3727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3734_ = l_Lean_stringToMessageData(v___x_3733_);
return v___x_3734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3737_ = l_Lean_stringToMessageData(v___x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3740_, lean_object* v_numMotives_3741_, lean_object* v_numMinors_3742_, lean_object* v___x_3743_, lean_object* v_all_3744_, lean_object* v_head_3745_, lean_object* v_tail_3746_, lean_object* v_recName_3747_, lean_object* v_brecOnGoName_3748_, lean_object* v_levelParams_3749_, lean_object* v_brecOnName_3750_, lean_object* v_brecOnEqName_3751_, lean_object* v_type_3752_, lean_object* v_refArgs_3753_, lean_object* v_refBody_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3760_ = lean_nat_add(v_nParams_3740_, v_numMotives_3741_);
v___x_3761_ = lean_nat_add(v___x_3760_, v_numMinors_3742_);
v___x_3762_ = lean_array_get_size(v_refArgs_3753_);
v___x_3763_ = lean_nat_dec_lt(v___x_3761_, v___x_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec_ref(v_refArgs_3753_);
lean_dec_ref(v_type_3752_);
lean_dec(v_brecOnEqName_3751_);
lean_dec(v_brecOnName_3750_);
lean_dec(v_levelParams_3749_);
lean_dec(v_brecOnGoName_3748_);
lean_dec(v_recName_3747_);
lean_dec(v_tail_3746_);
lean_dec(v_head_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
lean_dec(v_nParams_3740_);
v___x_3764_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3765_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3764_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
return v___x_3765_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3766_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3740_);
lean_inc_ref_n(v_refArgs_3753_, 2);
v___x_3767_ = l_Array_toSubarray___redArg(v_refArgs_3753_, v___x_3766_, v_nParams_3740_);
lean_inc(v___x_3760_);
v___x_3768_ = l_Array_toSubarray___redArg(v_refArgs_3753_, v_nParams_3740_, v___x_3760_);
v___x_3769_ = l_Subarray_copy___redArg(v___x_3768_);
v___x_3770_ = l_Lean_Expr_getAppFn(v_refBody_3754_);
v___x_3771_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3769_, v___x_3770_);
lean_dec_ref(v___x_3770_);
if (lean_obj_tag(v___x_3771_) == 1)
{
lean_object* v_val_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_dec_ref(v_type_3752_);
v_val_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v___x_3773_ = l_Lean_instInhabitedExpr;
v___x_3774_ = lean_unsigned_to_nat(1u);
v___x_3775_ = lean_nat_sub(v___x_3762_, v___x_3774_);
v___x_3776_ = lean_array_get(v___x_3773_, v_refArgs_3753_, v___x_3775_);
lean_inc(v___y_3758_);
lean_inc_ref(v___y_3757_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
lean_inc(v___x_3776_);
v___x_3777_ = lean_infer_type(v___x_3776_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3779_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
lean_inc(v___y_3758_);
lean_inc_ref(v___y_3757_);
lean_inc(v___y_3756_);
lean_inc_ref(v___y_3755_);
v___x_3779_ = lean_infer_type(v_a_3778_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3780_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___x_3781_, 1);
if (lean_obj_tag(v_a_3782_) == 1)
{
lean_object* v_val_3783_; lean_object* v___x_3784_; lean_object* v___f_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; size_t v_sz_3795_; size_t v___x_3796_; lean_object* v___x_3797_; 
v_val_3783_ = lean_ctor_get(v_a_3782_, 0);
lean_inc(v_val_3783_);
lean_dec_ref_known(v_a_3782_, 1);
v___x_3784_ = l_Subarray_copy___redArg(v___x_3767_);
lean_inc_ref(v___x_3769_);
lean_inc_ref(v___x_3784_);
lean_inc(v___x_3743_);
v___f_3785_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3785_, 0, v___x_3743_);
lean_closure_set(v___f_3785_, 1, v___x_3784_);
lean_closure_set(v___f_3785_, 2, v___x_3769_);
lean_closure_set(v___f_3785_, 3, v_all_3744_);
lean_closure_set(v___f_3785_, 4, v___x_3766_);
lean_closure_set(v___f_3785_, 5, v___x_3774_);
v___x_3786_ = lean_array_get_size(v___x_3769_);
v___x_3787_ = l_Array_ofFn___redArg(v___x_3786_, v___f_3785_);
v___x_3788_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3789_ = lean_array_get_size(v___x_3787_);
lean_inc_ref(v___x_3787_);
v___x_3790_ = l_Array_toSubarray___redArg(v___x_3787_, v___x_3766_, v___x_3789_);
v___x_3791_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
lean_ctor_set(v___x_3792_, 1, v___x_3786_);
lean_inc_ref(v___x_3790_);
v___x_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3790_);
lean_ctor_set(v___x_3793_, 1, v___x_3792_);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3788_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v_sz_3795_ = lean_array_size(v___x_3769_);
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3769_, v_sz_3795_, v___x_3796_, v___x_3794_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v_fst_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___f_3808_; uint8_t v___x_3809_; lean_object* v___x_3810_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v_fst_3799_ = lean_ctor_get(v_a_3798_, 0);
lean_inc(v_fst_3799_);
lean_dec(v_a_3798_);
lean_inc(v___x_3761_);
lean_inc_ref(v_refArgs_3753_);
v___x_3800_ = l_Array_toSubarray___redArg(v_refArgs_3753_, v___x_3760_, v___x_3761_);
v___x_3801_ = l_Subarray_copy___redArg(v___x_3800_);
v___x_3802_ = l_Array_toSubarray___redArg(v_refArgs_3753_, v___x_3761_, v___x_3775_);
v___x_3803_ = l_Subarray_copy___redArg(v___x_3802_);
v___x_3804_ = l_Lean_mkLevelMax(v_val_3783_, v_head_3745_);
v___x_3805_ = lean_box_usize(v_sz_3795_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3807_ = lean_box(v___x_3763_);
v___f_3808_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3808_, 0, v___x_3804_);
lean_closure_set(v___f_3808_, 1, v_tail_3746_);
lean_closure_set(v___f_3808_, 2, v_recName_3747_);
lean_closure_set(v___f_3808_, 3, v___x_3784_);
lean_closure_set(v___f_3808_, 4, v___x_3790_);
lean_closure_set(v___f_3808_, 5, v___x_3769_);
lean_closure_set(v___f_3808_, 6, v___x_3805_);
lean_closure_set(v___f_3808_, 7, v___x_3806_);
lean_closure_set(v___f_3808_, 8, v___x_3801_);
lean_closure_set(v___f_3808_, 9, v___x_3787_);
lean_closure_set(v___f_3808_, 10, v___x_3803_);
lean_closure_set(v___f_3808_, 11, v___x_3776_);
lean_closure_set(v___f_3808_, 12, v___x_3774_);
lean_closure_set(v___f_3808_, 13, v___x_3773_);
lean_closure_set(v___f_3808_, 14, v_val_3772_);
lean_closure_set(v___f_3808_, 15, v___x_3807_);
lean_closure_set(v___f_3808_, 16, v_brecOnGoName_3748_);
lean_closure_set(v___f_3808_, 17, v_levelParams_3749_);
lean_closure_set(v___f_3808_, 18, v___x_3743_);
lean_closure_set(v___f_3808_, 19, v_brecOnName_3750_);
lean_closure_set(v___f_3808_, 20, v___x_3766_);
lean_closure_set(v___f_3808_, 21, v_brecOnEqName_3751_);
v___x_3809_ = 0;
v___x_3810_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3799_, v___f_3808_, v___x_3809_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
return v___x_3810_;
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3818_; 
lean_dec_ref(v___x_3790_);
lean_dec_ref(v___x_3787_);
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3783_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec(v_val_3772_);
lean_dec_ref(v___x_3769_);
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec_ref(v_refArgs_3753_);
lean_dec(v_brecOnEqName_3751_);
lean_dec(v_brecOnName_3750_);
lean_dec(v_levelParams_3749_);
lean_dec(v_brecOnGoName_3748_);
lean_dec(v_recName_3747_);
lean_dec(v_tail_3746_);
lean_dec(v_head_3745_);
lean_dec(v___x_3743_);
v_a_3811_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3813_ = v___x_3797_;
v_isShared_3814_ = v_isSharedCheck_3818_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3797_);
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
lean_dec(v_val_3772_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3767_);
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec_ref(v_refArgs_3753_);
lean_dec(v_brecOnEqName_3751_);
lean_dec(v_brecOnName_3750_);
lean_dec(v_levelParams_3749_);
lean_dec(v_brecOnGoName_3748_);
lean_dec(v_recName_3747_);
lean_dec(v_tail_3746_);
lean_dec(v_head_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
v___x_3819_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3820_ = l_Lean_MessageData_ofExpr(v___x_3776_);
v___x_3821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3823_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
return v___x_3824_;
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec(v_val_3772_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3767_);
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec_ref(v_refArgs_3753_);
lean_dec(v_brecOnEqName_3751_);
lean_dec(v_brecOnName_3750_);
lean_dec(v_levelParams_3749_);
lean_dec(v_brecOnGoName_3748_);
lean_dec(v_recName_3747_);
lean_dec(v_tail_3746_);
lean_dec(v_head_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
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
lean_dec(v_val_3772_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3767_);
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec_ref(v_refArgs_3753_);
lean_dec(v_brecOnEqName_3751_);
lean_dec(v_brecOnName_3750_);
lean_dec(v_levelParams_3749_);
lean_dec(v_brecOnGoName_3748_);
lean_dec(v_recName_3747_);
lean_dec(v_tail_3746_);
lean_dec(v_head_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
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
lean_dec(v_val_3772_);
lean_dec_ref(v___x_3769_);
lean_dec_ref(v___x_3767_);
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec_ref(v_refArgs_3753_);
lean_dec(v_brecOnEqName_3751_);
lean_dec(v_brecOnName_3750_);
lean_dec(v_levelParams_3749_);
lean_dec(v_brecOnGoName_3748_);
lean_dec(v_recName_3747_);
lean_dec(v_tail_3746_);
lean_dec(v_head_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
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
lean_dec(v___x_3771_);
lean_dec_ref(v___x_3767_);
lean_dec(v___x_3761_);
lean_dec(v___x_3760_);
lean_dec_ref(v_refArgs_3753_);
lean_dec(v_brecOnEqName_3751_);
lean_dec(v_brecOnName_3750_);
lean_dec(v_levelParams_3749_);
lean_dec(v_brecOnGoName_3748_);
lean_dec(v_recName_3747_);
lean_dec(v_tail_3746_);
lean_dec(v_head_3745_);
lean_dec_ref(v_all_3744_);
lean_dec(v___x_3743_);
v___x_3849_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3850_ = l_Lean_MessageData_ofExpr(v_type_3752_);
v___x_3851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3849_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3851_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___x_3854_ = lean_array_to_list(v___x_3769_);
v___x_3855_ = lean_box(0);
v___x_3856_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3854_, v___x_3855_);
v___x_3857_ = l_Lean_MessageData_ofList(v___x_3856_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3853_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3858_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
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
lean_object* v_all_3864_ = _args[4];
lean_object* v_head_3865_ = _args[5];
lean_object* v_tail_3866_ = _args[6];
lean_object* v_recName_3867_ = _args[7];
lean_object* v_brecOnGoName_3868_ = _args[8];
lean_object* v_levelParams_3869_ = _args[9];
lean_object* v_brecOnName_3870_ = _args[10];
lean_object* v_brecOnEqName_3871_ = _args[11];
lean_object* v_type_3872_ = _args[12];
lean_object* v_refArgs_3873_ = _args[13];
lean_object* v_refBody_3874_ = _args[14];
lean_object* v___y_3875_ = _args[15];
lean_object* v___y_3876_ = _args[16];
lean_object* v___y_3877_ = _args[17];
lean_object* v___y_3878_ = _args[18];
lean_object* v___y_3879_ = _args[19];
_start:
{
lean_object* v_res_3880_; 
v_res_3880_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3860_, v_numMotives_3861_, v_numMinors_3862_, v___x_3863_, v_all_3864_, v_head_3865_, v_tail_3866_, v_recName_3867_, v_brecOnGoName_3868_, v_levelParams_3869_, v_brecOnName_3870_, v_brecOnEqName_3871_, v_type_3872_, v_refArgs_3873_, v_refBody_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_);
lean_dec(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v___y_3876_);
lean_dec_ref(v___y_3875_);
lean_dec_ref(v_refBody_3874_);
lean_dec(v_numMinors_3862_);
lean_dec(v_numMotives_3861_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3883_, lean_object* v_nParams_3884_, lean_object* v_all_3885_, lean_object* v_brecOnName_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v___x_3892_; 
lean_inc(v_recName_3883_);
v___x_3892_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3883_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3924_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3924_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3924_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
if (lean_obj_tag(v_a_3893_) == 7)
{
lean_object* v_val_3897_; lean_object* v_toConstantVal_3898_; lean_object* v_numMotives_3899_; lean_object* v_numMinors_3900_; lean_object* v_levelParams_3901_; lean_object* v_type_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_del_object(v___x_3895_);
v_val_3897_ = lean_ctor_get(v_a_3893_, 0);
lean_inc_ref(v_val_3897_);
lean_dec_ref_known(v_a_3893_, 1);
v_toConstantVal_3898_ = lean_ctor_get(v_val_3897_, 0);
lean_inc_ref(v_toConstantVal_3898_);
v_numMotives_3899_ = lean_ctor_get(v_val_3897_, 4);
lean_inc(v_numMotives_3899_);
v_numMinors_3900_ = lean_ctor_get(v_val_3897_, 5);
lean_inc(v_numMinors_3900_);
lean_dec_ref(v_val_3897_);
v_levelParams_3901_ = lean_ctor_get(v_toConstantVal_3898_, 1);
lean_inc_n(v_levelParams_3901_, 2);
v_type_3902_ = lean_ctor_get(v_toConstantVal_3898_, 2);
lean_inc_ref(v_type_3902_);
lean_dec_ref(v_toConstantVal_3898_);
v___x_3903_ = lean_box(0);
v___x_3904_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3901_, v___x_3903_);
if (lean_obj_tag(v___x_3904_) == 1)
{
lean_object* v_head_3905_; lean_object* v_tail_3906_; lean_object* v___x_3907_; lean_object* v_brecOnGoName_3908_; lean_object* v___x_3909_; lean_object* v_brecOnEqName_3910_; lean_object* v___f_3911_; uint8_t v___x_3912_; lean_object* v___x_3913_; 
v_head_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_head_3905_);
v_tail_3906_ = lean_ctor_get(v___x_3904_, 1);
lean_inc(v_tail_3906_);
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3886_, 2);
v_brecOnGoName_3908_ = l_Lean_Name_str___override(v_brecOnName_3886_, v___x_3907_);
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3910_ = l_Lean_Name_str___override(v_brecOnName_3886_, v___x_3909_);
lean_inc_ref(v_type_3902_);
v___f_3911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 20, 13);
lean_closure_set(v___f_3911_, 0, v_nParams_3884_);
lean_closure_set(v___f_3911_, 1, v_numMotives_3899_);
lean_closure_set(v___f_3911_, 2, v_numMinors_3900_);
lean_closure_set(v___f_3911_, 3, v___x_3904_);
lean_closure_set(v___f_3911_, 4, v_all_3885_);
lean_closure_set(v___f_3911_, 5, v_head_3905_);
lean_closure_set(v___f_3911_, 6, v_tail_3906_);
lean_closure_set(v___f_3911_, 7, v_recName_3883_);
lean_closure_set(v___f_3911_, 8, v_brecOnGoName_3908_);
lean_closure_set(v___f_3911_, 9, v_levelParams_3901_);
lean_closure_set(v___f_3911_, 10, v_brecOnName_3886_);
lean_closure_set(v___f_3911_, 11, v_brecOnEqName_3910_);
lean_closure_set(v___f_3911_, 12, v_type_3902_);
v___x_3912_ = 0;
v___x_3913_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3902_, v___f_3911_, v___x_3912_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
return v___x_3913_;
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_dec(v___x_3904_);
lean_dec_ref(v_type_3902_);
lean_dec(v_levelParams_3901_);
lean_dec(v_numMinors_3900_);
lean_dec(v_numMotives_3899_);
lean_dec(v_brecOnName_3886_);
lean_dec_ref(v_all_3885_);
lean_dec(v_nParams_3884_);
v___x_3914_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3915_ = l_Lean_MessageData_ofName(v_recName_3883_);
v___x_3916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3914_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3918_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_);
return v___x_3919_;
}
}
else
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_dec(v_a_3893_);
lean_dec(v_brecOnName_3886_);
lean_dec_ref(v_all_3885_);
lean_dec(v_nParams_3884_);
lean_dec(v_recName_3883_);
v___x_3920_ = lean_box(0);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3920_);
v___x_3922_ = v___x_3895_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec(v_brecOnName_3886_);
lean_dec_ref(v_all_3885_);
lean_dec(v_nParams_3884_);
lean_dec(v_recName_3883_);
v_a_3925_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3892_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3892_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3933_, lean_object* v_nParams_3934_, lean_object* v_all_3935_, lean_object* v_brecOnName_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v_res_3942_; 
v_res_3942_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3933_, v_nParams_3934_, v_all_3935_, v_brecOnName_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
return v_res_3942_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3943_, lean_object* v___x_3944_, lean_object* v___x_3945_, lean_object* v___x_3946_, lean_object* v___x_3947_, lean_object* v_a_3948_, lean_object* v_b_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v___x_3955_; 
v___x_3955_ = lean_nat_dec_lt(v_a_3948_, v_upperBound_3943_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; 
lean_dec(v_a_3948_);
lean_dec_ref(v___x_3947_);
lean_dec(v___x_3946_);
lean_dec(v___x_3945_);
lean_dec(v___x_3944_);
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_b_3949_);
return v___x_3956_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3957_ = lean_unsigned_to_nat(1u);
v___x_3958_ = lean_nat_add(v_a_3948_, v___x_3957_);
lean_dec(v_a_3948_);
lean_inc_n(v___x_3958_, 2);
lean_inc(v___x_3944_);
v___x_3959_ = lean_name_append_index_after(v___x_3944_, v___x_3958_);
lean_inc(v___x_3945_);
v___x_3960_ = lean_name_append_index_after(v___x_3945_, v___x_3958_);
lean_inc_ref(v___x_3947_);
lean_inc(v___x_3946_);
v___x_3961_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3959_, v___x_3946_, v___x_3947_, v___x_3960_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v___x_3962_; 
lean_dec_ref_known(v___x_3961_, 1);
v___x_3962_ = lean_box(0);
v_a_3948_ = v___x_3958_;
v_b_3949_ = v___x_3962_;
goto _start;
}
else
{
lean_dec(v___x_3958_);
lean_dec_ref(v___x_3947_);
lean_dec(v___x_3946_);
lean_dec(v___x_3945_);
lean_dec(v___x_3944_);
return v___x_3961_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3964_, lean_object* v___x_3965_, lean_object* v___x_3966_, lean_object* v___x_3967_, lean_object* v___x_3968_, lean_object* v_a_3969_, lean_object* v_b_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3964_, v___x_3965_, v___x_3966_, v___x_3967_, v___x_3968_, v_a_3969_, v_b_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v_upperBound_3964_);
return v_res_3976_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3982_ = ((lean_object*)(l_Lean_mkBelow___closed__6));
v___x_3983_ = l_Lean_Name_append(v___x_3982_, v___x_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_options_3990_; lean_object* v_inheritedTraceOptions_3991_; uint8_t v_hasTrace_3992_; uint8_t v___x_3993_; 
v_options_3990_ = lean_ctor_get(v_a_3987_, 2);
v_inheritedTraceOptions_3991_ = lean_ctor_get(v_a_3987_, 13);
v_hasTrace_3992_ = lean_ctor_get_uint8(v_options_3990_, sizeof(void*)*1);
v___x_3993_ = lean_bool_not(v_hasTrace_3992_);
if (v___x_3993_ == 0)
{
lean_object* v___f_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; lean_object* v___x_3997_; lean_object* v___y_3999_; lean_object* v___y_4000_; uint8_t v___y_4001_; lean_object* v_a_4002_; lean_object* v___y_4015_; lean_object* v___y_4016_; uint8_t v___y_4017_; lean_object* v_a_4018_; lean_object* v___y_4021_; lean_object* v___y_4022_; uint8_t v___y_4023_; lean_object* v_a_4024_; lean_object* v___y_4027_; lean_object* v___y_4028_; uint8_t v___y_4029_; lean_object* v_a_4030_; lean_object* v___y_4040_; lean_object* v___y_4041_; uint8_t v___y_4042_; lean_object* v_a_4043_; lean_object* v___y_4046_; lean_object* v___y_4047_; uint8_t v___y_4048_; lean_object* v_a_4049_; uint8_t v___y_4052_; uint8_t v_a_4122_; 
lean_inc(v_indName_3984_);
v___f_3994_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3994_, 0, v_indName_3984_);
v___x_3995_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3996_ = 1;
v___x_3997_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
if (v_hasTrace_3992_ == 0)
{
v_a_4122_ = v_hasTrace_3992_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4200_; uint8_t v___x_4201_; 
v___x_4200_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3991_, v_options_3990_, v___x_4200_);
if (v___x_4201_ == 0)
{
v_a_4122_ = v___x_4201_;
goto v___jp_4121_;
}
else
{
v___y_4052_ = v___x_4201_;
goto v___jp_4051_;
}
}
v___jp_3998_:
{
lean_object* v___x_4003_; double v___x_4004_; double v___x_4005_; double v___x_4006_; double v___x_4007_; double v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4003_ = lean_io_mono_nanos_now();
v___x_4004_ = lean_float_of_nat(v___y_4000_);
v___x_4005_ = lean_float_once(&l_Lean_mkBelow___closed__4, &l_Lean_mkBelow___closed__4_once, _init_l_Lean_mkBelow___closed__4);
v___x_4006_ = lean_float_div(v___x_4004_, v___x_4005_);
v___x_4007_ = lean_float_of_nat(v___x_4003_);
v___x_4008_ = lean_float_div(v___x_4007_, v___x_4005_);
v___x_4009_ = lean_box_float(v___x_4006_);
v___x_4010_ = lean_box_float(v___x_4008_);
v___x_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4012_, 0, v_a_4002_);
lean_ctor_set(v___x_4012_, 1, v___x_4011_);
v___x_4013_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2(v___x_3995_, v___x_3996_, v___x_3997_, v_options_3990_, v___y_4001_, v___y_3999_, v___f_3994_, v___x_4012_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
return v___x_4013_;
}
v___jp_4014_:
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4019_, 0, v_a_4018_);
v___y_3999_ = v___y_4015_;
v___y_4000_ = v___y_4016_;
v___y_4001_ = v___y_4017_;
v_a_4002_ = v___x_4019_;
goto v___jp_3998_;
}
v___jp_4020_:
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4025_, 0, v_a_4024_);
v___y_3999_ = v___y_4021_;
v___y_4000_ = v___y_4022_;
v___y_4001_ = v___y_4023_;
v_a_4002_ = v___x_4025_;
goto v___jp_3998_;
}
v___jp_4026_:
{
lean_object* v___x_4031_; double v___x_4032_; double v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4031_ = lean_io_get_num_heartbeats();
v___x_4032_ = lean_float_of_nat(v___y_4028_);
v___x_4033_ = lean_float_of_nat(v___x_4031_);
v___x_4034_ = lean_box_float(v___x_4032_);
v___x_4035_ = lean_box_float(v___x_4033_);
v___x_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4034_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
v___x_4037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4037_, 0, v_a_4030_);
lean_ctor_set(v___x_4037_, 1, v___x_4036_);
v___x_4038_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__2(v___x_3995_, v___x_3996_, v___x_3997_, v_options_3990_, v___y_4029_, v___y_4027_, v___f_3994_, v___x_4037_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
return v___x_4038_;
}
v___jp_4039_:
{
lean_object* v___x_4044_; 
v___x_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4044_, 0, v_a_4043_);
v___y_4027_ = v___y_4040_;
v___y_4028_ = v___y_4041_;
v___y_4029_ = v___y_4042_;
v_a_4030_ = v___x_4044_;
goto v___jp_4026_;
}
v___jp_4045_:
{
lean_object* v___x_4050_; 
v___x_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4050_, 0, v_a_4049_);
v___y_4027_ = v___y_4046_;
v___y_4028_ = v___y_4047_;
v___y_4029_ = v___y_4048_;
v_a_4030_ = v___x_4050_;
goto v___jp_4026_;
}
v___jp_4051_:
{
lean_object* v___x_4053_; lean_object* v_a_4054_; lean_object* v___x_4055_; uint8_t v___x_4056_; 
v___x_4053_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__0___redArg(v_a_3988_);
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref(v___x_4053_);
v___x_4055_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4056_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__1(v_options_3990_, v___x_4055_);
if (v___x_4056_ == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3984_);
v___x_4058_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4059_);
lean_dec_ref_known(v___x_4058_, 1);
if (lean_obj_tag(v_a_4059_) == 5)
{
lean_object* v_val_4060_; uint8_t v_isRec_4061_; 
v_val_4060_ = lean_ctor_get(v_a_4059_, 0);
lean_inc_ref(v_val_4060_);
lean_dec_ref_known(v_a_4059_, 1);
v_isRec_4061_ = lean_ctor_get_uint8(v_val_4060_, sizeof(void*)*6);
if (v_isRec_4061_ == 0)
{
lean_object* v___x_4062_; 
lean_dec_ref(v_val_4060_);
lean_dec(v_indName_3984_);
v___x_4062_ = lean_box(0);
v___y_4021_ = v_a_4054_;
v___y_4022_ = v___x_4057_;
v___y_4023_ = v___y_4052_;
v_a_4024_ = v___x_4062_;
goto v___jp_4020_;
}
else
{
lean_object* v_toConstantVal_4063_; lean_object* v_numParams_4064_; lean_object* v_all_4065_; lean_object* v_numNested_4066_; lean_object* v_type_4067_; lean_object* v___x_4068_; 
v_toConstantVal_4063_ = lean_ctor_get(v_val_4060_, 0);
lean_inc_ref(v_toConstantVal_4063_);
v_numParams_4064_ = lean_ctor_get(v_val_4060_, 1);
lean_inc(v_numParams_4064_);
v_all_4065_ = lean_ctor_get(v_val_4060_, 3);
lean_inc(v_all_4065_);
v_numNested_4066_ = lean_ctor_get(v_val_4060_, 5);
lean_inc(v_numNested_4066_);
lean_dec_ref(v_val_4060_);
v_type_4067_ = lean_ctor_get(v_toConstantVal_4063_, 2);
lean_inc_ref(v_type_4067_);
lean_dec_ref(v_toConstantVal_4063_);
v___x_4068_ = l_Lean_Meta_isPropFormerType(v_type_4067_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4068_) == 0)
{
lean_object* v_a_4069_; uint8_t v___x_4070_; 
v_a_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v___x_4070_ = lean_unbox(v_a_4069_);
lean_dec(v_a_4069_);
if (v___x_4070_ == 0)
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
lean_inc_n(v_indName_3984_, 2);
v___x_4071_ = l_Lean_mkRecName(v_indName_3984_);
v___x_4072_ = l_Lean_mkBRecOnName(v_indName_3984_);
lean_inc(v_all_4065_);
v___x_4073_ = lean_array_mk(v_all_4065_);
lean_inc(v___x_4072_);
lean_inc_ref(v___x_4073_);
lean_inc(v_numParams_4064_);
lean_inc(v___x_4071_);
v___x_4074_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4071_, v_numParams_4064_, v___x_4073_, v___x_4072_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; uint8_t v___x_4078_; 
lean_dec_ref_known(v___x_4074_, 1);
v___x_4075_ = lean_box(0);
v___x_4076_ = lean_unsigned_to_nat(0u);
v___x_4077_ = l_List_get_x21Internal___redArg(v___x_4075_, v_all_4065_, v___x_4076_);
lean_dec(v_all_4065_);
v___x_4078_ = lean_name_eq(v___x_4077_, v_indName_3984_);
lean_dec(v_indName_3984_);
lean_dec(v___x_4077_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; 
lean_dec_ref(v___x_4073_);
lean_dec(v___x_4072_);
lean_dec(v___x_4071_);
lean_dec(v_numNested_4066_);
lean_dec(v_numParams_4064_);
v___x_4079_ = lean_box(0);
v___y_4021_ = v_a_4054_;
v___y_4022_ = v___x_4057_;
v___y_4023_ = v___y_4052_;
v_a_4024_ = v___x_4079_;
goto v___jp_4020_;
}
else
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = lean_box(0);
v___x_4081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4066_, v___x_4071_, v___x_4072_, v_numParams_4064_, v___x_4073_, v___x_4076_, v___x_4080_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_numNested_4066_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_dec_ref_known(v___x_4081_, 1);
v___y_4021_ = v_a_4054_;
v___y_4022_ = v___x_4057_;
v___y_4023_ = v___y_4052_;
v_a_4024_ = v___x_4080_;
goto v___jp_4020_;
}
else
{
lean_object* v_a_4082_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref_known(v___x_4081_, 1);
v___y_4015_ = v_a_4054_;
v___y_4016_ = v___x_4057_;
v___y_4017_ = v___y_4052_;
v_a_4018_ = v_a_4082_;
goto v___jp_4014_;
}
}
}
else
{
lean_dec_ref(v___x_4073_);
lean_dec(v___x_4072_);
lean_dec(v___x_4071_);
lean_dec(v_numNested_4066_);
lean_dec(v_all_4065_);
lean_dec(v_numParams_4064_);
lean_dec(v_indName_3984_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4083_; 
v_a_4083_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4083_);
lean_dec_ref_known(v___x_4074_, 1);
v___y_4021_ = v_a_4054_;
v___y_4022_ = v___x_4057_;
v___y_4023_ = v___y_4052_;
v_a_4024_ = v_a_4083_;
goto v___jp_4020_;
}
else
{
lean_object* v_a_4084_; 
v_a_4084_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4074_, 1);
v___y_4015_ = v_a_4054_;
v___y_4016_ = v___x_4057_;
v___y_4017_ = v___y_4052_;
v_a_4018_ = v_a_4084_;
goto v___jp_4014_;
}
}
}
else
{
lean_object* v___x_4085_; 
lean_dec(v_numNested_4066_);
lean_dec(v_all_4065_);
lean_dec(v_numParams_4064_);
lean_dec(v_indName_3984_);
v___x_4085_ = lean_box(0);
v___y_4021_ = v_a_4054_;
v___y_4022_ = v___x_4057_;
v___y_4023_ = v___y_4052_;
v_a_4024_ = v___x_4085_;
goto v___jp_4020_;
}
}
else
{
lean_object* v_a_4086_; 
lean_dec(v_numNested_4066_);
lean_dec(v_all_4065_);
lean_dec(v_numParams_4064_);
lean_dec(v_indName_3984_);
v_a_4086_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___x_4068_, 1);
v___y_4015_ = v_a_4054_;
v___y_4016_ = v___x_4057_;
v___y_4017_ = v___y_4052_;
v_a_4018_ = v_a_4086_;
goto v___jp_4014_;
}
}
}
else
{
lean_object* v___x_4087_; 
lean_dec(v_a_4059_);
lean_dec(v_indName_3984_);
v___x_4087_ = lean_box(0);
v___y_4021_ = v_a_4054_;
v___y_4022_ = v___x_4057_;
v___y_4023_ = v___y_4052_;
v_a_4024_ = v___x_4087_;
goto v___jp_4020_;
}
}
else
{
lean_object* v_a_4088_; 
lean_dec(v_indName_3984_);
v_a_4088_ = lean_ctor_get(v___x_4058_, 0);
lean_inc(v_a_4088_);
lean_dec_ref_known(v___x_4058_, 1);
v___y_4015_ = v_a_4054_;
v___y_4016_ = v___x_4057_;
v___y_4017_ = v___y_4052_;
v_a_4018_ = v_a_4088_;
goto v___jp_4014_;
}
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3984_);
v___x_4090_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
if (lean_obj_tag(v_a_4091_) == 5)
{
lean_object* v_val_4092_; uint8_t v_isRec_4093_; 
v_val_4092_ = lean_ctor_get(v_a_4091_, 0);
lean_inc_ref(v_val_4092_);
lean_dec_ref_known(v_a_4091_, 1);
v_isRec_4093_ = lean_ctor_get_uint8(v_val_4092_, sizeof(void*)*6);
if (v_isRec_4093_ == 0)
{
lean_object* v___x_4094_; 
lean_dec_ref(v_val_4092_);
lean_dec(v_indName_3984_);
v___x_4094_ = lean_box(0);
v___y_4046_ = v_a_4054_;
v___y_4047_ = v___x_4089_;
v___y_4048_ = v___y_4052_;
v_a_4049_ = v___x_4094_;
goto v___jp_4045_;
}
else
{
lean_object* v_toConstantVal_4095_; lean_object* v_numParams_4096_; lean_object* v_all_4097_; lean_object* v_numNested_4098_; lean_object* v_type_4099_; lean_object* v___x_4100_; 
v_toConstantVal_4095_ = lean_ctor_get(v_val_4092_, 0);
lean_inc_ref(v_toConstantVal_4095_);
v_numParams_4096_ = lean_ctor_get(v_val_4092_, 1);
lean_inc(v_numParams_4096_);
v_all_4097_ = lean_ctor_get(v_val_4092_, 3);
lean_inc(v_all_4097_);
v_numNested_4098_ = lean_ctor_get(v_val_4092_, 5);
lean_inc(v_numNested_4098_);
lean_dec_ref(v_val_4092_);
v_type_4099_ = lean_ctor_get(v_toConstantVal_4095_, 2);
lean_inc_ref(v_type_4099_);
lean_dec_ref(v_toConstantVal_4095_);
v___x_4100_ = l_Lean_Meta_isPropFormerType(v_type_4099_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; uint8_t v___x_4102_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4100_, 1);
v___x_4102_ = lean_unbox(v_a_4101_);
lean_dec(v_a_4101_);
if (v___x_4102_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
lean_inc_n(v_indName_3984_, 2);
v___x_4103_ = l_Lean_mkRecName(v_indName_3984_);
v___x_4104_ = l_Lean_mkBRecOnName(v_indName_3984_);
lean_inc(v_all_4097_);
v___x_4105_ = lean_array_mk(v_all_4097_);
lean_inc(v___x_4104_);
lean_inc_ref(v___x_4105_);
lean_inc(v_numParams_4096_);
lean_inc(v___x_4103_);
v___x_4106_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4103_, v_numParams_4096_, v___x_4105_, v___x_4104_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
lean_dec_ref_known(v___x_4106_, 1);
v___x_4107_ = lean_box(0);
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = l_List_get_x21Internal___redArg(v___x_4107_, v_all_4097_, v___x_4108_);
lean_dec(v_all_4097_);
v___x_4110_ = lean_name_eq(v___x_4109_, v_indName_3984_);
lean_dec(v_indName_3984_);
lean_dec(v___x_4109_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; 
lean_dec_ref(v___x_4105_);
lean_dec(v___x_4104_);
lean_dec(v___x_4103_);
lean_dec(v_numNested_4098_);
lean_dec(v_numParams_4096_);
v___x_4111_ = lean_box(0);
v___y_4046_ = v_a_4054_;
v___y_4047_ = v___x_4089_;
v___y_4048_ = v___y_4052_;
v_a_4049_ = v___x_4111_;
goto v___jp_4045_;
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_box(0);
v___x_4113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4098_, v___x_4103_, v___x_4104_, v_numParams_4096_, v___x_4105_, v___x_4108_, v___x_4112_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_numNested_4098_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_dec_ref_known(v___x_4113_, 1);
v___y_4046_ = v_a_4054_;
v___y_4047_ = v___x_4089_;
v___y_4048_ = v___y_4052_;
v_a_4049_ = v___x_4112_;
goto v___jp_4045_;
}
else
{
lean_object* v_a_4114_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
v___y_4040_ = v_a_4054_;
v___y_4041_ = v___x_4089_;
v___y_4042_ = v___y_4052_;
v_a_4043_ = v_a_4114_;
goto v___jp_4039_;
}
}
}
else
{
lean_dec_ref(v___x_4105_);
lean_dec(v___x_4104_);
lean_dec(v___x_4103_);
lean_dec(v_numNested_4098_);
lean_dec(v_all_4097_);
lean_dec(v_numParams_4096_);
lean_dec(v_indName_3984_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4115_; 
v_a_4115_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4115_);
lean_dec_ref_known(v___x_4106_, 1);
v___y_4046_ = v_a_4054_;
v___y_4047_ = v___x_4089_;
v___y_4048_ = v___y_4052_;
v_a_4049_ = v_a_4115_;
goto v___jp_4045_;
}
else
{
lean_object* v_a_4116_; 
v_a_4116_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4116_);
lean_dec_ref_known(v___x_4106_, 1);
v___y_4040_ = v_a_4054_;
v___y_4041_ = v___x_4089_;
v___y_4042_ = v___y_4052_;
v_a_4043_ = v_a_4116_;
goto v___jp_4039_;
}
}
}
else
{
lean_object* v___x_4117_; 
lean_dec(v_numNested_4098_);
lean_dec(v_all_4097_);
lean_dec(v_numParams_4096_);
lean_dec(v_indName_3984_);
v___x_4117_ = lean_box(0);
v___y_4046_ = v_a_4054_;
v___y_4047_ = v___x_4089_;
v___y_4048_ = v___y_4052_;
v_a_4049_ = v___x_4117_;
goto v___jp_4045_;
}
}
else
{
lean_object* v_a_4118_; 
lean_dec(v_numNested_4098_);
lean_dec(v_all_4097_);
lean_dec(v_numParams_4096_);
lean_dec(v_indName_3984_);
v_a_4118_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4118_);
lean_dec_ref_known(v___x_4100_, 1);
v___y_4040_ = v_a_4054_;
v___y_4041_ = v___x_4089_;
v___y_4042_ = v___y_4052_;
v_a_4043_ = v_a_4118_;
goto v___jp_4039_;
}
}
}
else
{
lean_object* v___x_4119_; 
lean_dec(v_a_4091_);
lean_dec(v_indName_3984_);
v___x_4119_ = lean_box(0);
v___y_4046_ = v_a_4054_;
v___y_4047_ = v___x_4089_;
v___y_4048_ = v___y_4052_;
v_a_4049_ = v___x_4119_;
goto v___jp_4045_;
}
}
else
{
lean_object* v_a_4120_; 
lean_dec(v_indName_3984_);
v_a_4120_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4120_);
lean_dec_ref_known(v___x_4090_, 1);
v___y_4040_ = v_a_4054_;
v___y_4041_ = v___x_4089_;
v___y_4042_ = v___y_4052_;
v_a_4043_ = v_a_4120_;
goto v___jp_4039_;
}
}
}
v___jp_4121_:
{
lean_object* v___x_4123_; uint8_t v___x_4124_; 
v___x_4123_ = l_Lean_trace_profiler;
v___x_4124_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__1(v_options_3990_, v___x_4123_);
if (v___x_4124_ == 0)
{
lean_object* v___x_4125_; 
lean_dec_ref(v___f_3994_);
lean_inc(v_indName_3984_);
v___x_4125_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4191_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4128_ = v___x_4125_;
v_isShared_4129_ = v_isSharedCheck_4191_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4125_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4191_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
if (lean_obj_tag(v_a_4126_) == 5)
{
lean_object* v_val_4130_; uint8_t v_isRec_4131_; 
v_val_4130_ = lean_ctor_get(v_a_4126_, 0);
lean_inc_ref(v_val_4130_);
lean_dec_ref_known(v_a_4126_, 1);
v_isRec_4131_ = lean_ctor_get_uint8(v_val_4130_, sizeof(void*)*6);
if (v_isRec_4131_ == 0)
{
lean_object* v___x_4132_; lean_object* v___x_4134_; 
lean_dec_ref(v_val_4130_);
lean_dec(v_indName_3984_);
v___x_4132_ = lean_box(0);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4132_);
v___x_4134_ = v___x_4128_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
else
{
lean_object* v_toConstantVal_4136_; lean_object* v_numParams_4137_; lean_object* v_all_4138_; lean_object* v_numNested_4139_; lean_object* v_type_4140_; lean_object* v___x_4141_; 
lean_del_object(v___x_4128_);
v_toConstantVal_4136_ = lean_ctor_get(v_val_4130_, 0);
lean_inc_ref(v_toConstantVal_4136_);
v_numParams_4137_ = lean_ctor_get(v_val_4130_, 1);
lean_inc(v_numParams_4137_);
v_all_4138_ = lean_ctor_get(v_val_4130_, 3);
lean_inc(v_all_4138_);
v_numNested_4139_ = lean_ctor_get(v_val_4130_, 5);
lean_inc(v_numNested_4139_);
lean_dec_ref(v_val_4130_);
v_type_4140_ = lean_ctor_get(v_toConstantVal_4136_, 2);
lean_inc_ref(v_type_4140_);
lean_dec_ref(v_toConstantVal_4136_);
v___x_4141_ = l_Lean_Meta_isPropFormerType(v_type_4140_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4178_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4178_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4178_ == 0)
{
v___x_4144_ = v___x_4141_;
v_isShared_4145_ = v_isSharedCheck_4178_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4141_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4178_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
uint8_t v___x_4146_; 
v___x_4146_ = lean_unbox(v_a_4142_);
lean_dec(v_a_4142_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_del_object(v___x_4144_);
lean_inc_n(v_indName_3984_, 2);
v___x_4147_ = l_Lean_mkRecName(v_indName_3984_);
v___x_4148_ = l_Lean_mkBRecOnName(v_indName_3984_);
lean_inc(v_all_4138_);
v___x_4149_ = lean_array_mk(v_all_4138_);
lean_inc(v___x_4148_);
lean_inc_ref(v___x_4149_);
lean_inc(v_numParams_4137_);
lean_inc(v___x_4147_);
v___x_4150_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4147_, v_numParams_4137_, v___x_4149_, v___x_4148_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4172_; 
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4172_ == 0)
{
lean_object* v_unused_4173_; 
v_unused_4173_ = lean_ctor_get(v___x_4150_, 0);
lean_dec(v_unused_4173_);
v___x_4152_ = v___x_4150_;
v_isShared_4153_ = v_isSharedCheck_4172_;
goto v_resetjp_4151_;
}
else
{
lean_dec(v___x_4150_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4172_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v___x_4154_ = lean_box(0);
v___x_4155_ = lean_unsigned_to_nat(0u);
v___x_4156_ = l_List_get_x21Internal___redArg(v___x_4154_, v_all_4138_, v___x_4155_);
lean_dec(v_all_4138_);
v___x_4157_ = lean_name_eq(v___x_4156_, v_indName_3984_);
lean_dec(v_indName_3984_);
lean_dec(v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_dec_ref(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec(v_numNested_4139_);
lean_dec(v_numParams_4137_);
v___x_4158_ = lean_box(0);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v___x_4158_);
v___x_4160_ = v___x_4152_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_del_object(v___x_4152_);
v___x_4162_ = lean_box(0);
v___x_4163_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4139_, v___x_4147_, v___x_4148_, v_numParams_4137_, v___x_4149_, v___x_4155_, v___x_4162_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_numNested_4139_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4170_ == 0)
{
lean_object* v_unused_4171_; 
v_unused_4171_ = lean_ctor_get(v___x_4163_, 0);
lean_dec(v_unused_4171_);
v___x_4165_ = v___x_4163_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_dec(v___x_4163_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4162_);
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4162_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
else
{
return v___x_4163_;
}
}
}
}
else
{
lean_dec_ref(v___x_4149_);
lean_dec(v___x_4148_);
lean_dec(v___x_4147_);
lean_dec(v_numNested_4139_);
lean_dec(v_all_4138_);
lean_dec(v_numParams_4137_);
lean_dec(v_indName_3984_);
return v___x_4150_;
}
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4176_; 
lean_dec(v_numNested_4139_);
lean_dec(v_all_4138_);
lean_dec(v_numParams_4137_);
lean_dec(v_indName_3984_);
v___x_4174_ = lean_box(0);
if (v_isShared_4145_ == 0)
{
lean_ctor_set(v___x_4144_, 0, v___x_4174_);
v___x_4176_ = v___x_4144_;
goto v_reusejp_4175_;
}
else
{
lean_object* v_reuseFailAlloc_4177_; 
v_reuseFailAlloc_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4177_, 0, v___x_4174_);
v___x_4176_ = v_reuseFailAlloc_4177_;
goto v_reusejp_4175_;
}
v_reusejp_4175_:
{
return v___x_4176_;
}
}
}
}
else
{
lean_object* v_a_4179_; lean_object* v___x_4181_; uint8_t v_isShared_4182_; uint8_t v_isSharedCheck_4186_; 
lean_dec(v_numNested_4139_);
lean_dec(v_all_4138_);
lean_dec(v_numParams_4137_);
lean_dec(v_indName_3984_);
v_a_4179_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4186_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4181_ = v___x_4141_;
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
else
{
lean_inc(v_a_4179_);
lean_dec(v___x_4141_);
v___x_4181_ = lean_box(0);
v_isShared_4182_ = v_isSharedCheck_4186_;
goto v_resetjp_4180_;
}
v_resetjp_4180_:
{
lean_object* v___x_4184_; 
if (v_isShared_4182_ == 0)
{
v___x_4184_ = v___x_4181_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4179_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
}
}
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4189_; 
lean_dec(v_a_4126_);
lean_dec(v_indName_3984_);
v___x_4187_ = lean_box(0);
if (v_isShared_4129_ == 0)
{
lean_ctor_set(v___x_4128_, 0, v___x_4187_);
v___x_4189_ = v___x_4128_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4187_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
else
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4199_; 
lean_dec(v_indName_3984_);
v_a_4192_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4199_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4199_ == 0)
{
v___x_4194_ = v___x_4125_;
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4125_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4199_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4197_; 
if (v_isShared_4195_ == 0)
{
v___x_4197_ = v___x_4194_;
goto v_reusejp_4196_;
}
else
{
lean_object* v_reuseFailAlloc_4198_; 
v_reuseFailAlloc_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
v___x_4197_ = v_reuseFailAlloc_4198_;
goto v_reusejp_4196_;
}
v_reusejp_4196_:
{
return v___x_4197_;
}
}
}
}
else
{
v___y_4052_ = v_a_4122_;
goto v___jp_4051_;
}
}
}
else
{
lean_object* v___x_4202_; 
lean_inc(v_indName_3984_);
v___x_4202_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4268_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4205_ = v___x_4202_;
v_isShared_4206_ = v_isSharedCheck_4268_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4202_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4268_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
if (lean_obj_tag(v_a_4203_) == 5)
{
lean_object* v_val_4207_; uint8_t v_isRec_4208_; 
v_val_4207_ = lean_ctor_get(v_a_4203_, 0);
lean_inc_ref(v_val_4207_);
lean_dec_ref_known(v_a_4203_, 1);
v_isRec_4208_ = lean_ctor_get_uint8(v_val_4207_, sizeof(void*)*6);
if (v_isRec_4208_ == 0)
{
lean_object* v___x_4209_; lean_object* v___x_4211_; 
lean_dec_ref(v_val_4207_);
lean_dec(v_indName_3984_);
v___x_4209_ = lean_box(0);
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 0, v___x_4209_);
v___x_4211_ = v___x_4205_;
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
lean_object* v_toConstantVal_4213_; lean_object* v_numParams_4214_; lean_object* v_all_4215_; lean_object* v_numNested_4216_; lean_object* v_type_4217_; lean_object* v___x_4218_; 
lean_del_object(v___x_4205_);
v_toConstantVal_4213_ = lean_ctor_get(v_val_4207_, 0);
lean_inc_ref(v_toConstantVal_4213_);
v_numParams_4214_ = lean_ctor_get(v_val_4207_, 1);
lean_inc(v_numParams_4214_);
v_all_4215_ = lean_ctor_get(v_val_4207_, 3);
lean_inc(v_all_4215_);
v_numNested_4216_ = lean_ctor_get(v_val_4207_, 5);
lean_inc(v_numNested_4216_);
lean_dec_ref(v_val_4207_);
v_type_4217_ = lean_ctor_get(v_toConstantVal_4213_, 2);
lean_inc_ref(v_type_4217_);
lean_dec_ref(v_toConstantVal_4213_);
v___x_4218_ = l_Lean_Meta_isPropFormerType(v_type_4217_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4218_) == 0)
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4255_; 
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4255_ == 0)
{
v___x_4221_ = v___x_4218_;
v_isShared_4222_ = v_isSharedCheck_4255_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4218_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4255_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
uint8_t v___x_4223_; 
v___x_4223_ = lean_unbox(v_a_4219_);
lean_dec(v_a_4219_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_del_object(v___x_4221_);
lean_inc_n(v_indName_3984_, 2);
v___x_4224_ = l_Lean_mkRecName(v_indName_3984_);
v___x_4225_ = l_Lean_mkBRecOnName(v_indName_3984_);
lean_inc(v_all_4215_);
v___x_4226_ = lean_array_mk(v_all_4215_);
lean_inc(v___x_4225_);
lean_inc_ref(v___x_4226_);
lean_inc(v_numParams_4214_);
lean_inc(v___x_4224_);
v___x_4227_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4224_, v_numParams_4214_, v___x_4226_, v___x_4225_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4249_; 
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4249_ == 0)
{
lean_object* v_unused_4250_; 
v_unused_4250_ = lean_ctor_get(v___x_4227_, 0);
lean_dec(v_unused_4250_);
v___x_4229_ = v___x_4227_;
v_isShared_4230_ = v_isSharedCheck_4249_;
goto v_resetjp_4228_;
}
else
{
lean_dec(v___x_4227_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4249_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; 
v___x_4231_ = lean_box(0);
v___x_4232_ = lean_unsigned_to_nat(0u);
v___x_4233_ = l_List_get_x21Internal___redArg(v___x_4231_, v_all_4215_, v___x_4232_);
lean_dec(v_all_4215_);
v___x_4234_ = lean_name_eq(v___x_4233_, v_indName_3984_);
lean_dec(v_indName_3984_);
lean_dec(v___x_4233_);
if (v___x_4234_ == 0)
{
lean_object* v___x_4235_; lean_object* v___x_4237_; 
lean_dec_ref(v___x_4226_);
lean_dec(v___x_4225_);
lean_dec(v___x_4224_);
lean_dec(v_numNested_4216_);
lean_dec(v_numParams_4214_);
v___x_4235_ = lean_box(0);
if (v_isShared_4230_ == 0)
{
lean_ctor_set(v___x_4229_, 0, v___x_4235_);
v___x_4237_ = v___x_4229_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v___x_4235_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
else
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
lean_del_object(v___x_4229_);
v___x_4239_ = lean_box(0);
v___x_4240_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4216_, v___x_4224_, v___x_4225_, v_numParams_4214_, v___x_4226_, v___x_4232_, v___x_4239_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_);
lean_dec(v_numNested_4216_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4247_ == 0)
{
lean_object* v_unused_4248_; 
v_unused_4248_ = lean_ctor_get(v___x_4240_, 0);
lean_dec(v_unused_4248_);
v___x_4242_ = v___x_4240_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_dec(v___x_4240_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
lean_ctor_set(v___x_4242_, 0, v___x_4239_);
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v___x_4239_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
else
{
return v___x_4240_;
}
}
}
}
else
{
lean_dec_ref(v___x_4226_);
lean_dec(v___x_4225_);
lean_dec(v___x_4224_);
lean_dec(v_numNested_4216_);
lean_dec(v_all_4215_);
lean_dec(v_numParams_4214_);
lean_dec(v_indName_3984_);
return v___x_4227_;
}
}
else
{
lean_object* v___x_4251_; lean_object* v___x_4253_; 
lean_dec(v_numNested_4216_);
lean_dec(v_all_4215_);
lean_dec(v_numParams_4214_);
lean_dec(v_indName_3984_);
v___x_4251_ = lean_box(0);
if (v_isShared_4222_ == 0)
{
lean_ctor_set(v___x_4221_, 0, v___x_4251_);
v___x_4253_ = v___x_4221_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
}
else
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4263_; 
lean_dec(v_numNested_4216_);
lean_dec(v_all_4215_);
lean_dec(v_numParams_4214_);
lean_dec(v_indName_3984_);
v_a_4256_ = lean_ctor_get(v___x_4218_, 0);
v_isSharedCheck_4263_ = !lean_is_exclusive(v___x_4218_);
if (v_isSharedCheck_4263_ == 0)
{
v___x_4258_ = v___x_4218_;
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4218_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4263_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4261_; 
if (v_isShared_4259_ == 0)
{
v___x_4261_ = v___x_4258_;
goto v_reusejp_4260_;
}
else
{
lean_object* v_reuseFailAlloc_4262_; 
v_reuseFailAlloc_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4262_, 0, v_a_4256_);
v___x_4261_ = v_reuseFailAlloc_4262_;
goto v_reusejp_4260_;
}
v_reusejp_4260_:
{
return v___x_4261_;
}
}
}
}
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4266_; 
lean_dec(v_a_4203_);
lean_dec(v_indName_3984_);
v___x_4264_ = lean_box(0);
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 0, v___x_4264_);
v___x_4266_ = v___x_4205_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v_indName_3984_);
v_a_4269_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4202_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4202_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l_Lean_mkBRecOn(v_indName_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
return v_res_4283_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4284_, lean_object* v___x_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v___x_4288_, lean_object* v_inst_4289_, lean_object* v_R_4290_, lean_object* v_a_4291_, lean_object* v_b_4292_, lean_object* v_c_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4284_, v___x_4285_, v___x_4286_, v___x_4287_, v___x_4288_, v_a_4291_, v_b_4292_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v___x_4303_, lean_object* v___x_4304_, lean_object* v_inst_4305_, lean_object* v_R_4306_, lean_object* v_a_4307_, lean_object* v_b_4308_, lean_object* v_c_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4300_, v___x_4301_, v___x_4302_, v___x_4303_, v___x_4304_, v_inst_4305_, v_R_4306_, v_a_4307_, v_b_4308_, v_c_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v_upperBound_4300_);
return v_res_4315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4361_ = lean_unsigned_to_nat(2304625798u);
v___x_4362_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4363_ = l_Lean_Name_num___override(v___x_4362_, v___x_4361_);
return v___x_4363_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4366_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4367_ = l_Lean_Name_str___override(v___x_4366_, v___x_4365_);
return v___x_4367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4370_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4371_ = l_Lean_Name_str___override(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4372_ = lean_unsigned_to_nat(2u);
v___x_4373_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4374_ = l_Lean_Name_num___override(v___x_4373_, v___x_4372_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4376_; uint8_t v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4376_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4377_ = 0;
v___x_4378_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4379_ = l_Lean_registerTraceClass(v___x_4376_, v___x_4377_, v___x_4378_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4381_;
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
