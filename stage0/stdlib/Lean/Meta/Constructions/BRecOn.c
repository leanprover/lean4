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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_mkBelowName(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkBRecOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mkBRecOn"};
static const lean_object* l_Lean_mkBRecOn___closed__0 = (const lean_object*)&l_Lean_mkBRecOn___closed__0_value;
static const lean_ctor_object l_Lean_mkBRecOn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkBelow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_mkBRecOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkBRecOn___closed__1_value_aux_0),((lean_object*)&l_Lean_mkBRecOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 5, 240, 19, 65, 164, 203, 201)}};
static const lean_object* l_Lean_mkBRecOn___closed__1 = (const lean_object*)&l_Lean_mkBRecOn___closed__1_value;
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
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
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
uint8_t v___x_2172__boxed_100_; lean_object* v_res_101_; 
v___x_2172__boxed_100_ = lean_unbox(v___x_92_);
v_res_101_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_91_, v___x_2172__boxed_100_, v_args_93_, v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
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
v___x_109_ = lean_apply_6(v_k_102_, v_b_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_, lean_box(0));
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0___boxed(lean_object* v_k_110_, lean_object* v_b_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___redArg___lam__0(v_k_110_, v_b_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
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
lean_inc(v___y_222_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
v___x_225_ = l_Lean_Meta_mkPProd(v_arg__type_211_, v___x_224_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; uint8_t v___x_227_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_225_);
v___x_227_ = 1;
v___x_228_ = l_Lean_Meta_mkForallFVars(v_arg__args_210_, v_a_226_, v___x_212_, v___x_213_, v___x_213_, v___x_227_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_228_);
v___x_230_ = lean_array_push(v_prods_214_, v_a_229_);
lean_inc(v___y_222_);
lean_inc_ref(v___y_221_);
lean_inc(v___y_220_);
lean_inc_ref(v___y_219_);
v___x_231_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_215_, v_motives_216_, v___x_230_, v_tail_217_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v___x_231_);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_233_);
v___x_235_ = lean_array_push(v___x_234_, v_arg_x27_218_);
v___x_236_ = l_Lean_Meta_mkLambdaFVars(v___x_235_, v_a_232_, v___x_212_, v___x_213_, v___x_212_, v___x_213_, v___x_227_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec_ref(v___x_235_);
return v___x_236_;
}
else
{
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec_ref(v_arg_x27_218_);
return v___x_231_;
}
}
else
{
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
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
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
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
uint8_t v___x_2331__boxed_251_; uint8_t v___x_2332__boxed_252_; lean_object* v_res_253_; 
v___x_2331__boxed_251_ = lean_unbox(v___x_239_);
v___x_2332__boxed_252_ = lean_unbox(v___x_240_);
v_res_253_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_237_, v_arg__type_238_, v___x_2331__boxed_251_, v___x_2332__boxed_252_, v_prods_241_, v_rlvl_242_, v_motives_243_, v_tail_244_, v_arg_x27_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
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
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
v___x_270_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go(v_rlvl_255_, v_motives_254_, v_prods_256_, v_tail_257_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; lean_object* v___x_276_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_mk_empty_array_with_capacity(v___x_272_);
v___x_274_ = lean_array_push(v___x_273_, v_head_258_);
v___x_275_ = 1;
v___x_276_ = l_Lean_Meta_mkLambdaFVars(v___x_274_, v_a_271_, v___x_268_, v___x_269_, v___x_268_, v___x_269_, v___x_275_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v___x_274_);
return v___x_276_;
}
else
{
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec_ref(v_head_258_);
return v___x_270_;
}
}
else
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = l_Lean_Expr_fvarId_x21(v_head_258_);
lean_dec_ref(v_head_258_);
lean_inc_ref(v___y_262_);
v___x_278_ = l_Lean_FVarId_getUserName___redArg(v___x_277_, v___y_262_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_280_; lean_object* v___f_281_; uint8_t v___x_282_; lean_object* v___x_283_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_a_279_);
lean_dec_ref(v___x_278_);
v___x_280_ = lean_box(v___x_269_);
lean_inc(v_rlvl_255_);
v___f_281_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0___boxed), 9, 2);
lean_closure_set(v___f_281_, 0, v_rlvl_255_);
lean_closure_set(v___f_281_, 1, v___x_280_);
v___x_282_ = 0;
lean_inc(v___y_265_);
lean_inc_ref(v___y_264_);
lean_inc(v___y_263_);
lean_inc_ref(v___y_262_);
v___x_283_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_259_, v___f_281_, v___x_282_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___f_287_; lean_object* v___x_288_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_a_284_);
lean_dec_ref(v___x_283_);
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
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
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
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
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
lean_inc(v_head_321_);
v_tail_322_ = lean_ctor_get(v_a_314_, 1);
lean_inc(v_tail_322_);
lean_dec_ref(v_a_314_);
lean_inc(v_a_318_);
lean_inc_ref(v_a_317_);
lean_inc(v_a_316_);
lean_inc_ref(v_a_315_);
lean_inc(v_head_321_);
v___x_323_ = lean_infer_type(v_head_321_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___f_325_; uint8_t v___x_326_; lean_object* v___x_327_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref(v___x_323_);
lean_inc(v_a_324_);
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
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
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
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(lean_object* v_msg_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___f_435_; lean_object* v___x_5030__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_5030__overap_436_ = lean_panic_fn(v___f_435_, v_msg_429_);
v___x_437_ = lean_apply_5(v___x_5030__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___boxed(lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2(v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(lean_object* v_name_445_, lean_object* v_levelParams_446_, lean_object* v_type_447_, lean_object* v_value_448_, lean_object* v_hints_449_, lean_object* v___y_450_){
_start:
{
lean_object* v___x_452_; uint8_t v___y_454_; uint8_t v___y_461_; lean_object* v_env_464_; uint8_t v___x_465_; 
v___x_452_ = lean_st_ref_get(v___y_450_);
v_env_464_ = lean_ctor_get(v___x_452_, 0);
lean_inc_ref(v_env_464_);
lean_dec(v___x_452_);
lean_inc_ref(v_env_464_);
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
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
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
lean_dec_ref(v___x_511_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
lean_inc_ref(v___x_498_);
lean_inc(v___x_497_);
v___x_513_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise(v___x_497_, v___x_498_, v_a_512_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; lean_object* v___x_515_; size_t v___x_516_; size_t v___x_517_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref(v___x_513_);
v___x_515_ = l_Lean_Expr_app___override(v_b_502_, v_a_514_);
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_501_, v___x_516_);
v_i_501_ = v___x_517_;
v_b_502_ = v___x_515_;
goto _start;
}
else
{
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec_ref(v_b_502_);
lean_dec_ref(v___x_498_);
lean_dec(v___x_497_);
return v___x_513_;
}
}
else
{
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
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
uint8_t v___x_9223__boxed_555_; lean_object* v_res_556_; 
v___x_9223__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9223__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
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
lean_dec_ref(v___x_570_);
v___x_572_ = lean_box(v___x_567_);
lean_inc(v___x_557_);
v___f_573_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0___boxed), 9, 2);
lean_closure_set(v___f_573_, 0, v___x_557_);
lean_closure_set(v___f_573_, 1, v___x_572_);
v___x_574_ = 0;
lean_inc(v___y_565_);
lean_inc_ref(v___y_564_);
lean_inc(v___y_563_);
lean_inc_ref(v___y_562_);
v___x_575_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_571_, v___f_573_, v___x_574_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_577_; size_t v___x_578_; size_t v___x_579_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_576_);
lean_dec_ref(v___x_575_);
v___x_577_ = l_Lean_Expr_app___override(v_b_561_, v_a_576_);
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_560_, v___x_578_);
v_i_560_ = v___x_579_;
v_b_561_ = v___x_577_;
goto _start;
}
else
{
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_b_561_);
lean_dec(v___x_557_);
return v___x_575_;
}
}
else
{
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
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
lean_dec_ref(v___x_682_);
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
lean_dec_ref(v___x_684_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
v___x_686_ = l_Lean_Meta_typeFormerTypeLevel(v_a_685_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref(v___x_686_);
if (lean_obj_tag(v_a_687_) == 1)
{
lean_object* v_val_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; size_t v_sz_697_; size_t v___x_698_; lean_object* v___x_699_; 
v_val_688_ = lean_ctor_get(v_a_687_, 0);
lean_inc(v_val_688_);
lean_dec_ref(v_a_687_);
lean_inc(v___x_670_);
lean_inc_ref(v_refArgs_663_);
v___x_689_ = l_Array_toSubarray___redArg(v_refArgs_663_, v_nParams_655_, v___x_670_);
v___x_690_ = l_Subarray_copy___redArg(v___x_677_);
v___x_691_ = l_Subarray_copy___redArg(v___x_689_);
v___x_692_ = l_Lean_mkLevelMax(v_val_688_, v_head_658_);
lean_inc(v___x_692_);
v___x_693_ = l_Lean_Level_succ___override(v___x_692_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_tail_659_);
v___x_695_ = l_Lean_Expr_const___override(v_recName_660_, v___x_694_);
v___x_696_ = l_Lean_mkAppN(v___x_695_, v___x_690_);
v_sz_697_ = lean_array_size(v___x_691_);
v___x_698_ = ((size_t)0ULL);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___x_692_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3(v___x_692_, v___x_691_, v_sz_697_, v___x_698_, v___x_696_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; size_t v_sz_703_; lean_object* v___x_704_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
lean_inc(v___x_671_);
lean_inc_ref(v_refArgs_663_);
v___x_701_ = l_Array_toSubarray___redArg(v_refArgs_663_, v___x_670_, v___x_671_);
v___x_702_ = l_Subarray_copy___redArg(v___x_701_);
v_sz_703_ = lean_array_size(v___x_702_);
lean_inc(v___y_668_);
lean_inc_ref(v___y_667_);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc_ref(v___x_691_);
lean_inc(v___x_692_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__4(v___x_692_, v___x_691_, v___x_702_, v_sz_703_, v___x_698_, v_a_700_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec_ref(v___x_702_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; uint8_t v___x_716_; uint8_t v___x_717_; lean_object* v___x_718_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
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
lean_dec_ref(v___x_718_);
v___x_720_ = l_Lean_Meta_mkLambdaFVars(v___x_714_, v___x_709_, v___x_716_, v___x_673_, v___x_716_, v___x_673_, v___x_717_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
lean_dec_ref(v___x_714_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___x_720_);
v___x_722_ = lean_box(1);
v___x_723_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_belowName_661_, v_levelParams_662_, v_a_719_, v_a_721_, v___x_722_, v___y_668_);
lean_dec(v___y_668_);
return v___x_723_;
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v_a_719_);
lean_dec(v___y_668_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
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
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
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
lean_object* v_fileName_896_; lean_object* v_fileMap_897_; lean_object* v_options_898_; lean_object* v_currRecDepth_899_; lean_object* v_maxRecDepth_900_; lean_object* v_ref_901_; lean_object* v_currNamespace_902_; lean_object* v_openDecls_903_; lean_object* v_initHeartbeats_904_; lean_object* v_maxHeartbeats_905_; lean_object* v_quotContext_906_; lean_object* v_currMacroScope_907_; uint8_t v_diag_908_; lean_object* v_cancelTk_x3f_909_; uint8_t v_suppressElabErrors_910_; lean_object* v_inheritedTraceOptions_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_920_; 
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
v_isSharedCheck_920_ = !lean_is_exclusive(v___y_893_);
if (v_isSharedCheck_920_ == 0)
{
v___x_913_ = v___y_893_;
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_inheritedTraceOptions_911_);
lean_inc(v_cancelTk_x3f_909_);
lean_inc(v_currMacroScope_907_);
lean_inc(v_quotContext_906_);
lean_inc(v_maxHeartbeats_905_);
lean_inc(v_initHeartbeats_904_);
lean_inc(v_openDecls_903_);
lean_inc(v_currNamespace_902_);
lean_inc(v_ref_901_);
lean_inc(v_maxRecDepth_900_);
lean_inc(v_currRecDepth_899_);
lean_inc(v_options_898_);
lean_inc(v_fileMap_897_);
lean_inc(v_fileName_896_);
lean_dec(v___y_893_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_920_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v_ref_915_; lean_object* v___x_917_; 
v_ref_915_ = l_Lean_replaceRef(v_ref_889_, v_ref_901_);
lean_dec(v_ref_901_);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 5, v_ref_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_fileName_896_);
lean_ctor_set(v_reuseFailAlloc_919_, 1, v_fileMap_897_);
lean_ctor_set(v_reuseFailAlloc_919_, 2, v_options_898_);
lean_ctor_set(v_reuseFailAlloc_919_, 3, v_currRecDepth_899_);
lean_ctor_set(v_reuseFailAlloc_919_, 4, v_maxRecDepth_900_);
lean_ctor_set(v_reuseFailAlloc_919_, 5, v_ref_915_);
lean_ctor_set(v_reuseFailAlloc_919_, 6, v_currNamespace_902_);
lean_ctor_set(v_reuseFailAlloc_919_, 7, v_openDecls_903_);
lean_ctor_set(v_reuseFailAlloc_919_, 8, v_initHeartbeats_904_);
lean_ctor_set(v_reuseFailAlloc_919_, 9, v_maxHeartbeats_905_);
lean_ctor_set(v_reuseFailAlloc_919_, 10, v_quotContext_906_);
lean_ctor_set(v_reuseFailAlloc_919_, 11, v_currMacroScope_907_);
lean_ctor_set(v_reuseFailAlloc_919_, 12, v_cancelTk_x3f_909_);
lean_ctor_set(v_reuseFailAlloc_919_, 13, v_inheritedTraceOptions_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*14, v_diag_908_);
lean_ctor_set_uint8(v_reuseFailAlloc_919_, sizeof(void*)*14 + 1, v_suppressElabErrors_910_);
v___x_917_ = v_reuseFailAlloc_919_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_890_, v___y_891_, v___y_892_, v___x_917_, v___y_894_);
lean_dec_ref(v___x_917_);
return v___x_918_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_921_, lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_921_, v_msg_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
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
v___x_934_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
lean_ctor_set(v___x_934_, 2, v___x_933_);
lean_ctor_set(v___x_934_, 3, v___x_932_);
lean_ctor_set(v___x_934_, 4, v___x_932_);
lean_ctor_set(v___x_934_, 5, v___x_932_);
lean_ctor_set(v___x_934_, 6, v___x_932_);
lean_ctor_set(v___x_934_, 7, v___x_932_);
lean_ctor_set(v___x_934_, 8, v___x_932_);
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
lean_inc(v_ref_1117_);
v___x_1118_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1117_, v_constName_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
lean_dec(v_ref_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
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
lean_dec_ref(v___y_1129_);
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
lean_inc_ref(v_a_1166_);
lean_inc(v_recName_1161_);
v___x_1169_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1161_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1169_) == 0)
{
lean_object* v_a_1170_; 
v_a_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_a_1170_);
lean_dec_ref(v___x_1169_);
if (lean_obj_tag(v_a_1170_) == 7)
{
lean_object* v_val_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1286_; 
v_val_1171_ = lean_ctor_get(v_a_1170_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_a_1170_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1173_ = v_a_1170_;
v_isShared_1174_ = v_isSharedCheck_1286_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_val_1171_);
lean_dec(v_a_1170_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1286_;
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
lean_inc(v_levelParams_1178_);
v_type_1179_ = lean_ctor_get(v_toConstantVal_1175_, 2);
lean_inc_ref(v_type_1179_);
lean_dec_ref(v_toConstantVal_1175_);
v___x_1180_ = lean_box(0);
lean_inc(v_levelParams_1178_);
v___x_1181_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1178_, v___x_1180_);
if (lean_obj_tag(v___x_1181_) == 1)
{
lean_object* v_head_1182_; lean_object* v_tail_1183_; lean_object* v___f_1184_; uint8_t v___x_1185_; lean_object* v___x_1186_; 
v_head_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_head_1182_);
v_tail_1183_ = lean_ctor_get(v___x_1181_, 1);
lean_inc(v_tail_1183_);
lean_dec_ref(v___x_1181_);
v___f_1184_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1184_, 0, v_nParams_1162_);
lean_closure_set(v___f_1184_, 1, v_numMotives_1176_);
lean_closure_set(v___f_1184_, 2, v_numMinors_1177_);
lean_closure_set(v___f_1184_, 3, v_head_1182_);
lean_closure_set(v___f_1184_, 4, v_tail_1183_);
lean_closure_set(v___f_1184_, 5, v_recName_1161_);
lean_closure_set(v___f_1184_, 6, v_belowName_1163_);
lean_closure_set(v___f_1184_, 7, v_levelParams_1178_);
v___x_1185_ = 0;
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
lean_inc(v_a_1165_);
lean_inc_ref(v_a_1164_);
v___x_1186_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1179_, v___f_1184_, v___x_1185_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v___x_1189_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___x_1186_);
lean_inc(v_a_1187_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 1);
lean_ctor_set(v___x_1173_, 0, v_a_1187_);
v___x_1189_ = v___x_1173_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1187_);
v___x_1189_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; 
lean_inc(v_a_1167_);
lean_inc_ref(v_a_1166_);
v___x_1190_ = l_Lean_addDecl(v___x_1189_, v___x_1185_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_toConstantVal_1191_; lean_object* v_name_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___x_1190_);
v_toConstantVal_1191_ = lean_ctor_get(v_a_1187_, 0);
lean_inc_ref(v_toConstantVal_1191_);
lean_dec(v_a_1187_);
v_name_1192_ = lean_ctor_get(v_toConstantVal_1191_, 0);
lean_inc(v_name_1192_);
lean_dec_ref(v_toConstantVal_1191_);
lean_inc(v_name_1192_);
v___x_1193_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1192_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec_ref(v_a_1164_);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1269_ == 0)
{
lean_object* v_unused_1270_; 
v_unused_1270_ = lean_ctor_get(v___x_1193_, 0);
lean_dec(v_unused_1270_);
v___x_1195_ = v___x_1193_;
v_isShared_1196_ = v_isSharedCheck_1269_;
goto v_resetjp_1194_;
}
else
{
lean_dec(v___x_1193_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1269_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1197_; lean_object* v_env_1198_; lean_object* v_nextMacroScope_1199_; lean_object* v_ngen_1200_; lean_object* v_auxDeclNGen_1201_; lean_object* v_traceState_1202_; lean_object* v_messages_1203_; lean_object* v_infoState_1204_; lean_object* v_snapshotTasks_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1267_; 
v___x_1197_ = lean_st_ref_take(v_a_1167_);
v_env_1198_ = lean_ctor_get(v___x_1197_, 0);
v_nextMacroScope_1199_ = lean_ctor_get(v___x_1197_, 1);
v_ngen_1200_ = lean_ctor_get(v___x_1197_, 2);
v_auxDeclNGen_1201_ = lean_ctor_get(v___x_1197_, 3);
v_traceState_1202_ = lean_ctor_get(v___x_1197_, 4);
v_messages_1203_ = lean_ctor_get(v___x_1197_, 6);
v_infoState_1204_ = lean_ctor_get(v___x_1197_, 7);
v_snapshotTasks_1205_ = lean_ctor_get(v___x_1197_, 8);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1197_, 5);
lean_dec(v_unused_1268_);
v___x_1207_ = v___x_1197_;
v_isShared_1208_ = v_isSharedCheck_1267_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_snapshotTasks_1205_);
lean_inc(v_infoState_1204_);
lean_inc(v_messages_1203_);
lean_inc(v_traceState_1202_);
lean_inc(v_auxDeclNGen_1201_);
lean_inc(v_ngen_1200_);
lean_inc(v_nextMacroScope_1199_);
lean_inc(v_env_1198_);
lean_dec(v___x_1197_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1267_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_inc(v_name_1192_);
v___x_1209_ = l_Lean_markAuxRecursor(v_env_1198_, v_name_1192_);
v___x_1210_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 5, v___x_1210_);
lean_ctor_set(v___x_1207_, 0, v___x_1209_);
v___x_1212_ = v___x_1207_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_nextMacroScope_1199_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_ngen_1200_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v_auxDeclNGen_1201_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v_traceState_1202_);
lean_ctor_set(v_reuseFailAlloc_1266_, 5, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1266_, 6, v_messages_1203_);
lean_ctor_set(v_reuseFailAlloc_1266_, 7, v_infoState_1204_);
lean_ctor_set(v_reuseFailAlloc_1266_, 8, v_snapshotTasks_1205_);
v___x_1212_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v_mctx_1215_; lean_object* v_zetaDeltaFVarIds_1216_; lean_object* v_postponed_1217_; lean_object* v_diag_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1264_; 
v___x_1213_ = lean_st_ref_set(v_a_1167_, v___x_1212_);
v___x_1214_ = lean_st_ref_take(v_a_1165_);
v_mctx_1215_ = lean_ctor_get(v___x_1214_, 0);
v_zetaDeltaFVarIds_1216_ = lean_ctor_get(v___x_1214_, 2);
v_postponed_1217_ = lean_ctor_get(v___x_1214_, 3);
v_diag_1218_ = lean_ctor_get(v___x_1214_, 4);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1214_, 1);
lean_dec(v_unused_1265_);
v___x_1220_ = v___x_1214_;
v_isShared_1221_ = v_isSharedCheck_1264_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_diag_1218_);
lean_inc(v_postponed_1217_);
lean_inc(v_zetaDeltaFVarIds_1216_);
lean_inc(v_mctx_1215_);
lean_dec(v___x_1214_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1264_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; 
v___x_1222_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 1, v___x_1222_);
v___x_1224_ = v___x_1220_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_mctx_1215_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_zetaDeltaFVarIds_1216_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_postponed_1217_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_diag_1218_);
v___x_1224_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v_env_1227_; lean_object* v_nextMacroScope_1228_; lean_object* v_ngen_1229_; lean_object* v_auxDeclNGen_1230_; lean_object* v_traceState_1231_; lean_object* v_messages_1232_; lean_object* v_infoState_1233_; lean_object* v_snapshotTasks_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1261_; 
v___x_1225_ = lean_st_ref_set(v_a_1165_, v___x_1224_);
v___x_1226_ = lean_st_ref_take(v_a_1167_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
v_nextMacroScope_1228_ = lean_ctor_get(v___x_1226_, 1);
v_ngen_1229_ = lean_ctor_get(v___x_1226_, 2);
v_auxDeclNGen_1230_ = lean_ctor_get(v___x_1226_, 3);
v_traceState_1231_ = lean_ctor_get(v___x_1226_, 4);
v_messages_1232_ = lean_ctor_get(v___x_1226_, 6);
v_infoState_1233_ = lean_ctor_get(v___x_1226_, 7);
v_snapshotTasks_1234_ = lean_ctor_get(v___x_1226_, 8);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1226_, 5);
lean_dec(v_unused_1262_);
v___x_1236_ = v___x_1226_;
v_isShared_1237_ = v_isSharedCheck_1261_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snapshotTasks_1234_);
lean_inc(v_infoState_1233_);
lean_inc(v_messages_1232_);
lean_inc(v_traceState_1231_);
lean_inc(v_auxDeclNGen_1230_);
lean_inc(v_ngen_1229_);
lean_inc(v_nextMacroScope_1228_);
lean_inc(v_env_1227_);
lean_dec(v___x_1226_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1261_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_addProtected(v_env_1227_, v_name_1192_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 5, v___x_1210_);
lean_ctor_set(v___x_1236_, 0, v___x_1238_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1238_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_nextMacroScope_1228_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_ngen_1229_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_auxDeclNGen_1230_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_traceState_1231_);
lean_ctor_set(v_reuseFailAlloc_1260_, 5, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1260_, 6, v_messages_1232_);
lean_ctor_set(v_reuseFailAlloc_1260_, 7, v_infoState_1233_);
lean_ctor_set(v_reuseFailAlloc_1260_, 8, v_snapshotTasks_1234_);
v___x_1240_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v_mctx_1243_; lean_object* v_zetaDeltaFVarIds_1244_; lean_object* v_postponed_1245_; lean_object* v_diag_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1258_; 
v___x_1241_ = lean_st_ref_set(v_a_1167_, v___x_1240_);
lean_dec(v_a_1167_);
v___x_1242_ = lean_st_ref_take(v_a_1165_);
v_mctx_1243_ = lean_ctor_get(v___x_1242_, 0);
v_zetaDeltaFVarIds_1244_ = lean_ctor_get(v___x_1242_, 2);
v_postponed_1245_ = lean_ctor_get(v___x_1242_, 3);
v_diag_1246_ = lean_ctor_get(v___x_1242_, 4);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1242_, 1);
lean_dec(v_unused_1259_);
v___x_1248_ = v___x_1242_;
v_isShared_1249_ = v_isSharedCheck_1258_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_diag_1246_);
lean_inc(v_postponed_1245_);
lean_inc(v_zetaDeltaFVarIds_1244_);
lean_inc(v_mctx_1243_);
lean_dec(v___x_1242_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1258_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v___x_1222_);
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_mctx_1243_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_zetaDeltaFVarIds_1244_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_postponed_1245_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_diag_1246_);
v___x_1251_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1252_ = lean_st_ref_set(v_a_1165_, v___x_1251_);
lean_dec(v_a_1165_);
v___x_1253_ = lean_box(0);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1253_);
v___x_1255_ = v___x_1195_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
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
lean_dec(v_a_1187_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_del_object(v___x_1173_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
v_a_1272_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1186_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1186_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v___x_1181_);
lean_dec_ref(v_type_1179_);
lean_dec(v_levelParams_1178_);
lean_dec(v_numMinors_1177_);
lean_dec(v_numMotives_1176_);
lean_del_object(v___x_1173_);
lean_dec(v_belowName_1163_);
lean_dec(v_nParams_1162_);
v___x_1280_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1281_ = l_Lean_MessageData_ofName(v_recName_1161_);
v___x_1282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1280_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1282_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1284_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v___x_1285_;
}
}
}
else
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_dec(v_a_1170_);
lean_dec(v_belowName_1163_);
lean_dec(v_nParams_1162_);
v___x_1287_ = l_Lean_MessageData_ofName(v_recName_1161_);
v___x_1288_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1287_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1289_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
return v___x_1290_;
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_belowName_1163_);
lean_dec(v_nParams_1162_);
lean_dec(v_recName_1161_);
v_a_1291_ = lean_ctor_get(v___x_1169_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1169_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1169_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1169_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___boxed(lean_object* v_recName_1299_, lean_object* v_nParams_1300_, lean_object* v_belowName_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v_recName_1299_, v_nParams_1300_, v_belowName_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(lean_object* v_00_u03b1_1308_, lean_object* v_msg_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___boxed(lean_object* v_00_u03b1_1316_, lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6(v_00_u03b1_1316_, v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(lean_object* v_declName_1324_, uint8_t v_s_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_1324_, v_s_1325_, v___y_1327_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___boxed(lean_object* v_declName_1332_, lean_object* v_s_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
uint8_t v_s_boxed_1339_; lean_object* v_res_1340_; 
v_s_boxed_1339_ = lean_unbox(v_s_1333_);
v_res_1340_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9(v_declName_1332_, v_s_boxed_1339_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(lean_object* v_00_u03b1_1341_, lean_object* v_constName_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1349_, lean_object* v_constName_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0(v_00_u03b1_1349_, v_constName_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_);
lean_dec(v___y_1354_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_1357_, lean_object* v_ref_1358_, lean_object* v_constName_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1358_, v_constName_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_ref_1367_, lean_object* v_constName_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3(v_00_u03b1_1366_, v_ref_1367_, v_constName_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec(v___y_1370_);
lean_dec_ref(v___y_1369_);
lean_dec(v_ref_1367_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(lean_object* v_00_u03b1_1375_, lean_object* v_ref_1376_, lean_object* v_msg_1377_, lean_object* v_declHint_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1376_, v_msg_1377_, v_declHint_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___boxed(lean_object* v_00_u03b1_1385_, lean_object* v_ref_1386_, lean_object* v_msg_1387_, lean_object* v_declHint_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11(v_00_u03b1_1385_, v_ref_1386_, v_msg_1387_, v_declHint_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
lean_dec(v___y_1392_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v_ref_1386_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(lean_object* v_msg_1395_, lean_object* v_declHint_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1395_, v_declHint_1396_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___boxed(lean_object* v_msg_1403_, lean_object* v_declHint_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13(v_msg_1403_, v_declHint_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(lean_object* v_00_u03b1_1411_, lean_object* v_ref_1412_, lean_object* v_msg_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1412_, v_msg_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___boxed(lean_object* v_00_u03b1_1420_, lean_object* v_ref_1421_, lean_object* v_msg_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13(v_00_u03b1_1420_, v_ref_1421_, v_msg_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v_ref_1421_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(lean_object* v_cls_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_options_1435_; uint8_t v_hasTrace_1436_; 
v_options_1435_ = lean_ctor_get(v___y_1433_, 2);
v_hasTrace_1436_ = lean_ctor_get_uint8(v_options_1435_, sizeof(void*)*1);
if (v_hasTrace_1436_ == 0)
{
lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec(v_cls_1432_);
v___x_1437_ = lean_box(v_hasTrace_1436_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
else
{
lean_object* v_inheritedTraceOptions_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_inheritedTraceOptions_1439_ = lean_ctor_get(v___y_1433_, 13);
v___x_1440_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__1));
v___x_1441_ = l_Lean_Name_append(v___x_1440_, v_cls_1432_);
v___x_1442_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1439_, v_options_1435_, v___x_1441_);
lean_dec(v___x_1441_);
v___x_1443_ = lean_box(v___x_1442_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v_cls_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v_cls_1445_, v___y_1446_);
lean_dec_ref(v___y_1446_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1(lean_object* v_cls_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v_cls_1449_, v___y_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___boxed(lean_object* v_cls_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1(v_cls_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
return v_res_1462_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1463_ = lean_unsigned_to_nat(32u);
v___x_1464_ = lean_mk_empty_array_with_capacity(v___x_1463_);
v___x_1465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
return v___x_1465_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = ((size_t)5ULL);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_unsigned_to_nat(32u);
v___x_1469_ = lean_mk_empty_array_with_capacity(v___x_1468_);
v___x_1470_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0);
v___x_1471_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1469_);
lean_ctor_set(v___x_1471_, 2, v___x_1467_);
lean_ctor_set(v___x_1471_, 3, v___x_1467_);
lean_ctor_set_usize(v___x_1471_, 4, v___x_1466_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v_traceState_1475_; lean_object* v_traces_1476_; lean_object* v___x_1477_; lean_object* v_traceState_1478_; lean_object* v_env_1479_; lean_object* v_nextMacroScope_1480_; lean_object* v_ngen_1481_; lean_object* v_auxDeclNGen_1482_; lean_object* v_cache_1483_; lean_object* v_messages_1484_; lean_object* v_infoState_1485_; lean_object* v_snapshotTasks_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1505_; 
v___x_1474_ = lean_st_ref_get(v___y_1472_);
v_traceState_1475_ = lean_ctor_get(v___x_1474_, 4);
lean_inc_ref(v_traceState_1475_);
lean_dec(v___x_1474_);
v_traces_1476_ = lean_ctor_get(v_traceState_1475_, 0);
lean_inc_ref(v_traces_1476_);
lean_dec_ref(v_traceState_1475_);
v___x_1477_ = lean_st_ref_take(v___y_1472_);
v_traceState_1478_ = lean_ctor_get(v___x_1477_, 4);
v_env_1479_ = lean_ctor_get(v___x_1477_, 0);
v_nextMacroScope_1480_ = lean_ctor_get(v___x_1477_, 1);
v_ngen_1481_ = lean_ctor_get(v___x_1477_, 2);
v_auxDeclNGen_1482_ = lean_ctor_get(v___x_1477_, 3);
v_cache_1483_ = lean_ctor_get(v___x_1477_, 5);
v_messages_1484_ = lean_ctor_get(v___x_1477_, 6);
v_infoState_1485_ = lean_ctor_get(v___x_1477_, 7);
v_snapshotTasks_1486_ = lean_ctor_get(v___x_1477_, 8);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1488_ = v___x_1477_;
v_isShared_1489_ = v_isSharedCheck_1505_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_snapshotTasks_1486_);
lean_inc(v_infoState_1485_);
lean_inc(v_messages_1484_);
lean_inc(v_cache_1483_);
lean_inc(v_traceState_1478_);
lean_inc(v_auxDeclNGen_1482_);
lean_inc(v_ngen_1481_);
lean_inc(v_nextMacroScope_1480_);
lean_inc(v_env_1479_);
lean_dec(v___x_1477_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1505_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
uint64_t v_tid_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1503_; 
v_tid_1490_ = lean_ctor_get_uint64(v_traceState_1478_, sizeof(void*)*1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_traceState_1478_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v_traceState_1478_, 0);
lean_dec(v_unused_1504_);
v___x_1492_ = v_traceState_1478_;
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v_traceState_1478_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1503_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1496_; 
v___x_1494_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1494_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1494_);
lean_ctor_set_uint64(v_reuseFailAlloc_1502_, sizeof(void*)*1, v_tid_1490_);
v___x_1496_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 4, v___x_1496_);
v___x_1498_ = v___x_1488_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_env_1479_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_nextMacroScope_1480_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_ngen_1481_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_auxDeclNGen_1482_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1501_, 5, v_cache_1483_);
lean_ctor_set(v_reuseFailAlloc_1501_, 6, v_messages_1484_);
lean_ctor_set(v_reuseFailAlloc_1501_, 7, v_infoState_1485_);
lean_ctor_set(v_reuseFailAlloc_1501_, 8, v_snapshotTasks_1486_);
v___x_1498_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_st_ref_set(v___y_1472_, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1500_, 0, v_traces_1476_);
return v___x_1500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___boxed(lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v___y_1506_);
lean_dec(v___y_1506_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2(lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v___y_1512_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___boxed(lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2(v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
return v_res_1520_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__3(lean_object* v_opts_1521_, lean_object* v_opt_1522_){
_start:
{
lean_object* v_name_1523_; lean_object* v_defValue_1524_; lean_object* v_map_1525_; lean_object* v___x_1526_; 
v_name_1523_ = lean_ctor_get(v_opt_1522_, 0);
v_defValue_1524_ = lean_ctor_get(v_opt_1522_, 1);
v_map_1525_ = lean_ctor_get(v_opts_1521_, 0);
v___x_1526_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1525_, v_name_1523_);
if (lean_obj_tag(v___x_1526_) == 0)
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_unbox(v_defValue_1524_);
return v___x_1527_;
}
else
{
lean_object* v_val_1528_; 
v_val_1528_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_val_1528_);
lean_dec_ref(v___x_1526_);
if (lean_obj_tag(v_val_1528_) == 1)
{
uint8_t v_v_1529_; 
v_v_1529_ = lean_ctor_get_uint8(v_val_1528_, 0);
lean_dec_ref(v_val_1528_);
return v_v_1529_;
}
else
{
uint8_t v___x_1530_; 
lean_dec(v_val_1528_);
v___x_1530_ = lean_unbox(v_defValue_1524_);
return v___x_1530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_opts_1531_, lean_object* v_opt_1532_){
_start:
{
uint8_t v_res_1533_; lean_object* v_r_1534_; 
v_res_1533_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_opts_1531_, v_opt_1532_);
lean_dec_ref(v_opt_1532_);
lean_dec_ref(v_opts_1531_);
v_r_1534_ = lean_box(v_res_1533_);
return v_r_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1535_, lean_object* v_x_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_MessageData_ofName(v_indName_1535_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1544_, lean_object* v_x_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_mkBelow___lam__0(v_indName_1544_, v_x_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec_ref(v_x_1545_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1552_, lean_object* v___x_1553_, lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v_a_1556_, lean_object* v_b_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
uint8_t v___x_1563_; 
v___x_1563_ = lean_nat_dec_lt(v_a_1556_, v_upperBound_1552_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v_a_1556_);
lean_dec(v___x_1555_);
lean_dec(v___x_1554_);
lean_dec(v___x_1553_);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v_b_1557_);
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_a_1556_, v___x_1565_);
lean_dec(v_a_1556_);
lean_inc(v___x_1566_);
lean_inc(v___x_1553_);
v___x_1567_ = lean_name_append_index_after(v___x_1553_, v___x_1566_);
lean_inc(v___x_1566_);
lean_inc(v___x_1554_);
v___x_1568_ = lean_name_append_index_after(v___x_1554_, v___x_1566_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
lean_inc(v___y_1559_);
lean_inc_ref(v___y_1558_);
lean_inc(v___x_1555_);
v___x_1569_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1567_, v___x_1555_, v___x_1568_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
if (lean_obj_tag(v___x_1569_) == 0)
{
lean_object* v___x_1570_; 
lean_dec_ref(v___x_1569_);
v___x_1570_ = lean_box(0);
v_a_1556_ = v___x_1566_;
v_b_1557_ = v___x_1570_;
goto _start;
}
else
{
lean_dec(v___x_1566_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___x_1555_);
lean_dec(v___x_1554_);
lean_dec(v___x_1553_);
return v___x_1569_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1572_, lean_object* v___x_1573_, lean_object* v___x_1574_, lean_object* v___x_1575_, lean_object* v_a_1576_, lean_object* v_b_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1572_, v___x_1573_, v___x_1574_, v___x_1575_, v_a_1576_, v_b_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v_upperBound_1572_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(lean_object* v_x_1584_){
_start:
{
if (lean_obj_tag(v_x_1584_) == 0)
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
v_a_1586_ = lean_ctor_get(v_x_1584_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v_x_1584_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v_x_1584_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 1);
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
else
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v_x_1584_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1584_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v_x_1584_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v_x_1584_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 0);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg___boxed(lean_object* v_x_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_x_1602_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(lean_object* v_opts_1605_, lean_object* v_opt_1606_){
_start:
{
lean_object* v_name_1607_; lean_object* v_defValue_1608_; lean_object* v_map_1609_; lean_object* v___x_1610_; 
v_name_1607_ = lean_ctor_get(v_opt_1606_, 0);
v_defValue_1608_ = lean_ctor_get(v_opt_1606_, 1);
v_map_1609_ = lean_ctor_get(v_opts_1605_, 0);
v___x_1610_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1609_, v_name_1607_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_inc(v_defValue_1608_);
return v_defValue_1608_;
}
else
{
lean_object* v_val_1611_; 
v_val_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_val_1611_);
lean_dec_ref(v___x_1610_);
if (lean_obj_tag(v_val_1611_) == 3)
{
lean_object* v_v_1612_; 
v_v_1612_ = lean_ctor_get(v_val_1611_, 0);
lean_inc(v_v_1612_);
lean_dec_ref(v_val_1611_);
return v_v_1612_;
}
else
{
lean_dec(v_val_1611_);
lean_inc(v_defValue_1608_);
return v_defValue_1608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7___boxed(lean_object* v_opts_1613_, lean_object* v_opt_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(v_opts_1613_, v_opt_1614_);
lean_dec_ref(v_opt_1614_);
lean_dec_ref(v_opts_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4(lean_object* v_e_1616_){
_start:
{
if (lean_obj_tag(v_e_1616_) == 0)
{
uint8_t v___x_1617_; 
v___x_1617_ = 2;
return v___x_1617_;
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = 0;
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4___boxed(lean_object* v_e_1619_){
_start:
{
uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4(v_e_1619_);
lean_dec_ref(v_e_1619_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6(size_t v_sz_1622_, size_t v_i_1623_, lean_object* v_bs_1624_){
_start:
{
uint8_t v___x_1625_; 
v___x_1625_ = lean_usize_dec_lt(v_i_1623_, v_sz_1622_);
if (v___x_1625_ == 0)
{
return v_bs_1624_;
}
else
{
lean_object* v_v_1626_; lean_object* v_msg_1627_; lean_object* v___x_1628_; lean_object* v_bs_x27_1629_; size_t v___x_1630_; size_t v___x_1631_; lean_object* v___x_1632_; 
v_v_1626_ = lean_array_uget_borrowed(v_bs_1624_, v_i_1623_);
v_msg_1627_ = lean_ctor_get(v_v_1626_, 1);
lean_inc_ref(v_msg_1627_);
v___x_1628_ = lean_unsigned_to_nat(0u);
v_bs_x27_1629_ = lean_array_uset(v_bs_1624_, v_i_1623_, v___x_1628_);
v___x_1630_ = ((size_t)1ULL);
v___x_1631_ = lean_usize_add(v_i_1623_, v___x_1630_);
v___x_1632_ = lean_array_uset(v_bs_x27_1629_, v_i_1623_, v_msg_1627_);
v_i_1623_ = v___x_1631_;
v_bs_1624_ = v___x_1632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_1634_, lean_object* v_i_1635_, lean_object* v_bs_1636_){
_start:
{
size_t v_sz_boxed_1637_; size_t v_i_boxed_1638_; lean_object* v_res_1639_; 
v_sz_boxed_1637_ = lean_unbox_usize(v_sz_1634_);
lean_dec(v_sz_1634_);
v_i_boxed_1638_ = lean_unbox_usize(v_i_1635_);
lean_dec(v_i_1635_);
v_res_1639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6(v_sz_boxed_1637_, v_i_boxed_1638_, v_bs_1636_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5(lean_object* v_oldTraces_1640_, lean_object* v_data_1641_, lean_object* v_ref_1642_, lean_object* v_msg_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_fileName_1649_; lean_object* v_fileMap_1650_; lean_object* v_options_1651_; lean_object* v_currRecDepth_1652_; lean_object* v_maxRecDepth_1653_; lean_object* v_ref_1654_; lean_object* v_currNamespace_1655_; lean_object* v_openDecls_1656_; lean_object* v_initHeartbeats_1657_; lean_object* v_maxHeartbeats_1658_; lean_object* v_quotContext_1659_; lean_object* v_currMacroScope_1660_; uint8_t v_diag_1661_; lean_object* v_cancelTk_x3f_1662_; uint8_t v_suppressElabErrors_1663_; lean_object* v_inheritedTraceOptions_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1719_; 
v_fileName_1649_ = lean_ctor_get(v___y_1646_, 0);
v_fileMap_1650_ = lean_ctor_get(v___y_1646_, 1);
v_options_1651_ = lean_ctor_get(v___y_1646_, 2);
v_currRecDepth_1652_ = lean_ctor_get(v___y_1646_, 3);
v_maxRecDepth_1653_ = lean_ctor_get(v___y_1646_, 4);
v_ref_1654_ = lean_ctor_get(v___y_1646_, 5);
v_currNamespace_1655_ = lean_ctor_get(v___y_1646_, 6);
v_openDecls_1656_ = lean_ctor_get(v___y_1646_, 7);
v_initHeartbeats_1657_ = lean_ctor_get(v___y_1646_, 8);
v_maxHeartbeats_1658_ = lean_ctor_get(v___y_1646_, 9);
v_quotContext_1659_ = lean_ctor_get(v___y_1646_, 10);
v_currMacroScope_1660_ = lean_ctor_get(v___y_1646_, 11);
v_diag_1661_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*14);
v_cancelTk_x3f_1662_ = lean_ctor_get(v___y_1646_, 12);
v_suppressElabErrors_1663_ = lean_ctor_get_uint8(v___y_1646_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1664_ = lean_ctor_get(v___y_1646_, 13);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___y_1646_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1666_ = v___y_1646_;
v_isShared_1667_ = v_isSharedCheck_1719_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_inheritedTraceOptions_1664_);
lean_inc(v_cancelTk_x3f_1662_);
lean_inc(v_currMacroScope_1660_);
lean_inc(v_quotContext_1659_);
lean_inc(v_maxHeartbeats_1658_);
lean_inc(v_initHeartbeats_1657_);
lean_inc(v_openDecls_1656_);
lean_inc(v_currNamespace_1655_);
lean_inc(v_ref_1654_);
lean_inc(v_maxRecDepth_1653_);
lean_inc(v_currRecDepth_1652_);
lean_inc(v_options_1651_);
lean_inc(v_fileMap_1650_);
lean_inc(v_fileName_1649_);
lean_dec(v___y_1646_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1719_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v_traceState_1669_; lean_object* v_traces_1670_; lean_object* v_ref_1671_; lean_object* v___x_1673_; 
v___x_1668_ = lean_st_ref_get(v___y_1647_);
v_traceState_1669_ = lean_ctor_get(v___x_1668_, 4);
lean_inc_ref(v_traceState_1669_);
lean_dec(v___x_1668_);
v_traces_1670_ = lean_ctor_get(v_traceState_1669_, 0);
lean_inc_ref(v_traces_1670_);
lean_dec_ref(v_traceState_1669_);
v_ref_1671_ = l_Lean_replaceRef(v_ref_1642_, v_ref_1654_);
lean_dec(v_ref_1654_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 5, v_ref_1671_);
v___x_1673_ = v___x_1666_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_fileName_1649_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v_fileMap_1650_);
lean_ctor_set(v_reuseFailAlloc_1718_, 2, v_options_1651_);
lean_ctor_set(v_reuseFailAlloc_1718_, 3, v_currRecDepth_1652_);
lean_ctor_set(v_reuseFailAlloc_1718_, 4, v_maxRecDepth_1653_);
lean_ctor_set(v_reuseFailAlloc_1718_, 5, v_ref_1671_);
lean_ctor_set(v_reuseFailAlloc_1718_, 6, v_currNamespace_1655_);
lean_ctor_set(v_reuseFailAlloc_1718_, 7, v_openDecls_1656_);
lean_ctor_set(v_reuseFailAlloc_1718_, 8, v_initHeartbeats_1657_);
lean_ctor_set(v_reuseFailAlloc_1718_, 9, v_maxHeartbeats_1658_);
lean_ctor_set(v_reuseFailAlloc_1718_, 10, v_quotContext_1659_);
lean_ctor_set(v_reuseFailAlloc_1718_, 11, v_currMacroScope_1660_);
lean_ctor_set(v_reuseFailAlloc_1718_, 12, v_cancelTk_x3f_1662_);
lean_ctor_set(v_reuseFailAlloc_1718_, 13, v_inheritedTraceOptions_1664_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*14, v_diag_1661_);
lean_ctor_set_uint8(v_reuseFailAlloc_1718_, sizeof(void*)*14 + 1, v_suppressElabErrors_1663_);
v___x_1673_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
lean_object* v___x_1674_; size_t v_sz_1675_; size_t v___x_1676_; lean_object* v___x_1677_; lean_object* v_msg_1678_; lean_object* v___x_1679_; lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1717_; 
v___x_1674_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1670_);
lean_dec_ref(v_traces_1670_);
v_sz_1675_ = lean_array_size(v___x_1674_);
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6(v_sz_1675_, v___x_1676_, v___x_1674_);
v_msg_1678_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1678_, 0, v_data_1641_);
lean_ctor_set(v_msg_1678_, 1, v_msg_1643_);
lean_ctor_set(v_msg_1678_, 2, v___x_1677_);
v___x_1679_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1678_, v___y_1644_, v___y_1645_, v___x_1673_, v___y_1647_);
lean_dec_ref(v___x_1673_);
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1682_ = v___x_1679_;
v_isShared_1683_ = v_isSharedCheck_1717_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1679_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1717_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v_traceState_1685_; lean_object* v_env_1686_; lean_object* v_nextMacroScope_1687_; lean_object* v_ngen_1688_; lean_object* v_auxDeclNGen_1689_; lean_object* v_cache_1690_; lean_object* v_messages_1691_; lean_object* v_infoState_1692_; lean_object* v_snapshotTasks_1693_; lean_object* v___x_1695_; uint8_t v_isShared_1696_; uint8_t v_isSharedCheck_1716_; 
v___x_1684_ = lean_st_ref_take(v___y_1647_);
v_traceState_1685_ = lean_ctor_get(v___x_1684_, 4);
v_env_1686_ = lean_ctor_get(v___x_1684_, 0);
v_nextMacroScope_1687_ = lean_ctor_get(v___x_1684_, 1);
v_ngen_1688_ = lean_ctor_get(v___x_1684_, 2);
v_auxDeclNGen_1689_ = lean_ctor_get(v___x_1684_, 3);
v_cache_1690_ = lean_ctor_get(v___x_1684_, 5);
v_messages_1691_ = lean_ctor_get(v___x_1684_, 6);
v_infoState_1692_ = lean_ctor_get(v___x_1684_, 7);
v_snapshotTasks_1693_ = lean_ctor_get(v___x_1684_, 8);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1695_ = v___x_1684_;
v_isShared_1696_ = v_isSharedCheck_1716_;
goto v_resetjp_1694_;
}
else
{
lean_inc(v_snapshotTasks_1693_);
lean_inc(v_infoState_1692_);
lean_inc(v_messages_1691_);
lean_inc(v_cache_1690_);
lean_inc(v_traceState_1685_);
lean_inc(v_auxDeclNGen_1689_);
lean_inc(v_ngen_1688_);
lean_inc(v_nextMacroScope_1687_);
lean_inc(v_env_1686_);
lean_dec(v___x_1684_);
v___x_1695_ = lean_box(0);
v_isShared_1696_ = v_isSharedCheck_1716_;
goto v_resetjp_1694_;
}
v_resetjp_1694_:
{
uint64_t v_tid_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1714_; 
v_tid_1697_ = lean_ctor_get_uint64(v_traceState_1685_, sizeof(void*)*1);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_traceState_1685_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_traceState_1685_, 0);
lean_dec(v_unused_1715_);
v___x_1699_ = v_traceState_1685_;
v_isShared_1700_ = v_isSharedCheck_1714_;
goto v_resetjp_1698_;
}
else
{
lean_dec(v_traceState_1685_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1714_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_ref_1642_);
lean_ctor_set(v___x_1701_, 1, v_a_1680_);
v___x_1702_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1640_, v___x_1701_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 0, v___x_1702_);
v___x_1704_ = v___x_1699_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1702_);
lean_ctor_set_uint64(v_reuseFailAlloc_1713_, sizeof(void*)*1, v_tid_1697_);
v___x_1704_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1706_; 
if (v_isShared_1696_ == 0)
{
lean_ctor_set(v___x_1695_, 4, v___x_1704_);
v___x_1706_ = v___x_1695_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_env_1686_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v_nextMacroScope_1687_);
lean_ctor_set(v_reuseFailAlloc_1712_, 2, v_ngen_1688_);
lean_ctor_set(v_reuseFailAlloc_1712_, 3, v_auxDeclNGen_1689_);
lean_ctor_set(v_reuseFailAlloc_1712_, 4, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1712_, 5, v_cache_1690_);
lean_ctor_set(v_reuseFailAlloc_1712_, 6, v_messages_1691_);
lean_ctor_set(v_reuseFailAlloc_1712_, 7, v_infoState_1692_);
lean_ctor_set(v_reuseFailAlloc_1712_, 8, v_snapshotTasks_1693_);
v___x_1706_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1707_ = lean_st_ref_set(v___y_1647_, v___x_1706_);
v___x_1708_ = lean_box(0);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 0, v___x_1708_);
v___x_1710_ = v___x_1682_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5___boxed(lean_object* v_oldTraces_1720_, lean_object* v_data_1721_, lean_object* v_ref_1722_, lean_object* v_msg_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v_res_1729_; 
v_res_1729_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5(v_oldTraces_1720_, v_data_1721_, v_ref_1722_, v_msg_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
lean_dec(v___y_1727_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
return v_res_1729_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__0));
v___x_1732_ = l_Lean_stringToMessageData(v___x_1731_);
return v___x_1732_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1733_; double v___x_1734_; 
v___x_1733_ = lean_unsigned_to_nat(0u);
v___x_1734_ = lean_float_of_nat(v___x_1733_);
return v___x_1734_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__3));
v___x_1737_ = l_Lean_stringToMessageData(v___x_1736_);
return v___x_1737_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1738_; double v___x_1739_; 
v___x_1738_ = lean_unsigned_to_nat(1000u);
v___x_1739_ = lean_float_of_nat(v___x_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(lean_object* v_cls_1740_, uint8_t v_collapsed_1741_, lean_object* v_tag_1742_, lean_object* v_opts_1743_, uint8_t v_clsEnabled_1744_, lean_object* v_oldTraces_1745_, lean_object* v_msg_1746_, lean_object* v_resStartStop_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_fst_1753_; lean_object* v_snd_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1844_; 
v_fst_1753_ = lean_ctor_get(v_resStartStop_1747_, 0);
v_snd_1754_ = lean_ctor_get(v_resStartStop_1747_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_resStartStop_1747_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1756_ = v_resStartStop_1747_;
v_isShared_1757_ = v_isSharedCheck_1844_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_snd_1754_);
lean_inc(v_fst_1753_);
lean_dec(v_resStartStop_1747_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1844_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___y_1759_; lean_object* v___y_1760_; lean_object* v_data_1761_; lean_object* v_fst_1764_; lean_object* v_snd_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1843_; 
v_fst_1764_ = lean_ctor_get(v_snd_1754_, 0);
v_snd_1765_ = lean_ctor_get(v_snd_1754_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_snd_1754_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1767_ = v_snd_1754_;
v_isShared_1768_ = v_isSharedCheck_1843_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_snd_1765_);
lean_inc(v_fst_1764_);
lean_dec(v_snd_1754_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1843_;
goto v_resetjp_1766_;
}
v___jp_1758_:
{
lean_object* v___x_1762_; 
v___x_1762_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5(v_oldTraces_1745_, v_data_1761_, v___y_1759_, v___y_1760_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
if (lean_obj_tag(v___x_1762_) == 0)
{
lean_object* v___x_1763_; 
lean_dec_ref(v___x_1762_);
v___x_1763_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_fst_1753_);
return v___x_1763_;
}
else
{
lean_dec(v_fst_1753_);
return v___x_1762_;
}
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; uint8_t v___x_1770_; lean_object* v___y_1772_; lean_object* v_a_1773_; uint8_t v___y_1797_; double v___y_1828_; 
v___x_1769_ = l_Lean_trace_profiler;
v___x_1770_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_opts_1743_, v___x_1769_);
if (v___x_1770_ == 0)
{
v___y_1797_ = v___x_1770_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1834_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_opts_1743_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; double v___x_1837_; double v___x_1838_; double v___x_1839_; 
v___x_1835_ = l_Lean_trace_profiler_threshold;
v___x_1836_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(v_opts_1743_, v___x_1835_);
v___x_1837_ = lean_float_of_nat(v___x_1836_);
v___x_1838_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5);
v___x_1839_ = lean_float_div(v___x_1837_, v___x_1838_);
v___y_1828_ = v___x_1839_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; double v___x_1842_; 
v___x_1840_ = l_Lean_trace_profiler_threshold;
v___x_1841_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(v_opts_1743_, v___x_1840_);
v___x_1842_ = lean_float_of_nat(v___x_1841_);
v___y_1828_ = v___x_1842_;
goto v___jp_1827_;
}
}
v___jp_1771_:
{
uint8_t v_result_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v_result_1774_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4(v_fst_1753_);
v___x_1775_ = l_Lean_TraceResult_toEmoji(v_result_1774_);
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
v___x_1777_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1);
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 7);
lean_ctor_set(v___x_1767_, 1, v___x_1777_);
lean_ctor_set(v___x_1767_, 0, v___x_1776_);
v___x_1779_ = v___x_1767_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1776_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v_m_1781_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 7);
lean_ctor_set(v___x_1756_, 1, v_a_1773_);
lean_ctor_set(v___x_1756_, 0, v___x_1779_);
v_m_1781_ = v___x_1756_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_a_1773_);
v_m_1781_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; double v___x_1784_; lean_object* v_data_1785_; 
v___x_1782_ = lean_box(v_result_1774_);
v___x_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
v___x_1784_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2);
lean_inc_ref(v_tag_1742_);
lean_inc_ref(v___x_1783_);
lean_inc(v_cls_1740_);
v_data_1785_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1785_, 0, v_cls_1740_);
lean_ctor_set(v_data_1785_, 1, v___x_1783_);
lean_ctor_set(v_data_1785_, 2, v_tag_1742_);
lean_ctor_set_float(v_data_1785_, sizeof(void*)*3, v___x_1784_);
lean_ctor_set_float(v_data_1785_, sizeof(void*)*3 + 8, v___x_1784_);
lean_ctor_set_uint8(v_data_1785_, sizeof(void*)*3 + 16, v_collapsed_1741_);
if (v___x_1770_ == 0)
{
lean_dec_ref(v___x_1783_);
lean_dec(v_snd_1765_);
lean_dec(v_fst_1764_);
lean_dec_ref(v_tag_1742_);
lean_dec(v_cls_1740_);
v___y_1759_ = v___y_1772_;
v___y_1760_ = v_m_1781_;
v_data_1761_ = v_data_1785_;
goto v___jp_1758_;
}
else
{
lean_object* v_data_1786_; double v___x_1787_; double v___x_1788_; 
lean_dec_ref(v_data_1785_);
v_data_1786_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1786_, 0, v_cls_1740_);
lean_ctor_set(v_data_1786_, 1, v___x_1783_);
lean_ctor_set(v_data_1786_, 2, v_tag_1742_);
v___x_1787_ = lean_unbox_float(v_fst_1764_);
lean_dec(v_fst_1764_);
lean_ctor_set_float(v_data_1786_, sizeof(void*)*3, v___x_1787_);
v___x_1788_ = lean_unbox_float(v_snd_1765_);
lean_dec(v_snd_1765_);
lean_ctor_set_float(v_data_1786_, sizeof(void*)*3 + 8, v___x_1788_);
lean_ctor_set_uint8(v_data_1786_, sizeof(void*)*3 + 16, v_collapsed_1741_);
v___y_1759_ = v___y_1772_;
v___y_1760_ = v_m_1781_;
v_data_1761_ = v_data_1786_;
goto v___jp_1758_;
}
}
}
}
v___jp_1791_:
{
lean_object* v_ref_1792_; lean_object* v___x_1793_; 
v_ref_1792_ = lean_ctor_get(v___y_1750_, 5);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v_fst_1753_);
v___x_1793_ = lean_apply_6(v_msg_1746_, v_fst_1753_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, lean_box(0));
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v_a_1794_; 
v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___x_1793_);
lean_inc(v_ref_1792_);
v___y_1772_ = v_ref_1792_;
v_a_1773_ = v_a_1794_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1795_; 
lean_dec_ref(v___x_1793_);
v___x_1795_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4);
lean_inc(v_ref_1792_);
v___y_1772_ = v_ref_1792_;
v_a_1773_ = v___x_1795_;
goto v___jp_1771_;
}
}
v___jp_1796_:
{
if (v_clsEnabled_1744_ == 0)
{
if (v___y_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v_traceState_1799_; lean_object* v_env_1800_; lean_object* v_nextMacroScope_1801_; lean_object* v_ngen_1802_; lean_object* v_auxDeclNGen_1803_; lean_object* v_cache_1804_; lean_object* v_messages_1805_; lean_object* v_infoState_1806_; lean_object* v_snapshotTasks_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1826_; 
lean_del_object(v___x_1767_);
lean_dec(v_snd_1765_);
lean_dec(v_fst_1764_);
lean_del_object(v___x_1756_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v_msg_1746_);
lean_dec_ref(v_tag_1742_);
lean_dec(v_cls_1740_);
v___x_1798_ = lean_st_ref_take(v___y_1751_);
v_traceState_1799_ = lean_ctor_get(v___x_1798_, 4);
v_env_1800_ = lean_ctor_get(v___x_1798_, 0);
v_nextMacroScope_1801_ = lean_ctor_get(v___x_1798_, 1);
v_ngen_1802_ = lean_ctor_get(v___x_1798_, 2);
v_auxDeclNGen_1803_ = lean_ctor_get(v___x_1798_, 3);
v_cache_1804_ = lean_ctor_get(v___x_1798_, 5);
v_messages_1805_ = lean_ctor_get(v___x_1798_, 6);
v_infoState_1806_ = lean_ctor_get(v___x_1798_, 7);
v_snapshotTasks_1807_ = lean_ctor_get(v___x_1798_, 8);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1809_ = v___x_1798_;
v_isShared_1810_ = v_isSharedCheck_1826_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snapshotTasks_1807_);
lean_inc(v_infoState_1806_);
lean_inc(v_messages_1805_);
lean_inc(v_cache_1804_);
lean_inc(v_traceState_1799_);
lean_inc(v_auxDeclNGen_1803_);
lean_inc(v_ngen_1802_);
lean_inc(v_nextMacroScope_1801_);
lean_inc(v_env_1800_);
lean_dec(v___x_1798_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1826_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
uint64_t v_tid_1811_; lean_object* v_traces_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1825_; 
v_tid_1811_ = lean_ctor_get_uint64(v_traceState_1799_, sizeof(void*)*1);
v_traces_1812_ = lean_ctor_get(v_traceState_1799_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_traceState_1799_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1814_ = v_traceState_1799_;
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_traces_1812_);
lean_dec(v_traceState_1799_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1745_, v_traces_1812_);
lean_dec_ref(v_traces_1812_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 0, v___x_1816_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v___x_1816_);
lean_ctor_set_uint64(v_reuseFailAlloc_1824_, sizeof(void*)*1, v_tid_1811_);
v___x_1818_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 4, v___x_1818_);
v___x_1820_ = v___x_1809_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_env_1800_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_nextMacroScope_1801_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_ngen_1802_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_auxDeclNGen_1803_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1823_, 5, v_cache_1804_);
lean_ctor_set(v_reuseFailAlloc_1823_, 6, v_messages_1805_);
lean_ctor_set(v_reuseFailAlloc_1823_, 7, v_infoState_1806_);
lean_ctor_set(v_reuseFailAlloc_1823_, 8, v_snapshotTasks_1807_);
v___x_1820_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_st_ref_set(v___y_1751_, v___x_1820_);
lean_dec(v___y_1751_);
v___x_1822_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_fst_1753_);
return v___x_1822_;
}
}
}
}
}
else
{
goto v___jp_1791_;
}
}
else
{
goto v___jp_1791_;
}
}
v___jp_1827_:
{
double v___x_1829_; double v___x_1830_; double v___x_1831_; uint8_t v___x_1832_; 
v___x_1829_ = lean_unbox_float(v_snd_1765_);
v___x_1830_ = lean_unbox_float(v_fst_1764_);
v___x_1831_ = lean_float_sub(v___x_1829_, v___x_1830_);
v___x_1832_ = lean_float_decLt(v___y_1828_, v___x_1831_);
v___y_1797_ = v___x_1832_;
goto v___jp_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___boxed(lean_object* v_cls_1845_, lean_object* v_collapsed_1846_, lean_object* v_tag_1847_, lean_object* v_opts_1848_, lean_object* v_clsEnabled_1849_, lean_object* v_oldTraces_1850_, lean_object* v_msg_1851_, lean_object* v_resStartStop_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
uint8_t v_collapsed_boxed_1858_; uint8_t v_clsEnabled_boxed_1859_; lean_object* v_res_1860_; 
v_collapsed_boxed_1858_ = lean_unbox(v_collapsed_1846_);
v_clsEnabled_boxed_1859_ = lean_unbox(v_clsEnabled_1849_);
v_res_1860_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v_cls_1845_, v_collapsed_boxed_1858_, v_tag_1847_, v_opts_1848_, v_clsEnabled_boxed_1859_, v_oldTraces_1850_, v_msg_1851_, v_resStartStop_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec_ref(v_opts_1848_);
return v_res_1860_;
}
}
static double _init_l_Lean_mkBelow___closed__4(void){
_start:
{
lean_object* v___x_1867_; double v___x_1868_; 
v___x_1867_ = lean_unsigned_to_nat(1000000000u);
v___x_1868_ = lean_float_of_nat(v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v_options_1875_; uint8_t v_hasTrace_1876_; 
v_options_1875_ = lean_ctor_get(v_a_1872_, 2);
v_hasTrace_1876_ = lean_ctor_get_uint8(v_options_1875_, sizeof(void*)*1);
if (v_hasTrace_1876_ == 0)
{
lean_object* v___x_1877_; 
lean_inc_ref(v_a_1872_);
lean_inc(v_indName_1869_);
v___x_1877_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1942_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1880_ = v___x_1877_;
v_isShared_1881_ = v_isSharedCheck_1942_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_a_1878_);
lean_dec(v___x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1942_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
if (lean_obj_tag(v_a_1878_) == 5)
{
lean_object* v_val_1882_; uint8_t v_isRec_1883_; 
v_val_1882_ = lean_ctor_get(v_a_1878_, 0);
lean_inc_ref(v_val_1882_);
lean_dec_ref(v_a_1878_);
v_isRec_1883_ = lean_ctor_get_uint8(v_val_1882_, sizeof(void*)*6);
if (v_isRec_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1886_; 
lean_dec_ref(v_val_1882_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v___x_1884_ = lean_box(0);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1884_);
v___x_1886_ = v___x_1880_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
else
{
lean_object* v_toConstantVal_1888_; lean_object* v_numParams_1889_; lean_object* v_all_1890_; lean_object* v_numNested_1891_; lean_object* v_type_1892_; lean_object* v___x_1893_; 
lean_del_object(v___x_1880_);
v_toConstantVal_1888_ = lean_ctor_get(v_val_1882_, 0);
lean_inc_ref(v_toConstantVal_1888_);
v_numParams_1889_ = lean_ctor_get(v_val_1882_, 1);
lean_inc(v_numParams_1889_);
v_all_1890_ = lean_ctor_get(v_val_1882_, 3);
lean_inc(v_all_1890_);
v_numNested_1891_ = lean_ctor_get(v_val_1882_, 5);
lean_inc(v_numNested_1891_);
lean_dec_ref(v_val_1882_);
v_type_1892_ = lean_ctor_get(v_toConstantVal_1888_, 2);
lean_inc_ref(v_type_1892_);
lean_dec_ref(v_toConstantVal_1888_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
v___x_1893_ = l_Lean_Meta_isPropFormerType(v_type_1892_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1929_; 
v_a_1894_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1896_ = v___x_1893_;
v_isShared_1897_ = v_isSharedCheck_1929_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1893_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1929_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
uint8_t v___x_1898_; 
v___x_1898_ = lean_unbox(v_a_1894_);
lean_dec(v_a_1894_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_del_object(v___x_1896_);
lean_inc(v_indName_1869_);
v___x_1899_ = l_Lean_mkRecName(v_indName_1869_);
lean_inc(v_indName_1869_);
v___x_1900_ = l_Lean_mkBelowName(v_indName_1869_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
lean_inc(v___x_1900_);
lean_inc(v_numParams_1889_);
lean_inc(v___x_1899_);
v___x_1901_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1899_, v_numParams_1889_, v___x_1900_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1923_; 
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v___x_1901_, 0);
lean_dec(v_unused_1924_);
v___x_1903_ = v___x_1901_;
v_isShared_1904_ = v_isSharedCheck_1923_;
goto v_resetjp_1902_;
}
else
{
lean_dec(v___x_1901_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1923_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = l_List_get_x21Internal___redArg(v___x_1905_, v_all_1890_, v___x_1906_);
lean_dec(v_all_1890_);
v___x_1908_ = lean_name_eq(v___x_1907_, v_indName_1869_);
lean_dec(v_indName_1869_);
lean_dec(v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
lean_dec(v___x_1900_);
lean_dec(v___x_1899_);
lean_dec(v_numNested_1891_);
lean_dec(v_numParams_1889_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
v___x_1909_ = lean_box(0);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 0, v___x_1909_);
v___x_1911_ = v___x_1903_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
lean_del_object(v___x_1903_);
v___x_1913_ = lean_box(0);
v___x_1914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1891_, v___x_1899_, v___x_1900_, v_numParams_1889_, v___x_1906_, v___x_1913_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_numNested_1891_);
if (lean_obj_tag(v___x_1914_) == 0)
{
lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v___x_1914_, 0);
lean_dec(v_unused_1922_);
v___x_1916_ = v___x_1914_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_dec(v___x_1914_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 0, v___x_1913_);
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1913_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
else
{
return v___x_1914_;
}
}
}
}
else
{
lean_dec(v___x_1900_);
lean_dec(v___x_1899_);
lean_dec(v_numNested_1891_);
lean_dec(v_all_1890_);
lean_dec(v_numParams_1889_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
return v___x_1901_;
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_dec(v_numNested_1891_);
lean_dec(v_all_1890_);
lean_dec(v_numParams_1889_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v___x_1925_ = lean_box(0);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1925_);
v___x_1927_ = v___x_1896_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
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
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v_numNested_1891_);
lean_dec(v_all_1890_);
lean_dec(v_numParams_1889_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v_a_1930_ = lean_ctor_get(v___x_1893_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1893_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1893_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
else
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_dec(v_a_1878_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v___x_1938_ = lean_box(0);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v___x_1938_);
v___x_1940_ = v___x_1880_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
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
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v_a_1943_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1877_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1877_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_2154_; 
v___x_1951_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1952_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v___x_1951_, v_a_1872_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_1955_ = v___x_1952_;
v_isShared_1956_ = v_isSharedCheck_2154_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1952_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_2154_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___f_1957_; lean_object* v___x_1958_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v_a_1962_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v_a_1978_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v_a_1985_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v_a_1990_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v_a_2003_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v_a_2008_; uint8_t v___x_2077_; 
lean_inc(v_indName_1869_);
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1957_, 0, v_indName_1869_);
v___x_1958_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_2077_ = lean_unbox(v_a_1953_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
v___x_2078_ = l_Lean_trace_profiler;
v___x_2079_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_1875_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
lean_dec_ref(v___f_1957_);
lean_del_object(v___x_1955_);
lean_dec(v_a_1953_);
lean_inc_ref(v_a_1872_);
lean_inc(v_indName_1869_);
v___x_2080_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2145_; 
v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2083_ = v___x_2080_;
v_isShared_2084_ = v_isSharedCheck_2145_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2080_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2145_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
if (lean_obj_tag(v_a_2081_) == 5)
{
lean_object* v_val_2085_; uint8_t v_isRec_2086_; 
v_val_2085_ = lean_ctor_get(v_a_2081_, 0);
lean_inc_ref(v_val_2085_);
lean_dec_ref(v_a_2081_);
v_isRec_2086_ = lean_ctor_get_uint8(v_val_2085_, sizeof(void*)*6);
if (v_isRec_2086_ == 0)
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
lean_dec_ref(v_val_2085_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v___x_2087_ = lean_box(0);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2087_);
v___x_2089_ = v___x_2083_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
else
{
lean_object* v_toConstantVal_2091_; lean_object* v_numParams_2092_; lean_object* v_all_2093_; lean_object* v_numNested_2094_; lean_object* v_type_2095_; lean_object* v___x_2096_; 
lean_del_object(v___x_2083_);
v_toConstantVal_2091_ = lean_ctor_get(v_val_2085_, 0);
lean_inc_ref(v_toConstantVal_2091_);
v_numParams_2092_ = lean_ctor_get(v_val_2085_, 1);
lean_inc(v_numParams_2092_);
v_all_2093_ = lean_ctor_get(v_val_2085_, 3);
lean_inc(v_all_2093_);
v_numNested_2094_ = lean_ctor_get(v_val_2085_, 5);
lean_inc(v_numNested_2094_);
lean_dec_ref(v_val_2085_);
v_type_2095_ = lean_ctor_get(v_toConstantVal_2091_, 2);
lean_inc_ref(v_type_2095_);
lean_dec_ref(v_toConstantVal_2091_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
v___x_2096_ = l_Lean_Meta_isPropFormerType(v_type_2095_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2132_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2132_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2132_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
uint8_t v___x_2101_; 
v___x_2101_ = lean_unbox(v_a_2097_);
lean_dec(v_a_2097_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
lean_del_object(v___x_2099_);
lean_inc(v_indName_1869_);
v___x_2102_ = l_Lean_mkRecName(v_indName_1869_);
lean_inc(v_indName_1869_);
v___x_2103_ = l_Lean_mkBelowName(v_indName_1869_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
lean_inc(v___x_2103_);
lean_inc(v_numParams_2092_);
lean_inc(v___x_2102_);
v___x_2104_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2102_, v_numParams_2092_, v___x_2103_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2126_; 
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v___x_2104_, 0);
lean_dec(v_unused_2127_);
v___x_2106_ = v___x_2104_;
v_isShared_2107_ = v_isSharedCheck_2126_;
goto v_resetjp_2105_;
}
else
{
lean_dec(v___x_2104_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2126_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; uint8_t v___x_2111_; 
v___x_2108_ = lean_box(0);
v___x_2109_ = lean_unsigned_to_nat(0u);
v___x_2110_ = l_List_get_x21Internal___redArg(v___x_2108_, v_all_2093_, v___x_2109_);
lean_dec(v_all_2093_);
v___x_2111_ = lean_name_eq(v___x_2110_, v_indName_1869_);
lean_dec(v_indName_1869_);
lean_dec(v___x_2110_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; lean_object* v___x_2114_; 
lean_dec(v___x_2103_);
lean_dec(v___x_2102_);
lean_dec(v_numNested_2094_);
lean_dec(v_numParams_2092_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
v___x_2112_ = lean_box(0);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 0, v___x_2112_);
v___x_2114_ = v___x_2106_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_del_object(v___x_2106_);
v___x_2116_ = lean_box(0);
v___x_2117_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2094_, v___x_2102_, v___x_2103_, v_numParams_2092_, v___x_2109_, v___x_2116_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_numNested_2094_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v___x_2117_, 0);
lean_dec(v_unused_2125_);
v___x_2119_ = v___x_2117_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v___x_2117_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2116_);
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2116_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
else
{
return v___x_2117_;
}
}
}
}
else
{
lean_dec(v___x_2103_);
lean_dec(v___x_2102_);
lean_dec(v_numNested_2094_);
lean_dec(v_all_2093_);
lean_dec(v_numParams_2092_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
return v___x_2104_;
}
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2130_; 
lean_dec(v_numNested_2094_);
lean_dec(v_all_2093_);
lean_dec(v_numParams_2092_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v___x_2128_ = lean_box(0);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2128_);
v___x_2130_ = v___x_2099_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
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
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_numNested_2094_);
lean_dec(v_all_2093_);
lean_dec(v_numParams_2092_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v_a_2133_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2096_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2096_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2143_; 
lean_dec(v_a_2081_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v___x_2141_ = lean_box(0);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2141_);
v___x_2143_ = v___x_2083_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v___x_2141_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_indName_1869_);
v_a_2146_ = lean_ctor_get(v___x_2080_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___x_2080_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___x_2080_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2080_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
else
{
lean_inc_ref(v_options_1875_);
goto v___jp_2010_;
}
}
else
{
lean_inc_ref(v_options_1875_);
goto v___jp_2010_;
}
v___jp_1959_:
{
lean_object* v___x_1963_; double v___x_1964_; double v___x_1965_; double v___x_1966_; double v___x_1967_; double v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1963_ = lean_io_mono_nanos_now();
v___x_1964_ = lean_float_of_nat(v___y_1961_);
v___x_1965_ = lean_float_once(&l_Lean_mkBelow___closed__4, &l_Lean_mkBelow___closed__4_once, _init_l_Lean_mkBelow___closed__4);
v___x_1966_ = lean_float_div(v___x_1964_, v___x_1965_);
v___x_1967_ = lean_float_of_nat(v___x_1963_);
v___x_1968_ = lean_float_div(v___x_1967_, v___x_1965_);
v___x_1969_ = lean_box_float(v___x_1966_);
v___x_1970_ = lean_box_float(v___x_1968_);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v_a_1962_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = lean_unbox(v_a_1953_);
lean_dec(v_a_1953_);
v___x_1974_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_1951_, v_hasTrace_1876_, v___x_1958_, v_options_1875_, v___x_1973_, v___y_1960_, v___f_1957_, v___x_1972_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec_ref(v_options_1875_);
return v___x_1974_;
}
v___jp_1975_:
{
lean_object* v___x_1980_; 
if (v_isShared_1956_ == 0)
{
lean_ctor_set_tag(v___x_1955_, 1);
lean_ctor_set(v___x_1955_, 0, v_a_1978_);
v___x_1980_ = v___x_1955_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
v___y_1960_ = v___y_1976_;
v___y_1961_ = v___y_1977_;
v_a_1962_ = v___x_1980_;
goto v___jp_1959_;
}
}
v___jp_1982_:
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1985_);
v___y_1960_ = v___y_1983_;
v___y_1961_ = v___y_1984_;
v_a_1962_ = v___x_1986_;
goto v___jp_1959_;
}
v___jp_1987_:
{
lean_object* v___x_1991_; double v___x_1992_; double v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1991_ = lean_io_get_num_heartbeats();
v___x_1992_ = lean_float_of_nat(v___y_1989_);
v___x_1993_ = lean_float_of_nat(v___x_1991_);
v___x_1994_ = lean_box_float(v___x_1992_);
v___x_1995_ = lean_box_float(v___x_1993_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1994_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_a_1990_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_unbox(v_a_1953_);
lean_dec(v_a_1953_);
v___x_1999_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_1951_, v_hasTrace_1876_, v___x_1958_, v_options_1875_, v___x_1998_, v___y_1988_, v___f_1957_, v___x_1997_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec_ref(v_options_1875_);
return v___x_1999_;
}
v___jp_2000_:
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_a_2003_);
v___y_1988_ = v___y_2001_;
v___y_1989_ = v___y_2002_;
v_a_1990_ = v___x_2004_;
goto v___jp_1987_;
}
v___jp_2005_:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_a_2008_);
v___y_1988_ = v___y_2006_;
v___y_1989_ = v___y_2007_;
v_a_1990_ = v___x_2009_;
goto v___jp_1987_;
}
v___jp_2010_:
{
lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2011_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v_a_1873_);
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref(v___x_2011_);
v___x_2013_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2014_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_1875_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = lean_io_mono_nanos_now();
lean_inc_ref(v_a_1872_);
lean_inc(v_indName_1869_);
v___x_2016_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2016_);
if (lean_obj_tag(v_a_2017_) == 5)
{
lean_object* v_val_2018_; uint8_t v_isRec_2019_; 
v_val_2018_ = lean_ctor_get(v_a_2017_, 0);
lean_inc_ref(v_val_2018_);
lean_dec_ref(v_a_2017_);
v_isRec_2019_ = lean_ctor_get_uint8(v_val_2018_, sizeof(void*)*6);
if (v_isRec_2019_ == 0)
{
lean_object* v___x_2020_; 
lean_dec_ref(v_val_2018_);
lean_dec(v_indName_1869_);
v___x_2020_ = lean_box(0);
v___y_1976_ = v_a_2012_;
v___y_1977_ = v___x_2015_;
v_a_1978_ = v___x_2020_;
goto v___jp_1975_;
}
else
{
lean_object* v_toConstantVal_2021_; lean_object* v_numParams_2022_; lean_object* v_all_2023_; lean_object* v_numNested_2024_; lean_object* v_type_2025_; lean_object* v___x_2026_; 
v_toConstantVal_2021_ = lean_ctor_get(v_val_2018_, 0);
lean_inc_ref(v_toConstantVal_2021_);
v_numParams_2022_ = lean_ctor_get(v_val_2018_, 1);
lean_inc(v_numParams_2022_);
v_all_2023_ = lean_ctor_get(v_val_2018_, 3);
lean_inc(v_all_2023_);
v_numNested_2024_ = lean_ctor_get(v_val_2018_, 5);
lean_inc(v_numNested_2024_);
lean_dec_ref(v_val_2018_);
v_type_2025_ = lean_ctor_get(v_toConstantVal_2021_, 2);
lean_inc_ref(v_type_2025_);
lean_dec_ref(v_toConstantVal_2021_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
v___x_2026_ = l_Lean_Meta_isPropFormerType(v_type_2025_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; uint8_t v___x_2028_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = lean_unbox(v_a_2027_);
lean_dec(v_a_2027_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_inc(v_indName_1869_);
v___x_2029_ = l_Lean_mkRecName(v_indName_1869_);
lean_inc(v_indName_1869_);
v___x_2030_ = l_Lean_mkBelowName(v_indName_1869_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
lean_inc(v___x_2030_);
lean_inc(v_numParams_2022_);
lean_inc(v___x_2029_);
v___x_2031_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2029_, v_numParams_2022_, v___x_2030_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
lean_dec_ref(v___x_2031_);
v___x_2032_ = lean_box(0);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = l_List_get_x21Internal___redArg(v___x_2032_, v_all_2023_, v___x_2033_);
lean_dec(v_all_2023_);
v___x_2035_ = lean_name_eq(v___x_2034_, v_indName_1869_);
lean_dec(v_indName_1869_);
lean_dec(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec(v___x_2030_);
lean_dec(v___x_2029_);
lean_dec(v_numNested_2024_);
lean_dec(v_numParams_2022_);
v___x_2036_ = lean_box(0);
v___y_1976_ = v_a_2012_;
v___y_1977_ = v___x_2015_;
v_a_1978_ = v___x_2036_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_box(0);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
v___x_2038_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2024_, v___x_2029_, v___x_2030_, v_numParams_2022_, v___x_2033_, v___x_2037_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_numNested_2024_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_dec_ref(v___x_2038_);
v___y_1976_ = v_a_2012_;
v___y_1977_ = v___x_2015_;
v_a_1978_ = v___x_2037_;
goto v___jp_1975_;
}
else
{
lean_object* v_a_2039_; 
lean_del_object(v___x_1955_);
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___x_2038_);
v___y_1983_ = v_a_2012_;
v___y_1984_ = v___x_2015_;
v_a_1985_ = v_a_2039_;
goto v___jp_1982_;
}
}
}
else
{
lean_dec(v___x_2030_);
lean_dec(v___x_2029_);
lean_dec(v_numNested_2024_);
lean_dec(v_all_2023_);
lean_dec(v_numParams_2022_);
lean_dec(v_indName_1869_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2040_; 
v_a_2040_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2031_);
v___y_1976_ = v_a_2012_;
v___y_1977_ = v___x_2015_;
v_a_1978_ = v_a_2040_;
goto v___jp_1975_;
}
else
{
lean_object* v_a_2041_; 
lean_del_object(v___x_1955_);
v_a_2041_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2041_);
lean_dec_ref(v___x_2031_);
v___y_1983_ = v_a_2012_;
v___y_1984_ = v___x_2015_;
v_a_1985_ = v_a_2041_;
goto v___jp_1982_;
}
}
}
else
{
lean_object* v___x_2042_; 
lean_dec(v_numNested_2024_);
lean_dec(v_all_2023_);
lean_dec(v_numParams_2022_);
lean_dec(v_indName_1869_);
v___x_2042_ = lean_box(0);
v___y_1976_ = v_a_2012_;
v___y_1977_ = v___x_2015_;
v_a_1978_ = v___x_2042_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2043_; 
lean_dec(v_numNested_2024_);
lean_dec(v_all_2023_);
lean_dec(v_numParams_2022_);
lean_del_object(v___x_1955_);
lean_dec(v_indName_1869_);
v_a_2043_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2026_);
v___y_1983_ = v_a_2012_;
v___y_1984_ = v___x_2015_;
v_a_1985_ = v_a_2043_;
goto v___jp_1982_;
}
}
}
else
{
lean_object* v___x_2044_; 
lean_dec(v_a_2017_);
lean_dec(v_indName_1869_);
v___x_2044_ = lean_box(0);
v___y_1976_ = v_a_2012_;
v___y_1977_ = v___x_2015_;
v_a_1978_ = v___x_2044_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2045_; 
lean_del_object(v___x_1955_);
lean_dec(v_indName_1869_);
v_a_2045_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2016_);
v___y_1983_ = v_a_2012_;
v___y_1984_ = v___x_2015_;
v_a_1985_ = v_a_2045_;
goto v___jp_1982_;
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_del_object(v___x_1955_);
v___x_2046_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_a_1872_);
lean_inc(v_indName_1869_);
v___x_2047_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
if (lean_obj_tag(v_a_2048_) == 5)
{
lean_object* v_val_2049_; uint8_t v_isRec_2050_; 
v_val_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc_ref(v_val_2049_);
lean_dec_ref(v_a_2048_);
v_isRec_2050_ = lean_ctor_get_uint8(v_val_2049_, sizeof(void*)*6);
if (v_isRec_2050_ == 0)
{
lean_object* v___x_2051_; 
lean_dec_ref(v_val_2049_);
lean_dec(v_indName_1869_);
v___x_2051_ = lean_box(0);
v___y_2001_ = v_a_2012_;
v___y_2002_ = v___x_2046_;
v_a_2003_ = v___x_2051_;
goto v___jp_2000_;
}
else
{
lean_object* v_toConstantVal_2052_; lean_object* v_numParams_2053_; lean_object* v_all_2054_; lean_object* v_numNested_2055_; lean_object* v_type_2056_; lean_object* v___x_2057_; 
v_toConstantVal_2052_ = lean_ctor_get(v_val_2049_, 0);
lean_inc_ref(v_toConstantVal_2052_);
v_numParams_2053_ = lean_ctor_get(v_val_2049_, 1);
lean_inc(v_numParams_2053_);
v_all_2054_ = lean_ctor_get(v_val_2049_, 3);
lean_inc(v_all_2054_);
v_numNested_2055_ = lean_ctor_get(v_val_2049_, 5);
lean_inc(v_numNested_2055_);
lean_dec_ref(v_val_2049_);
v_type_2056_ = lean_ctor_get(v_toConstantVal_2052_, 2);
lean_inc_ref(v_type_2056_);
lean_dec_ref(v_toConstantVal_2052_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
v___x_2057_ = l_Lean_Meta_isPropFormerType(v_type_2056_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; uint8_t v___x_2059_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
v___x_2059_ = lean_unbox(v_a_2058_);
lean_dec(v_a_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_inc(v_indName_1869_);
v___x_2060_ = l_Lean_mkRecName(v_indName_1869_);
lean_inc(v_indName_1869_);
v___x_2061_ = l_Lean_mkBelowName(v_indName_1869_);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
lean_inc(v___x_2061_);
lean_inc(v_numParams_2053_);
lean_inc(v___x_2060_);
v___x_2062_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2060_, v_numParams_2053_, v___x_2061_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
lean_dec_ref(v___x_2062_);
v___x_2063_ = lean_box(0);
v___x_2064_ = lean_unsigned_to_nat(0u);
v___x_2065_ = l_List_get_x21Internal___redArg(v___x_2063_, v_all_2054_, v___x_2064_);
lean_dec(v_all_2054_);
v___x_2066_ = lean_name_eq(v___x_2065_, v_indName_1869_);
lean_dec(v_indName_1869_);
lean_dec(v___x_2065_);
if (v___x_2066_ == 0)
{
lean_object* v___x_2067_; 
lean_dec(v___x_2061_);
lean_dec(v___x_2060_);
lean_dec(v_numNested_2055_);
lean_dec(v_numParams_2053_);
v___x_2067_ = lean_box(0);
v___y_2001_ = v_a_2012_;
v___y_2002_ = v___x_2046_;
v_a_2003_ = v___x_2067_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2068_ = lean_box(0);
lean_inc(v_a_1873_);
lean_inc_ref(v_a_1872_);
lean_inc(v_a_1871_);
lean_inc_ref(v_a_1870_);
v___x_2069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2055_, v___x_2060_, v___x_2061_, v_numParams_2053_, v___x_2064_, v___x_2068_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
lean_dec(v_numNested_2055_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_dec_ref(v___x_2069_);
v___y_2001_ = v_a_2012_;
v___y_2002_ = v___x_2046_;
v_a_2003_ = v___x_2068_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2070_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref(v___x_2069_);
v___y_2006_ = v_a_2012_;
v___y_2007_ = v___x_2046_;
v_a_2008_ = v_a_2070_;
goto v___jp_2005_;
}
}
}
else
{
lean_dec(v___x_2061_);
lean_dec(v___x_2060_);
lean_dec(v_numNested_2055_);
lean_dec(v_all_2054_);
lean_dec(v_numParams_2053_);
lean_dec(v_indName_1869_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2071_; 
v_a_2071_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2062_);
v___y_2001_ = v_a_2012_;
v___y_2002_ = v___x_2046_;
v_a_2003_ = v_a_2071_;
goto v___jp_2000_;
}
else
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2062_);
v___y_2006_ = v_a_2012_;
v___y_2007_ = v___x_2046_;
v_a_2008_ = v_a_2072_;
goto v___jp_2005_;
}
}
}
else
{
lean_object* v___x_2073_; 
lean_dec(v_numNested_2055_);
lean_dec(v_all_2054_);
lean_dec(v_numParams_2053_);
lean_dec(v_indName_1869_);
v___x_2073_ = lean_box(0);
v___y_2001_ = v_a_2012_;
v___y_2002_ = v___x_2046_;
v_a_2003_ = v___x_2073_;
goto v___jp_2000_;
}
}
else
{
lean_object* v_a_2074_; 
lean_dec(v_numNested_2055_);
lean_dec(v_all_2054_);
lean_dec(v_numParams_2053_);
lean_dec(v_indName_1869_);
v_a_2074_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2074_);
lean_dec_ref(v___x_2057_);
v___y_2006_ = v_a_2012_;
v___y_2007_ = v___x_2046_;
v_a_2008_ = v_a_2074_;
goto v___jp_2005_;
}
}
}
else
{
lean_object* v___x_2075_; 
lean_dec(v_a_2048_);
lean_dec(v_indName_1869_);
v___x_2075_ = lean_box(0);
v___y_2001_ = v_a_2012_;
v___y_2002_ = v___x_2046_;
v_a_2003_ = v___x_2075_;
goto v___jp_2000_;
}
}
else
{
lean_object* v_a_2076_; 
lean_dec(v_indName_1869_);
v_a_2076_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2076_);
lean_dec_ref(v___x_2047_);
v___y_2006_ = v_a_2012_;
v___y_2007_ = v___x_2046_;
v_a_2008_ = v_a_2076_;
goto v___jp_2005_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_mkBelow(v_indName_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2162_, lean_object* v___x_2163_, lean_object* v___x_2164_, lean_object* v___x_2165_, lean_object* v_inst_2166_, lean_object* v_R_2167_, lean_object* v_a_2168_, lean_object* v_b_2169_, lean_object* v_c_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2162_, v___x_2163_, v___x_2164_, v___x_2165_, v_a_2168_, v_b_2169_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2177_, lean_object* v___x_2178_, lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v_inst_2181_, lean_object* v_R_2182_, lean_object* v_a_2183_, lean_object* v_b_2184_, lean_object* v_c_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2177_, v___x_2178_, v___x_2179_, v___x_2180_, v_inst_2181_, v_R_2182_, v_a_2183_, v_b_2184_, v_c_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v_upperBound_2177_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6(lean_object* v_00_u03b1_2192_, lean_object* v_x_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v___x_2199_; 
v___x_2199_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_x_2193_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2200_, lean_object* v_x_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6(v_00_u03b1_2200_, v_x_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
if (lean_obj_tag(v_a_2208_) == 0)
{
lean_object* v___x_2210_; 
v___x_2210_ = l_List_reverse___redArg(v_a_2209_);
return v___x_2210_;
}
else
{
lean_object* v_head_2211_; lean_object* v_tail_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2221_; 
v_head_2211_ = lean_ctor_get(v_a_2208_, 0);
v_tail_2212_ = lean_ctor_get(v_a_2208_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_a_2208_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2214_ = v_a_2208_;
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_tail_2212_);
lean_inc(v_head_2211_);
lean_dec(v_a_2208_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = l_Lean_MessageData_ofExpr(v_head_2211_);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v_a_2209_);
lean_ctor_set(v___x_2214_, 0, v___x_2216_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_a_2209_);
v___x_2218_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
v_a_2208_ = v_tail_2212_;
v_a_2209_ = v___x_2218_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2222_, lean_object* v_v_2223_, lean_object* v_i_2224_){
_start:
{
lean_object* v___x_2225_; uint8_t v___x_2226_; 
v___x_2225_ = lean_array_get_size(v_xs_2222_);
v___x_2226_ = lean_nat_dec_lt(v_i_2224_, v___x_2225_);
if (v___x_2226_ == 0)
{
lean_object* v___x_2227_; 
lean_dec(v_i_2224_);
v___x_2227_ = lean_box(0);
return v___x_2227_;
}
else
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = lean_array_fget_borrowed(v_xs_2222_, v_i_2224_);
v___x_2229_ = lean_expr_eqv(v___x_2228_, v_v_2223_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_unsigned_to_nat(1u);
v___x_2231_ = lean_nat_add(v_i_2224_, v___x_2230_);
lean_dec(v_i_2224_);
v_i_2224_ = v___x_2231_;
goto _start;
}
else
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_i_2224_);
return v___x_2233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2234_, lean_object* v_v_2235_, lean_object* v_i_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2234_, v_v_2235_, v_i_2236_);
lean_dec_ref(v_v_2235_);
lean_dec_ref(v_xs_2234_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2238_, lean_object* v_v_2239_){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2238_, v_v_2239_, v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2242_, lean_object* v_v_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2242_, v_v_2243_);
lean_dec_ref(v_v_2243_);
lean_dec_ref(v_xs_2242_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2245_, lean_object* v_v_2246_){
_start:
{
lean_object* v___x_2247_; 
v___x_2247_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2245_, v_v_2246_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_box(0);
return v___x_2248_;
}
else
{
lean_object* v_val_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_val_2249_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2247_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_val_2249_);
lean_dec(v___x_2247_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_val_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2257_, lean_object* v_v_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2257_, v_v_2258_);
lean_dec_ref(v_v_2258_);
lean_dec_ref(v_xs_2257_);
return v_res_2259_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2266_, lean_object* v_prods_2267_, lean_object* v_motives_2268_, lean_object* v_fs_2269_, lean_object* v_minor__type_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_, lean_object* v_x_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 5)
{
lean_object* v_fn_2279_; lean_object* v_arg_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v_fn_2279_ = lean_ctor_get(v_x_2271_, 0);
lean_inc_ref(v_fn_2279_);
v_arg_2280_ = lean_ctor_get(v_x_2271_, 1);
lean_inc_ref(v_arg_2280_);
lean_dec_ref(v_x_2271_);
v___x_2281_ = lean_array_set(v_x_2272_, v_x_2273_, v_arg_2280_);
v___x_2282_ = lean_unsigned_to_nat(1u);
v___x_2283_ = lean_nat_sub(v_x_2273_, v___x_2282_);
lean_dec(v_x_2273_);
v_x_2271_ = v_fn_2279_;
v_x_2272_ = v___x_2281_;
v_x_2273_ = v___x_2283_;
goto _start;
}
else
{
lean_object* v___x_2285_; 
lean_dec(v_x_2273_);
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
lean_inc(v___y_2275_);
lean_inc_ref(v___y_2274_);
v___x_2285_ = l_Lean_Meta_PProdN_mk(v_rlvl_2266_, v_prods_2267_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; lean_object* v___x_2287_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
v___x_2287_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2268_, v_x_2271_);
lean_dec_ref(v_x_2271_);
if (lean_obj_tag(v___x_2287_) == 1)
{
lean_object* v_val_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v_minor__type_2270_);
lean_dec_ref(v_motives_2268_);
v_val_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_val_2288_);
lean_dec_ref(v___x_2287_);
v___x_2289_ = l_Lean_instInhabitedExpr;
v___x_2290_ = lean_array_get_borrowed(v___x_2289_, v_fs_2269_, v_val_2288_);
lean_dec(v_val_2288_);
lean_inc(v_a_2286_);
v___x_2291_ = lean_array_push(v_x_2272_, v_a_2286_);
lean_inc(v___x_2290_);
v___x_2292_ = l_Lean_mkAppN(v___x_2290_, v___x_2291_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = l_Lean_Meta_mkPProdMk(v___x_2292_, v_a_2286_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2293_;
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec(v___x_2287_);
lean_dec(v_a_2286_);
lean_dec_ref(v_x_2272_);
v___x_2294_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2295_ = l_Lean_MessageData_ofExpr(v_minor__type_2270_);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = lean_array_to_list(v_motives_2268_);
v___x_2300_ = lean_box(0);
v___x_2301_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2299_, v___x_2300_);
v___x_2302_ = l_Lean_MessageData_ofList(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2298_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2303_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v___x_2304_;
}
}
else
{
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v_x_2272_);
lean_dec_ref(v_x_2271_);
lean_dec_ref(v_minor__type_2270_);
lean_dec_ref(v_motives_2268_);
return v___x_2285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2305_, lean_object* v_prods_2306_, lean_object* v_motives_2307_, lean_object* v_fs_2308_, lean_object* v_minor__type_2309_, lean_object* v_x_2310_, lean_object* v_x_2311_, lean_object* v_x_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2305_, v_prods_2306_, v_motives_2307_, v_fs_2308_, v_minor__type_2309_, v_x_2310_, v_x_2311_, v_x_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec_ref(v_fs_2308_);
return v_res_2318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2319_; lean_object* v_dummy_2320_; 
v___x_2319_ = lean_box(0);
v_dummy_2320_ = l_Lean_Expr_sort___override(v___x_2319_);
return v_dummy_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2321_, lean_object* v_head_2322_, lean_object* v_belows_2323_, lean_object* v_prods_2324_, lean_object* v_rlvl_2325_, lean_object* v_fs_2326_, lean_object* v_minor__type_2327_, lean_object* v_tail_2328_, lean_object* v_arg__args_2329_, lean_object* v_arg__type_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2321_, v_head_2322_, v_belows_2323_, v_prods_2324_, v_rlvl_2325_, v_fs_2326_, v_minor__type_2327_, v_tail_2328_, v_arg__args_2329_, v_arg__type_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec_ref(v_arg__args_2329_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2337_, lean_object* v_motives_2338_, lean_object* v_belows_2339_, lean_object* v_fs_2340_, lean_object* v_minor__type_2341_, lean_object* v_prods_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
if (lean_obj_tag(v_a_2343_) == 0)
{
lean_object* v_dummy_2349_; lean_object* v_nargs_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec_ref(v_belows_2339_);
v_dummy_2349_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2350_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2341_);
lean_inc(v_nargs_2350_);
v___x_2351_ = lean_mk_array(v_nargs_2350_, v_dummy_2349_);
v___x_2352_ = lean_unsigned_to_nat(1u);
v___x_2353_ = lean_nat_sub(v_nargs_2350_, v___x_2352_);
lean_dec(v_nargs_2350_);
lean_inc_ref(v_minor__type_2341_);
v___x_2354_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2337_, v_prods_2342_, v_motives_2338_, v_fs_2340_, v_minor__type_2341_, v_minor__type_2341_, v___x_2351_, v___x_2353_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec_ref(v_fs_2340_);
return v___x_2354_;
}
else
{
lean_object* v_head_2355_; lean_object* v_tail_2356_; lean_object* v___x_2357_; 
v_head_2355_ = lean_ctor_get(v_a_2343_, 0);
lean_inc(v_head_2355_);
v_tail_2356_ = lean_ctor_get(v_a_2343_, 1);
lean_inc(v_tail_2356_);
lean_dec_ref(v_a_2343_);
lean_inc(v_a_2347_);
lean_inc_ref(v_a_2346_);
lean_inc(v_a_2345_);
lean_inc_ref(v_a_2344_);
lean_inc(v_head_2355_);
v___x_2357_ = lean_infer_type(v_head_2355_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_object* v_a_2358_; lean_object* v___f_2359_; uint8_t v___x_2360_; lean_object* v___x_2361_; 
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
lean_inc(v_a_2358_);
lean_dec_ref(v___x_2357_);
v___f_2359_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2359_, 0, v_motives_2338_);
lean_closure_set(v___f_2359_, 1, v_head_2355_);
lean_closure_set(v___f_2359_, 2, v_belows_2339_);
lean_closure_set(v___f_2359_, 3, v_prods_2342_);
lean_closure_set(v___f_2359_, 4, v_rlvl_2337_);
lean_closure_set(v___f_2359_, 5, v_fs_2340_);
lean_closure_set(v___f_2359_, 6, v_minor__type_2341_);
lean_closure_set(v___f_2359_, 7, v_tail_2356_);
v___x_2360_ = 0;
v___x_2361_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2358_, v___f_2359_, v___x_2360_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
return v___x_2361_;
}
else
{
lean_dec(v_tail_2356_);
lean_dec(v_head_2355_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
lean_dec_ref(v_prods_2342_);
lean_dec_ref(v_minor__type_2341_);
lean_dec_ref(v_fs_2340_);
lean_dec_ref(v_belows_2339_);
lean_dec_ref(v_motives_2338_);
lean_dec(v_rlvl_2337_);
return v___x_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2362_, lean_object* v_rlvl_2363_, lean_object* v_motives_2364_, lean_object* v_belows_2365_, lean_object* v_fs_2366_, lean_object* v_minor__type_2367_, lean_object* v_tail_2368_, uint8_t v___x_2369_, uint8_t v___x_2370_, uint8_t v___x_2371_, lean_object* v_arg_x27_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
lean_inc_ref(v_arg_x27_2372_);
v___x_2378_ = lean_array_push(v_prods_2362_, v_arg_x27_2372_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v___y_2374_);
lean_inc_ref(v___y_2373_);
v___x_2379_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2363_, v_motives_2364_, v_belows_2365_, v_fs_2366_, v_minor__type_2367_, v___x_2378_, v_tail_2368_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
if (lean_obj_tag(v___x_2379_) == 0)
{
lean_object* v_a_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_a_2380_ = lean_ctor_get(v___x_2379_, 0);
lean_inc(v_a_2380_);
lean_dec_ref(v___x_2379_);
v___x_2381_ = lean_unsigned_to_nat(1u);
v___x_2382_ = lean_mk_empty_array_with_capacity(v___x_2381_);
v___x_2383_ = lean_array_push(v___x_2382_, v_arg_x27_2372_);
v___x_2384_ = l_Lean_Meta_mkLambdaFVars(v___x_2383_, v_a_2380_, v___x_2369_, v___x_2370_, v___x_2369_, v___x_2370_, v___x_2371_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v___x_2383_);
return v___x_2384_;
}
else
{
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec_ref(v_arg_x27_2372_);
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2385_, lean_object* v_rlvl_2386_, lean_object* v_motives_2387_, lean_object* v_belows_2388_, lean_object* v_fs_2389_, lean_object* v_minor__type_2390_, lean_object* v_tail_2391_, lean_object* v___x_2392_, lean_object* v___x_2393_, lean_object* v___x_2394_, lean_object* v_arg_x27_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
uint8_t v___x_1780__boxed_2401_; uint8_t v___x_1781__boxed_2402_; uint8_t v___x_1782__boxed_2403_; lean_object* v_res_2404_; 
v___x_1780__boxed_2401_ = lean_unbox(v___x_2392_);
v___x_1781__boxed_2402_ = lean_unbox(v___x_2393_);
v___x_1782__boxed_2403_ = lean_unbox(v___x_2394_);
v_res_2404_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2385_, v_rlvl_2386_, v_motives_2387_, v_belows_2388_, v_fs_2389_, v_minor__type_2390_, v_tail_2391_, v___x_1780__boxed_2401_, v___x_1781__boxed_2402_, v___x_1782__boxed_2403_, v_arg_x27_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2405_, lean_object* v_head_2406_, lean_object* v_belows_2407_, lean_object* v_arg__type_2408_, lean_object* v_prods_2409_, lean_object* v_rlvl_2410_, lean_object* v_fs_2411_, lean_object* v_minor__type_2412_, lean_object* v_tail_2413_, lean_object* v_arg__args_2414_, lean_object* v_x_2415_, lean_object* v_x_2416_, lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
if (lean_obj_tag(v_x_2415_) == 5)
{
lean_object* v_fn_2423_; lean_object* v_arg_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_fn_2423_ = lean_ctor_get(v_x_2415_, 0);
lean_inc_ref(v_fn_2423_);
v_arg_2424_ = lean_ctor_get(v_x_2415_, 1);
lean_inc_ref(v_arg_2424_);
lean_dec_ref(v_x_2415_);
v___x_2425_ = lean_array_set(v_x_2416_, v_x_2417_, v_arg_2424_);
v___x_2426_ = lean_unsigned_to_nat(1u);
v___x_2427_ = lean_nat_sub(v_x_2417_, v___x_2426_);
lean_dec(v_x_2417_);
v_x_2415_ = v_fn_2423_;
v_x_2416_ = v___x_2425_;
v_x_2417_ = v___x_2427_;
goto _start;
}
else
{
lean_object* v___x_2429_; 
lean_dec(v_x_2417_);
v___x_2429_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2405_, v_x_2415_);
lean_dec_ref(v_x_2415_);
if (lean_obj_tag(v___x_2429_) == 1)
{
lean_object* v_val_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v_val_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_val_2430_);
lean_dec_ref(v___x_2429_);
v___x_2431_ = l_Lean_Expr_fvarId_x21(v_head_2406_);
lean_dec_ref(v_head_2406_);
lean_inc_ref(v___y_2418_);
v___x_2432_ = l_Lean_FVarId_getUserName___redArg(v___x_2431_, v___y_2418_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref(v___x_2432_);
v___x_2434_ = l_Lean_instInhabitedExpr;
v___x_2435_ = lean_array_get_borrowed(v___x_2434_, v_belows_2407_, v_val_2430_);
lean_dec(v_val_2430_);
lean_inc(v___x_2435_);
v___x_2436_ = l_Lean_mkAppN(v___x_2435_, v_x_2416_);
lean_dec_ref(v_x_2416_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___x_2437_ = l_Lean_Meta_mkPProd(v_arg__type_2408_, v___x_2436_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; uint8_t v___x_2439_; uint8_t v___x_2440_; uint8_t v___x_2441_; lean_object* v___x_2442_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref(v___x_2437_);
v___x_2439_ = 0;
v___x_2440_ = 1;
v___x_2441_ = 1;
v___x_2442_ = l_Lean_Meta_mkForallFVars(v_arg__args_2414_, v_a_2438_, v___x_2439_, v___x_2440_, v___x_2440_, v___x_2441_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___f_2447_; lean_object* v___x_2448_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref(v___x_2442_);
v___x_2444_ = lean_box(v___x_2439_);
v___x_2445_ = lean_box(v___x_2440_);
v___x_2446_ = lean_box(v___x_2441_);
v___f_2447_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2447_, 0, v_prods_2409_);
lean_closure_set(v___f_2447_, 1, v_rlvl_2410_);
lean_closure_set(v___f_2447_, 2, v_motives_2405_);
lean_closure_set(v___f_2447_, 3, v_belows_2407_);
lean_closure_set(v___f_2447_, 4, v_fs_2411_);
lean_closure_set(v___f_2447_, 5, v_minor__type_2412_);
lean_closure_set(v___f_2447_, 6, v_tail_2413_);
lean_closure_set(v___f_2447_, 7, v___x_2444_);
lean_closure_set(v___f_2447_, 8, v___x_2445_);
lean_closure_set(v___f_2447_, 9, v___x_2446_);
v___x_2448_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2433_, v_a_2443_, v___f_2447_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
return v___x_2448_;
}
else
{
lean_dec(v_a_2433_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_tail_2413_);
lean_dec_ref(v_minor__type_2412_);
lean_dec_ref(v_fs_2411_);
lean_dec(v_rlvl_2410_);
lean_dec_ref(v_prods_2409_);
lean_dec_ref(v_belows_2407_);
lean_dec_ref(v_motives_2405_);
return v___x_2442_;
}
}
else
{
lean_dec(v_a_2433_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_tail_2413_);
lean_dec_ref(v_minor__type_2412_);
lean_dec_ref(v_fs_2411_);
lean_dec(v_rlvl_2410_);
lean_dec_ref(v_prods_2409_);
lean_dec_ref(v_belows_2407_);
lean_dec_ref(v_motives_2405_);
return v___x_2437_;
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_dec(v_val_2430_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v_x_2416_);
lean_dec(v_tail_2413_);
lean_dec_ref(v_minor__type_2412_);
lean_dec_ref(v_fs_2411_);
lean_dec(v_rlvl_2410_);
lean_dec_ref(v_prods_2409_);
lean_dec_ref(v_arg__type_2408_);
lean_dec_ref(v_belows_2407_);
lean_dec_ref(v_motives_2405_);
v_a_2449_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2432_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2432_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
else
{
lean_object* v___x_2457_; 
lean_dec(v___x_2429_);
lean_dec_ref(v_x_2416_);
lean_dec_ref(v_arg__type_2408_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___x_2457_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2410_, v_motives_2405_, v_belows_2407_, v_fs_2411_, v_minor__type_2412_, v_prods_2409_, v_tail_2413_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; uint8_t v___x_2462_; uint8_t v___x_2463_; uint8_t v___x_2464_; lean_object* v___x_2465_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = lean_unsigned_to_nat(1u);
v___x_2460_ = lean_mk_empty_array_with_capacity(v___x_2459_);
v___x_2461_ = lean_array_push(v___x_2460_, v_head_2406_);
v___x_2462_ = 0;
v___x_2463_ = 1;
v___x_2464_ = 1;
v___x_2465_ = l_Lean_Meta_mkLambdaFVars(v___x_2461_, v_a_2458_, v___x_2462_, v___x_2463_, v___x_2462_, v___x_2463_, v___x_2464_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v___x_2461_);
return v___x_2465_;
}
else
{
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v_head_2406_);
return v___x_2457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2466_, lean_object* v_head_2467_, lean_object* v_belows_2468_, lean_object* v_prods_2469_, lean_object* v_rlvl_2470_, lean_object* v_fs_2471_, lean_object* v_minor__type_2472_, lean_object* v_tail_2473_, lean_object* v_arg__args_2474_, lean_object* v_arg__type_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_dummy_2481_; lean_object* v_nargs_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; 
v_dummy_2481_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2482_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2475_);
lean_inc(v_nargs_2482_);
v___x_2483_ = lean_mk_array(v_nargs_2482_, v_dummy_2481_);
v___x_2484_ = lean_unsigned_to_nat(1u);
v___x_2485_ = lean_nat_sub(v_nargs_2482_, v___x_2484_);
lean_dec(v_nargs_2482_);
lean_inc_ref(v_arg__type_2475_);
v___x_2486_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2466_, v_head_2467_, v_belows_2468_, v_arg__type_2475_, v_prods_2469_, v_rlvl_2470_, v_fs_2471_, v_minor__type_2472_, v_tail_2473_, v_arg__args_2474_, v_arg__type_2475_, v___x_2483_, v___x_2485_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2487_, lean_object* v_motives_2488_, lean_object* v_belows_2489_, lean_object* v_fs_2490_, lean_object* v_minor__type_2491_, lean_object* v_prods_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2487_, v_motives_2488_, v_belows_2489_, v_fs_2490_, v_minor__type_2491_, v_prods_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2500_ = _args[0];
lean_object* v_head_2501_ = _args[1];
lean_object* v_belows_2502_ = _args[2];
lean_object* v_arg__type_2503_ = _args[3];
lean_object* v_prods_2504_ = _args[4];
lean_object* v_rlvl_2505_ = _args[5];
lean_object* v_fs_2506_ = _args[6];
lean_object* v_minor__type_2507_ = _args[7];
lean_object* v_tail_2508_ = _args[8];
lean_object* v_arg__args_2509_ = _args[9];
lean_object* v_x_2510_ = _args[10];
lean_object* v_x_2511_ = _args[11];
lean_object* v_x_2512_ = _args[12];
lean_object* v___y_2513_ = _args[13];
lean_object* v___y_2514_ = _args[14];
lean_object* v___y_2515_ = _args[15];
lean_object* v___y_2516_ = _args[16];
lean_object* v___y_2517_ = _args[17];
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2500_, v_head_2501_, v_belows_2502_, v_arg__type_2503_, v_prods_2504_, v_rlvl_2505_, v_fs_2506_, v_minor__type_2507_, v_tail_2508_, v_arg__args_2509_, v_x_2510_, v_x_2511_, v_x_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec_ref(v_arg__args_2509_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2519_, lean_object* v_motives_2520_, lean_object* v_belows_2521_, lean_object* v_fs_2522_, lean_object* v_minor__args_2523_, lean_object* v_minor__type_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2531_ = lean_array_to_list(v_minor__args_2523_);
v___x_2532_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2519_, v_motives_2520_, v_belows_2521_, v_fs_2522_, v_minor__type_2524_, v___x_2530_, v___x_2531_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2533_, lean_object* v_motives_2534_, lean_object* v_belows_2535_, lean_object* v_fs_2536_, lean_object* v_minor__args_2537_, lean_object* v_minor__type_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2533_, v_motives_2534_, v_belows_2535_, v_fs_2536_, v_minor__args_2537_, v_minor__type_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2545_, lean_object* v_motives_2546_, lean_object* v_belows_2547_, lean_object* v_fs_2548_, lean_object* v_minorType_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v___f_2555_; uint8_t v___x_2556_; lean_object* v___x_2557_; 
v___f_2555_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2555_, 0, v_rlvl_2545_);
lean_closure_set(v___f_2555_, 1, v_motives_2546_);
lean_closure_set(v___f_2555_, 2, v_belows_2547_);
lean_closure_set(v___f_2555_, 3, v_fs_2548_);
v___x_2556_ = 0;
v___x_2557_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2549_, v___f_2555_, v___x_2556_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2558_, lean_object* v_motives_2559_, lean_object* v_belows_2560_, lean_object* v_fs_2561_, lean_object* v_minorType_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2558_, v_motives_2559_, v_belows_2560_, v_fs_2561_, v_minorType_2562_, v_a_2563_, v_a_2564_, v_a_2565_, v_a_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___f_2575_; lean_object* v___x_27632__overap_2576_; lean_object* v___x_2577_; 
v___f_2575_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27632__overap_2576_ = lean_panic_fn(v___f_2575_, v_msg_2569_);
v___x_2577_ = lean_apply_5(v___x_27632__overap_2576_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, lean_box(0));
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2585_, lean_object* v___y_2586_){
_start:
{
uint8_t v___x_2588_; 
v___x_2588_ = l_Lean_Expr_hasMVar(v_e_2585_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2589_, 0, v_e_2585_);
return v___x_2589_;
}
else
{
lean_object* v___x_2590_; lean_object* v_mctx_2591_; lean_object* v___x_2592_; lean_object* v_fst_2593_; lean_object* v_snd_2594_; lean_object* v___x_2595_; lean_object* v_cache_2596_; lean_object* v_zetaDeltaFVarIds_2597_; lean_object* v_postponed_2598_; lean_object* v_diag_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2608_; 
v___x_2590_ = lean_st_ref_get(v___y_2586_);
v_mctx_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc_ref(v_mctx_2591_);
lean_dec(v___x_2590_);
v___x_2592_ = l_Lean_instantiateMVarsCore(v_mctx_2591_, v_e_2585_);
v_fst_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_fst_2593_);
v_snd_2594_ = lean_ctor_get(v___x_2592_, 1);
lean_inc(v_snd_2594_);
lean_dec_ref(v___x_2592_);
v___x_2595_ = lean_st_ref_take(v___y_2586_);
v_cache_2596_ = lean_ctor_get(v___x_2595_, 1);
v_zetaDeltaFVarIds_2597_ = lean_ctor_get(v___x_2595_, 2);
v_postponed_2598_ = lean_ctor_get(v___x_2595_, 3);
v_diag_2599_ = lean_ctor_get(v___x_2595_, 4);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2608_ == 0)
{
lean_object* v_unused_2609_; 
v_unused_2609_ = lean_ctor_get(v___x_2595_, 0);
lean_dec(v_unused_2609_);
v___x_2601_ = v___x_2595_;
v_isShared_2602_ = v_isSharedCheck_2608_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_diag_2599_);
lean_inc(v_postponed_2598_);
lean_inc(v_zetaDeltaFVarIds_2597_);
lean_inc(v_cache_2596_);
lean_dec(v___x_2595_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2608_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 0, v_snd_2594_);
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_snd_2594_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v_cache_2596_);
lean_ctor_set(v_reuseFailAlloc_2607_, 2, v_zetaDeltaFVarIds_2597_);
lean_ctor_set(v_reuseFailAlloc_2607_, 3, v_postponed_2598_);
lean_ctor_set(v_reuseFailAlloc_2607_, 4, v_diag_2599_);
v___x_2604_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2605_ = lean_st_ref_set(v___y_2586_, v___x_2604_);
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v_fst_2593_);
return v___x_2606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2610_, v___y_2611_);
lean_dec(v___y_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2614_, v___y_2616_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; lean_object* v_env_2632_; lean_object* v_toConstantVal_2633_; lean_object* v_value_2634_; lean_object* v_all_2635_; uint8_t v___y_2637_; lean_object* v_type_2645_; uint8_t v___x_2646_; 
v___x_2631_ = lean_st_ref_get(v___y_2629_);
v_env_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc_ref(v_env_2632_);
lean_dec(v___x_2631_);
v_toConstantVal_2633_ = lean_ctor_get(v_thm_2628_, 0);
v_value_2634_ = lean_ctor_get(v_thm_2628_, 1);
v_all_2635_ = lean_ctor_get(v_thm_2628_, 2);
v_type_2645_ = lean_ctor_get(v_toConstantVal_2633_, 2);
lean_inc_ref(v_env_2632_);
v___x_2646_ = l_Lean_Environment_hasUnsafe(v_env_2632_, v_type_2645_);
if (v___x_2646_ == 0)
{
uint8_t v___x_2647_; 
v___x_2647_ = l_Lean_Environment_hasUnsafe(v_env_2632_, v_value_2634_);
v___y_2637_ = v___x_2647_;
goto v___jp_2636_;
}
else
{
lean_dec_ref(v_env_2632_);
v___y_2637_ = v___x_2646_;
goto v___jp_2636_;
}
v___jp_2636_:
{
if (v___y_2637_ == 0)
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2638_, 0, v_thm_2628_);
v___x_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2638_);
return v___x_2639_;
}
else
{
lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
lean_inc(v_all_2635_);
lean_inc_ref(v_value_2634_);
lean_inc_ref(v_toConstantVal_2633_);
lean_dec_ref(v_thm_2628_);
v___x_2640_ = lean_box(0);
v___x_2641_ = 0;
v___x_2642_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2642_, 0, v_toConstantVal_2633_);
lean_ctor_set(v___x_2642_, 1, v_value_2634_);
lean_ctor_set(v___x_2642_, 2, v___x_2640_);
lean_ctor_set(v___x_2642_, 3, v_all_2635_);
lean_ctor_set_uint8(v___x_2642_, sizeof(void*)*4, v___x_2641_);
v___x_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2648_, v___y_2649_);
lean_dec(v___y_2649_);
return v_res_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2652_, v___y_2656_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2667_, lean_object* v___x_2668_, lean_object* v___x_2669_, lean_object* v_all_2670_, lean_object* v___x_2671_, lean_object* v___x_2672_, lean_object* v_x_2673_){
_start:
{
lean_object* v___y_2675_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = lean_array_get_size(v_all_2670_);
v___x_2680_ = lean_nat_dec_lt(v_x_2673_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2681_ = lean_box(0);
v___x_2682_ = lean_array_get_borrowed(v___x_2681_, v_all_2670_, v___x_2671_);
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2684_ = lean_nat_sub(v_x_2673_, v___x_2679_);
v___x_2685_ = lean_nat_add(v___x_2684_, v___x_2672_);
lean_dec(v___x_2684_);
v___x_2686_ = l_Nat_reprFast(v___x_2685_);
v___x_2687_ = lean_string_append(v___x_2683_, v___x_2686_);
lean_dec_ref(v___x_2686_);
lean_inc(v___x_2682_);
v___x_2688_ = l_Lean_Name_str___override(v___x_2682_, v___x_2687_);
v___y_2675_ = v___x_2688_;
goto v___jp_2674_;
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_array_fget_borrowed(v_all_2670_, v_x_2673_);
lean_inc(v___x_2689_);
v___x_2690_ = l_Lean_mkBelowName(v___x_2689_);
v___y_2675_ = v___x_2690_;
goto v___jp_2674_;
}
v___jp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2676_ = l_Lean_Expr_const___override(v___y_2675_, v___x_2667_);
v___x_2677_ = l_Array_append___redArg(v___x_2668_, v___x_2669_);
v___x_2678_ = l_Lean_mkAppN(v___x_2676_, v___x_2677_);
lean_dec_ref(v___x_2677_);
return v___x_2678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2691_, lean_object* v___x_2692_, lean_object* v___x_2693_, lean_object* v_all_2694_, lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v_x_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2691_, v___x_2692_, v___x_2693_, v_all_2694_, v___x_2695_, v___x_2696_, v_x_2697_);
lean_dec(v_x_2697_);
lean_dec(v___x_2696_);
lean_dec(v___x_2695_);
lean_dec_ref(v_all_2694_);
lean_dec_ref(v___x_2693_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2699_, lean_object* v___x_2700_, uint8_t v___x_2701_, lean_object* v_targs_2702_, lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = l_Lean_mkAppN(v_a_2699_, v_targs_2702_);
v___x_2710_ = l_Lean_mkAppN(v___x_2700_, v_targs_2702_);
lean_inc(v___y_2707_);
lean_inc_ref(v___y_2706_);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
v___x_2711_ = l_Lean_Meta_mkPProd(v___x_2709_, v___x_2710_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; uint8_t v___x_2713_; uint8_t v___x_2714_; lean_object* v___x_2715_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref(v___x_2711_);
v___x_2713_ = 0;
v___x_2714_ = 1;
v___x_2715_ = l_Lean_Meta_mkLambdaFVars(v_targs_2702_, v_a_2712_, v___x_2713_, v___x_2701_, v___x_2713_, v___x_2701_, v___x_2714_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v___x_2715_;
}
else
{
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2716_, lean_object* v___x_2717_, lean_object* v___x_2718_, lean_object* v_targs_2719_, lean_object* v_x_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
uint8_t v___x_30831__boxed_2726_; lean_object* v_res_2727_; 
v___x_30831__boxed_2726_ = lean_unbox(v___x_2718_);
v_res_2727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2716_, v___x_2717_, v___x_30831__boxed_2726_, v_targs_2719_, v_x_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec_ref(v_x_2720_);
lean_dec_ref(v_targs_2719_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v_as_2728_, size_t v_sz_2729_, size_t v_i_2730_, lean_object* v_b_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_usize_dec_lt(v_i_2730_, v_sz_2729_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; 
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_b_2731_);
return v___x_2738_;
}
else
{
lean_object* v_snd_2739_; lean_object* v_fst_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2796_; 
v_snd_2739_ = lean_ctor_get(v_b_2731_, 1);
v_fst_2740_ = lean_ctor_get(v_b_2731_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_b_2731_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2742_ = v_b_2731_;
v_isShared_2743_ = v_isSharedCheck_2796_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_snd_2739_);
lean_inc(v_fst_2740_);
lean_dec(v_b_2731_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2796_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v_array_2744_; lean_object* v_start_2745_; lean_object* v_stop_2746_; uint8_t v___x_2747_; 
v_array_2744_ = lean_ctor_get(v_snd_2739_, 0);
v_start_2745_ = lean_ctor_get(v_snd_2739_, 1);
v_stop_2746_ = lean_ctor_get(v_snd_2739_, 2);
v___x_2747_ = lean_nat_dec_lt(v_start_2745_, v_stop_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2749_; 
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
if (v_isShared_2743_ == 0)
{
v___x_2749_ = v___x_2742_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_fst_2740_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_snd_2739_);
v___x_2749_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
return v___x_2750_;
}
}
else
{
lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2792_; 
lean_inc(v_stop_2746_);
lean_inc(v_start_2745_);
lean_inc_ref(v_array_2744_);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_snd_2739_);
if (v_isSharedCheck_2792_ == 0)
{
lean_object* v_unused_2793_; lean_object* v_unused_2794_; lean_object* v_unused_2795_; 
v_unused_2793_ = lean_ctor_get(v_snd_2739_, 2);
lean_dec(v_unused_2793_);
v_unused_2794_ = lean_ctor_get(v_snd_2739_, 1);
lean_dec(v_unused_2794_);
v_unused_2795_ = lean_ctor_get(v_snd_2739_, 0);
lean_dec(v_unused_2795_);
v___x_2753_ = v_snd_2739_;
v_isShared_2754_ = v_isSharedCheck_2792_;
goto v_resetjp_2752_;
}
else
{
lean_dec(v_snd_2739_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2792_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v_a_2755_; lean_object* v___x_2756_; 
v_a_2755_ = lean_array_uget_borrowed(v_as_2728_, v_i_2730_);
lean_inc(v___y_2735_);
lean_inc_ref(v___y_2734_);
lean_inc(v___y_2733_);
lean_inc_ref(v___y_2732_);
lean_inc(v_a_2755_);
v___x_2756_ = lean_infer_type(v_a_2755_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___f_2760_; uint8_t v___x_2761_; lean_object* v___x_2762_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
v___x_2758_ = lean_array_fget_borrowed(v_array_2744_, v_start_2745_);
v___x_2759_ = lean_box(v___x_2747_);
lean_inc(v___x_2758_);
lean_inc(v_a_2755_);
v___f_2760_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2760_, 0, v_a_2755_);
lean_closure_set(v___f_2760_, 1, v___x_2758_);
lean_closure_set(v___f_2760_, 2, v___x_2759_);
v___x_2761_ = 0;
lean_inc(v___y_2735_);
lean_inc_ref(v___y_2734_);
lean_inc(v___y_2733_);
lean_inc_ref(v___y_2732_);
v___x_2762_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2757_, v___f_2760_, v___x_2761_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = lean_unsigned_to_nat(1u);
v___x_2765_ = lean_nat_add(v_start_2745_, v___x_2764_);
lean_dec(v_start_2745_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 1, v___x_2765_);
v___x_2767_ = v___x_2753_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_array_2744_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v_stop_2746_);
v___x_2767_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2770_; 
v___x_2768_ = l_Lean_Expr_app___override(v_fst_2740_, v_a_2763_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 1, v___x_2767_);
lean_ctor_set(v___x_2742_, 0, v___x_2768_);
v___x_2770_ = v___x_2742_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2768_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2767_);
v___x_2770_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
size_t v___x_2771_; size_t v___x_2772_; 
v___x_2771_ = ((size_t)1ULL);
v___x_2772_ = lean_usize_add(v_i_2730_, v___x_2771_);
v_i_2730_ = v___x_2772_;
v_b_2731_ = v___x_2770_;
goto _start;
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_del_object(v___x_2753_);
lean_dec(v_stop_2746_);
lean_dec(v_start_2745_);
lean_dec_ref(v_array_2744_);
lean_del_object(v___x_2742_);
lean_dec(v_fst_2740_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
v_a_2776_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2762_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2762_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_del_object(v___x_2753_);
lean_dec(v_stop_2746_);
lean_dec(v_start_2745_);
lean_dec_ref(v_array_2744_);
lean_del_object(v___x_2742_);
lean_dec(v_fst_2740_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
v_a_2784_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2756_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2756_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v_as_2797_, lean_object* v_sz_2798_, lean_object* v_i_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
size_t v_sz_boxed_2806_; size_t v_i_boxed_2807_; lean_object* v_res_2808_; 
v_sz_boxed_2806_ = lean_unbox_usize(v_sz_2798_);
lean_dec(v_sz_2798_);
v_i_boxed_2807_ = lean_unbox_usize(v_i_2799_);
lean_dec(v_i_2799_);
v_res_2808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v_as_2797_, v_sz_boxed_2806_, v_i_boxed_2807_, v_b_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec_ref(v_as_2797_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2809_, size_t v_sz_2810_, size_t v_i_2811_, lean_object* v_b_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_usize_dec_lt(v_i_2811_, v_sz_2810_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; 
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v_b_2812_);
return v___x_2819_;
}
else
{
lean_object* v_a_2820_; lean_object* v_toInductionSubgoal_2821_; lean_object* v_mvarId_2822_; uint8_t v___x_2823_; lean_object* v___x_2824_; 
v_a_2820_ = lean_array_uget_borrowed(v_as_2809_, v_i_2811_);
v_toInductionSubgoal_2821_ = lean_ctor_get(v_a_2820_, 0);
v_mvarId_2822_ = lean_ctor_get(v_toInductionSubgoal_2821_, 0);
v___x_2823_ = 0;
lean_inc(v___y_2816_);
lean_inc_ref(v___y_2815_);
lean_inc(v___y_2814_);
lean_inc_ref(v___y_2813_);
lean_inc(v_mvarId_2822_);
v___x_2824_ = l_Lean_MVarId_refl(v_mvarId_2822_, v___x_2823_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v___x_2825_; size_t v___x_2826_; size_t v___x_2827_; 
lean_dec_ref(v___x_2824_);
v___x_2825_ = lean_box(0);
v___x_2826_ = ((size_t)1ULL);
v___x_2827_ = lean_usize_add(v_i_2811_, v___x_2826_);
v_i_2811_ = v___x_2827_;
v_b_2812_ = v___x_2825_;
goto _start;
}
else
{
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2829_, lean_object* v_sz_2830_, lean_object* v_i_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
size_t v_sz_boxed_2838_; size_t v_i_boxed_2839_; lean_object* v_res_2840_; 
v_sz_boxed_2838_ = lean_unbox_usize(v_sz_2830_);
lean_dec(v_sz_2830_);
v_i_boxed_2839_ = lean_unbox_usize(v_i_2831_);
lean_dec(v_i_2831_);
v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2829_, v_sz_boxed_2838_, v_i_boxed_2839_, v_b_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
lean_dec_ref(v_as_2829_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v_fs_2844_, lean_object* v_as_2845_, size_t v_sz_2846_, size_t v_i_2847_, lean_object* v_b_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2855_; 
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_fs_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v___x_2842_);
lean_dec(v___x_2841_);
v___x_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2855_, 0, v_b_2848_);
return v___x_2855_;
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_array_uget_borrowed(v_as_2845_, v_i_2847_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc(v_a_2856_);
v___x_2857_ = lean_infer_type(v_a_2856_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref(v___x_2857_);
lean_inc(v___y_2852_);
lean_inc_ref(v___y_2851_);
lean_inc(v___y_2850_);
lean_inc_ref(v___y_2849_);
lean_inc_ref(v_fs_2844_);
lean_inc_ref(v___x_2843_);
lean_inc_ref(v___x_2842_);
lean_inc(v___x_2841_);
v___x_2859_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2841_, v___x_2842_, v___x_2843_, v_fs_2844_, v_a_2858_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v_a_2860_; lean_object* v___x_2861_; size_t v___x_2862_; size_t v___x_2863_; 
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_a_2860_);
lean_dec_ref(v___x_2859_);
v___x_2861_ = l_Lean_Expr_app___override(v_b_2848_, v_a_2860_);
v___x_2862_ = ((size_t)1ULL);
v___x_2863_ = lean_usize_add(v_i_2847_, v___x_2862_);
v_i_2847_ = v___x_2863_;
v_b_2848_ = v___x_2861_;
goto _start;
}
else
{
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_b_2848_);
lean_dec_ref(v_fs_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v___x_2842_);
lean_dec(v___x_2841_);
return v___x_2859_;
}
}
else
{
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_b_2848_);
lean_dec_ref(v_fs_2844_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v___x_2842_);
lean_dec(v___x_2841_);
return v___x_2857_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v___x_2867_, lean_object* v_fs_2868_, lean_object* v_as_2869_, lean_object* v_sz_2870_, lean_object* v_i_2871_, lean_object* v_b_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
size_t v_sz_boxed_2878_; size_t v_i_boxed_2879_; lean_object* v_res_2880_; 
v_sz_boxed_2878_ = lean_unbox_usize(v_sz_2870_);
lean_dec(v_sz_2870_);
v_i_boxed_2879_ = lean_unbox_usize(v_i_2871_);
lean_dec(v_i_2871_);
v_res_2880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2865_, v___x_2866_, v___x_2867_, v_fs_2868_, v_as_2869_, v_sz_boxed_2878_, v_i_boxed_2879_, v_b_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
lean_dec_ref(v_as_2869_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2881_, lean_object* v_tail_2882_, lean_object* v_recName_2883_, lean_object* v___x_2884_, lean_object* v___x_2885_, lean_object* v___x_2886_, size_t v_sz_2887_, size_t v___x_2888_, lean_object* v___x_2889_, lean_object* v___x_2890_, lean_object* v___x_2891_, lean_object* v___x_2892_, lean_object* v___x_2893_, lean_object* v___x_2894_, lean_object* v_val_2895_, uint8_t v___x_2896_, lean_object* v_brecOnGoName_2897_, lean_object* v_levelParams_2898_, lean_object* v___x_2899_, lean_object* v_brecOnName_2900_, lean_object* v___x_2901_, lean_object* v_brecOnEqName_2902_, lean_object* v_fs_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_){
_start:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_inc(v___x_2881_);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2881_);
lean_ctor_set(v___x_2909_, 1, v_tail_2882_);
v___x_2910_ = l_Lean_Expr_const___override(v_recName_2883_, v___x_2909_);
v___x_2911_ = l_Lean_mkAppN(v___x_2910_, v___x_2884_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___x_2885_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
v___x_2913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2886_, v_sz_2887_, v___x_2888_, v___x_2912_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v_fst_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_3276_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref(v___x_2913_);
v_fst_2915_ = lean_ctor_get(v_a_2914_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v_a_2914_);
if (v_isSharedCheck_3276_ == 0)
{
lean_object* v_unused_3277_; 
v_unused_3277_ = lean_ctor_get(v_a_2914_, 1);
lean_dec(v_unused_3277_);
v___x_2917_ = v_a_2914_;
v_isShared_2918_ = v_isSharedCheck_3276_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_fst_2915_);
lean_dec(v_a_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_3276_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
size_t v_sz_2919_; lean_object* v___x_2920_; 
v_sz_2919_ = lean_array_size(v___x_2889_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
lean_inc_ref(v_fs_2903_);
lean_inc_ref(v___x_2890_);
lean_inc_ref(v___x_2886_);
v___x_2920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2881_, v___x_2886_, v___x_2890_, v_fs_2903_, v___x_2889_, v_sz_2919_, v___x_2888_, v_fst_2915_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
v___x_2922_ = l_Lean_mkAppN(v_a_2921_, v___x_2891_);
lean_inc_ref(v___x_2892_);
v___x_2923_ = l_Lean_Expr_app___override(v___x_2922_, v___x_2892_);
v___x_2924_ = l_Array_append___redArg(v___x_2884_, v___x_2886_);
v___x_2925_ = l_Array_append___redArg(v___x_2924_, v___x_2891_);
v___x_2926_ = lean_mk_empty_array_with_capacity(v___x_2893_);
lean_inc_ref(v___x_2892_);
v___x_2927_ = lean_array_push(v___x_2926_, v___x_2892_);
lean_inc_ref(v___x_2894_);
v___x_2928_ = lean_array_get(v___x_2894_, v___x_2886_, v_val_2895_);
lean_dec_ref(v___x_2886_);
lean_inc_ref(v___x_2892_);
v___x_2929_ = lean_array_push(v___x_2891_, v___x_2892_);
v___x_2930_ = l_Lean_mkAppN(v___x_2928_, v___x_2929_);
lean_inc_ref(v___x_2894_);
v___x_2931_ = lean_array_get(v___x_2894_, v___x_2890_, v_val_2895_);
lean_dec_ref(v___x_2890_);
v___x_2932_ = l_Lean_mkAppN(v___x_2931_, v___x_2929_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
lean_inc_ref(v___x_2930_);
v___x_2933_ = l_Lean_Meta_mkPProd(v___x_2930_, v___x_2932_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; uint8_t v___x_2937_; uint8_t v___x_2938_; lean_object* v___x_2939_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref(v___x_2933_);
v___x_2935_ = l_Array_append___redArg(v___x_2925_, v___x_2927_);
lean_dec_ref(v___x_2927_);
v___x_2936_ = l_Array_append___redArg(v___x_2935_, v_fs_2903_);
v___x_2937_ = 0;
v___x_2938_ = 1;
v___x_2939_ = l_Lean_Meta_mkForallFVars(v___x_2936_, v_a_2934_, v___x_2937_, v___x_2896_, v___x_2896_, v___x_2938_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v___x_2941_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref(v___x_2939_);
v___x_2941_ = l_Lean_Meta_mkLambdaFVars(v___x_2936_, v___x_2923_, v___x_2937_, v___x_2896_, v___x_2937_, v___x_2896_, v___x_2938_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_object* v_a_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_3243_; 
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = lean_box(1);
lean_inc(v_levelParams_2898_);
lean_inc(v_brecOnGoName_2897_);
v___x_2944_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2897_, v_levelParams_2898_, v_a_2940_, v_a_2942_, v___x_2943_, v___y_2907_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_3243_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_3243_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
lean_inc(v_a_2945_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set_tag(v___x_2947_, 1);
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_3242_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; 
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
v___x_2951_ = l_Lean_addDecl(v___x_2950_, v___x_2937_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_toConstantVal_2952_; lean_object* v_name_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___x_2951_);
v_toConstantVal_2952_ = lean_ctor_get(v_a_2945_, 0);
lean_inc_ref(v_toConstantVal_2952_);
lean_dec(v_a_2945_);
v_name_2953_ = lean_ctor_get(v_toConstantVal_2952_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_toConstantVal_2952_);
if (v_isSharedCheck_3239_ == 0)
{
lean_object* v_unused_3240_; lean_object* v_unused_3241_; 
v_unused_3240_ = lean_ctor_get(v_toConstantVal_2952_, 2);
lean_dec(v_unused_3240_);
v_unused_3241_ = lean_ctor_get(v_toConstantVal_2952_, 1);
lean_dec(v_unused_3241_);
v___x_2955_ = v_toConstantVal_2952_;
v_isShared_2956_ = v_isSharedCheck_3239_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_name_2953_);
lean_dec(v_toConstantVal_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_3239_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v_env_2959_; lean_object* v_nextMacroScope_2960_; lean_object* v_ngen_2961_; lean_object* v_auxDeclNGen_2962_; lean_object* v_traceState_2963_; lean_object* v_messages_2964_; lean_object* v_infoState_2965_; lean_object* v_snapshotTasks_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_3237_; 
lean_inc(v_name_2953_);
v___x_2957_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2953_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec_ref(v___x_2957_);
v___x_2958_ = lean_st_ref_take(v___y_2907_);
v_env_2959_ = lean_ctor_get(v___x_2958_, 0);
v_nextMacroScope_2960_ = lean_ctor_get(v___x_2958_, 1);
v_ngen_2961_ = lean_ctor_get(v___x_2958_, 2);
v_auxDeclNGen_2962_ = lean_ctor_get(v___x_2958_, 3);
v_traceState_2963_ = lean_ctor_get(v___x_2958_, 4);
v_messages_2964_ = lean_ctor_get(v___x_2958_, 6);
v_infoState_2965_ = lean_ctor_get(v___x_2958_, 7);
v_snapshotTasks_2966_ = lean_ctor_get(v___x_2958_, 8);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; 
v_unused_3238_ = lean_ctor_get(v___x_2958_, 5);
lean_dec(v_unused_3238_);
v___x_2968_ = v___x_2958_;
v_isShared_2969_ = v_isSharedCheck_3237_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_snapshotTasks_2966_);
lean_inc(v_infoState_2965_);
lean_inc(v_messages_2964_);
lean_inc(v_traceState_2963_);
lean_inc(v_auxDeclNGen_2962_);
lean_inc(v_ngen_2961_);
lean_inc(v_nextMacroScope_2960_);
lean_inc(v_env_2959_);
lean_dec(v___x_2958_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_3237_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2970_ = l_Lean_addProtected(v_env_2959_, v_name_2953_);
v___x_2971_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 5, v___x_2971_);
lean_ctor_set(v___x_2968_, 0, v___x_2970_);
v___x_2973_ = v___x_2968_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v_nextMacroScope_2960_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_ngen_2961_);
lean_ctor_set(v_reuseFailAlloc_3236_, 3, v_auxDeclNGen_2962_);
lean_ctor_set(v_reuseFailAlloc_3236_, 4, v_traceState_2963_);
lean_ctor_set(v_reuseFailAlloc_3236_, 5, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3236_, 6, v_messages_2964_);
lean_ctor_set(v_reuseFailAlloc_3236_, 7, v_infoState_2965_);
lean_ctor_set(v_reuseFailAlloc_3236_, 8, v_snapshotTasks_2966_);
v___x_2973_ = v_reuseFailAlloc_3236_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v_mctx_2976_; lean_object* v_zetaDeltaFVarIds_2977_; lean_object* v_postponed_2978_; lean_object* v_diag_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3234_; 
v___x_2974_ = lean_st_ref_set(v___y_2907_, v___x_2973_);
v___x_2975_ = lean_st_ref_take(v___y_2905_);
v_mctx_2976_ = lean_ctor_get(v___x_2975_, 0);
v_zetaDeltaFVarIds_2977_ = lean_ctor_get(v___x_2975_, 2);
v_postponed_2978_ = lean_ctor_get(v___x_2975_, 3);
v_diag_2979_ = lean_ctor_get(v___x_2975_, 4);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3234_ == 0)
{
lean_object* v_unused_3235_; 
v_unused_3235_ = lean_ctor_get(v___x_2975_, 1);
lean_dec(v_unused_3235_);
v___x_2981_ = v___x_2975_;
v_isShared_2982_ = v_isSharedCheck_3234_;
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
v_isShared_2982_ = v_isSharedCheck_3234_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 1, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_mctx_2976_);
lean_ctor_set(v_reuseFailAlloc_3233_, 1, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3233_, 2, v_zetaDeltaFVarIds_2977_);
lean_ctor_set(v_reuseFailAlloc_3233_, 3, v_postponed_2978_);
lean_ctor_set(v_reuseFailAlloc_3233_, 4, v_diag_2979_);
v___x_2985_ = v_reuseFailAlloc_3233_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2986_ = lean_st_ref_set(v___y_2905_, v___x_2985_);
lean_inc(v___x_2899_);
v___x_2987_ = l_Lean_Expr_const___override(v_brecOnGoName_2897_, v___x_2899_);
v___x_2988_ = l_Lean_mkAppN(v___x_2987_, v___x_2936_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
lean_inc_ref(v___x_2988_);
v___x_2989_ = l_Lean_Meta_mkPProdFstM(v___x_2988_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref(v___x_2989_);
v___x_2991_ = l_Lean_Meta_mkLambdaFVars(v___x_2936_, v_a_2990_, v___x_2937_, v___x_2896_, v___x_2937_, v___x_2896_, v___x_2938_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; lean_object* v___x_2993_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref(v___x_2991_);
v___x_2993_ = l_Lean_Meta_mkForallFVars(v___x_2936_, v___x_2930_, v___x_2937_, v___x_2896_, v___x_2896_, v___x_2938_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3208_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref(v___x_2993_);
lean_inc(v_levelParams_2898_);
v___x_2995_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2900_, v_levelParams_2898_, v_a_2994_, v_a_2992_, v___x_2943_, v___y_2907_);
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3208_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3208_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
lean_inc(v_a_2996_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 1);
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; 
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
v___x_3002_ = l_Lean_addDecl(v___x_3001_, v___x_2937_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_toConstantVal_3003_; lean_object* v_name_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3204_; 
lean_dec_ref(v___x_3002_);
v_toConstantVal_3003_ = lean_ctor_get(v_a_2996_, 0);
lean_inc_ref(v_toConstantVal_3003_);
lean_dec(v_a_2996_);
v_name_3004_ = lean_ctor_get(v_toConstantVal_3003_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_toConstantVal_3003_);
if (v_isSharedCheck_3204_ == 0)
{
lean_object* v_unused_3205_; lean_object* v_unused_3206_; 
v_unused_3205_ = lean_ctor_get(v_toConstantVal_3003_, 2);
lean_dec(v_unused_3205_);
v_unused_3206_ = lean_ctor_get(v_toConstantVal_3003_, 1);
lean_dec(v_unused_3206_);
v___x_3006_ = v_toConstantVal_3003_;
v_isShared_3007_ = v_isSharedCheck_3204_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_name_3004_);
lean_dec(v_toConstantVal_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3204_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v_env_3010_; lean_object* v_nextMacroScope_3011_; lean_object* v_ngen_3012_; lean_object* v_auxDeclNGen_3013_; lean_object* v_traceState_3014_; lean_object* v_messages_3015_; lean_object* v_infoState_3016_; lean_object* v_snapshotTasks_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3202_; 
lean_inc(v_name_3004_);
v___x_3008_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_3004_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec_ref(v___x_3008_);
v___x_3009_ = lean_st_ref_take(v___y_2907_);
v_env_3010_ = lean_ctor_get(v___x_3009_, 0);
v_nextMacroScope_3011_ = lean_ctor_get(v___x_3009_, 1);
v_ngen_3012_ = lean_ctor_get(v___x_3009_, 2);
v_auxDeclNGen_3013_ = lean_ctor_get(v___x_3009_, 3);
v_traceState_3014_ = lean_ctor_get(v___x_3009_, 4);
v_messages_3015_ = lean_ctor_get(v___x_3009_, 6);
v_infoState_3016_ = lean_ctor_get(v___x_3009_, 7);
v_snapshotTasks_3017_ = lean_ctor_get(v___x_3009_, 8);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3202_ == 0)
{
lean_object* v_unused_3203_; 
v_unused_3203_ = lean_ctor_get(v___x_3009_, 5);
lean_dec(v_unused_3203_);
v___x_3019_ = v___x_3009_;
v_isShared_3020_ = v_isSharedCheck_3202_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_snapshotTasks_3017_);
lean_inc(v_infoState_3016_);
lean_inc(v_messages_3015_);
lean_inc(v_traceState_3014_);
lean_inc(v_auxDeclNGen_3013_);
lean_inc(v_ngen_3012_);
lean_inc(v_nextMacroScope_3011_);
lean_inc(v_env_3010_);
lean_dec(v___x_3009_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3202_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3023_; 
lean_inc(v_name_3004_);
v___x_3021_ = l_Lean_markAuxRecursor(v_env_3010_, v_name_3004_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 5, v___x_2971_);
lean_ctor_set(v___x_3019_, 0, v___x_3021_);
v___x_3023_ = v___x_3019_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_nextMacroScope_3011_);
lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_ngen_3012_);
lean_ctor_set(v_reuseFailAlloc_3201_, 3, v_auxDeclNGen_3013_);
lean_ctor_set(v_reuseFailAlloc_3201_, 4, v_traceState_3014_);
lean_ctor_set(v_reuseFailAlloc_3201_, 5, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3201_, 6, v_messages_3015_);
lean_ctor_set(v_reuseFailAlloc_3201_, 7, v_infoState_3016_);
lean_ctor_set(v_reuseFailAlloc_3201_, 8, v_snapshotTasks_3017_);
v___x_3023_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v_mctx_3026_; lean_object* v_zetaDeltaFVarIds_3027_; lean_object* v_postponed_3028_; lean_object* v_diag_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3199_; 
v___x_3024_ = lean_st_ref_set(v___y_2907_, v___x_3023_);
v___x_3025_ = lean_st_ref_take(v___y_2905_);
v_mctx_3026_ = lean_ctor_get(v___x_3025_, 0);
v_zetaDeltaFVarIds_3027_ = lean_ctor_get(v___x_3025_, 2);
v_postponed_3028_ = lean_ctor_get(v___x_3025_, 3);
v_diag_3029_ = lean_ctor_get(v___x_3025_, 4);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___x_3025_, 1);
lean_dec(v_unused_3200_);
v___x_3031_ = v___x_3025_;
v_isShared_3032_ = v_isSharedCheck_3199_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_diag_3029_);
lean_inc(v_postponed_3028_);
lean_inc(v_zetaDeltaFVarIds_3027_);
lean_inc(v_mctx_3026_);
lean_dec(v___x_3025_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3199_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 1, v___x_2983_);
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_mctx_3026_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_zetaDeltaFVarIds_3027_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_postponed_3028_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_diag_3029_);
v___x_3034_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v_env_3037_; lean_object* v_nextMacroScope_3038_; lean_object* v_ngen_3039_; lean_object* v_auxDeclNGen_3040_; lean_object* v_traceState_3041_; lean_object* v_messages_3042_; lean_object* v_infoState_3043_; lean_object* v_snapshotTasks_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3196_; 
v___x_3035_ = lean_st_ref_set(v___y_2905_, v___x_3034_);
v___x_3036_ = lean_st_ref_take(v___y_2907_);
v_env_3037_ = lean_ctor_get(v___x_3036_, 0);
v_nextMacroScope_3038_ = lean_ctor_get(v___x_3036_, 1);
v_ngen_3039_ = lean_ctor_get(v___x_3036_, 2);
v_auxDeclNGen_3040_ = lean_ctor_get(v___x_3036_, 3);
v_traceState_3041_ = lean_ctor_get(v___x_3036_, 4);
v_messages_3042_ = lean_ctor_get(v___x_3036_, 6);
v_infoState_3043_ = lean_ctor_get(v___x_3036_, 7);
v_snapshotTasks_3044_ = lean_ctor_get(v___x_3036_, 8);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v___x_3036_, 5);
lean_dec(v_unused_3197_);
v___x_3046_ = v___x_3036_;
v_isShared_3047_ = v_isSharedCheck_3196_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_snapshotTasks_3044_);
lean_inc(v_infoState_3043_);
lean_inc(v_messages_3042_);
lean_inc(v_traceState_3041_);
lean_inc(v_auxDeclNGen_3040_);
lean_inc(v_ngen_3039_);
lean_inc(v_nextMacroScope_3038_);
lean_inc(v_env_3037_);
lean_dec(v___x_3036_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3196_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_inc(v_name_3004_);
v___x_3048_ = l_Lean_addProtected(v_env_3037_, v_name_3004_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 5, v___x_2971_);
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3050_ = v___x_3046_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_nextMacroScope_3038_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_ngen_3039_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_auxDeclNGen_3040_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_traceState_3041_);
lean_ctor_set(v_reuseFailAlloc_3195_, 5, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3195_, 6, v_messages_3042_);
lean_ctor_set(v_reuseFailAlloc_3195_, 7, v_infoState_3043_);
lean_ctor_set(v_reuseFailAlloc_3195_, 8, v_snapshotTasks_3044_);
v___x_3050_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v_mctx_3053_; lean_object* v_zetaDeltaFVarIds_3054_; lean_object* v_postponed_3055_; lean_object* v_diag_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3193_; 
v___x_3051_ = lean_st_ref_set(v___y_2907_, v___x_3050_);
v___x_3052_ = lean_st_ref_take(v___y_2905_);
v_mctx_3053_ = lean_ctor_get(v___x_3052_, 0);
v_zetaDeltaFVarIds_3054_ = lean_ctor_get(v___x_3052_, 2);
v_postponed_3055_ = lean_ctor_get(v___x_3052_, 3);
v_diag_3056_ = lean_ctor_get(v___x_3052_, 4);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v___x_3052_, 1);
lean_dec(v_unused_3194_);
v___x_3058_ = v___x_3052_;
v_isShared_3059_ = v_isSharedCheck_3193_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_diag_3056_);
lean_inc(v_postponed_3055_);
lean_inc(v_zetaDeltaFVarIds_3054_);
lean_inc(v_mctx_3053_);
lean_dec(v___x_3052_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3193_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v___x_2983_);
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_mctx_3053_);
lean_ctor_set(v_reuseFailAlloc_3192_, 1, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3192_, 2, v_zetaDeltaFVarIds_3054_);
lean_ctor_set(v_reuseFailAlloc_3192_, 3, v_postponed_3055_);
lean_ctor_set(v_reuseFailAlloc_3192_, 4, v_diag_3056_);
v___x_3061_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3062_ = lean_st_ref_set(v___y_2905_, v___x_3061_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
v___x_3063_ = l_Lean_Meta_mkPProdSndM(v___x_2988_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_3063_) == 0)
{
lean_object* v_a_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_a_3064_ = lean_ctor_get(v___x_3063_, 0);
lean_inc(v_a_3064_);
lean_dec_ref(v___x_3063_);
v___x_3065_ = l_Lean_Expr_const___override(v_name_3004_, v___x_2899_);
v___x_3066_ = l_Lean_mkAppN(v___x_3065_, v___x_2936_);
v___x_3067_ = lean_array_get(v___x_2894_, v_fs_2903_, v_val_2895_);
lean_dec_ref(v_fs_2903_);
v___x_3068_ = l_Lean_mkAppN(v___x_3067_, v___x_2929_);
lean_dec_ref(v___x_2929_);
v___x_3069_ = l_Lean_Expr_app___override(v___x_3068_, v_a_3064_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
v___x_3070_ = l_Lean_Meta_mkEq(v___x_3066_, v___x_3069_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref(v___x_3070_);
v___x_3072_ = lean_box(0);
lean_inc_ref(v___y_2904_);
lean_inc(v_a_3071_);
v___x_3073_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3071_, v___x_3072_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref(v___x_3073_);
v___x_3075_ = l_Lean_Expr_mvarId_x21(v_a_3074_);
v___x_3076_ = l_Lean_Expr_fvarId_x21(v___x_2892_);
lean_dec_ref(v___x_2892_);
v___x_3077_ = lean_mk_empty_array_with_capacity(v___x_2901_);
v___x_3078_ = lean_box(0);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
v___x_3079_ = l_Lean_MVarId_cases(v___x_3075_, v___x_3076_, v___x_3077_, v___x_2937_, v___x_3078_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; size_t v_sz_3082_; lean_object* v___x_3083_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref(v___x_3079_);
v___x_3081_ = lean_box(0);
v_sz_3082_ = lean_array_size(v_a_3080_);
lean_inc(v___y_2907_);
lean_inc_ref(v___y_2906_);
lean_inc(v___y_2905_);
lean_inc_ref(v___y_2904_);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3080_, v_sz_3082_, v___x_2888_, v___x_3081_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec(v_a_3080_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v___x_3084_; lean_object* v_a_3085_; lean_object* v___x_3086_; 
lean_dec_ref(v___x_3083_);
v___x_3084_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_3074_, v___y_2905_);
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref(v___x_3084_);
v___x_3086_ = l_Lean_Meta_mkForallFVars(v___x_2936_, v_a_3071_, v___x_2937_, v___x_2896_, v___x_2896_, v___x_2938_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref(v___x_3086_);
v___x_3088_ = l_Lean_Meta_mkLambdaFVars(v___x_2936_, v_a_3085_, v___x_2937_, v___x_2896_, v___x_2937_, v___x_2896_, v___x_2938_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v___x_2936_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref(v___x_3088_);
lean_inc(v_brecOnEqName_2902_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 2, v_a_3087_);
lean_ctor_set(v___x_3006_, 1, v_levelParams_2898_);
lean_ctor_set(v___x_3006_, 0, v_brecOnEqName_2902_);
v___x_3091_ = v___x_3006_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_brecOnEqName_2902_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_levelParams_2898_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_a_3087_);
v___x_3091_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3092_; lean_object* v___x_3094_; 
v___x_3092_ = lean_box(0);
lean_inc(v_brecOnEqName_2902_);
if (v_isShared_2918_ == 0)
{
lean_ctor_set_tag(v___x_2917_, 1);
lean_ctor_set(v___x_2917_, 1, v___x_3092_);
lean_ctor_set(v___x_2917_, 0, v_brecOnEqName_2902_);
v___x_3094_ = v___x_2917_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_brecOnEqName_2902_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
lean_object* v___x_3096_; 
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 2, v___x_3094_);
lean_ctor_set(v___x_2955_, 1, v_a_3089_);
lean_ctor_set(v___x_2955_, 0, v___x_3091_);
v___x_3096_ = v___x_2955_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_a_3089_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3097_; lean_object* v_a_3098_; lean_object* v___x_3099_; 
v___x_3097_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3096_, v___y_2907_);
v_a_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_a_3098_);
lean_dec_ref(v___x_3097_);
lean_inc(v___y_2907_);
v___x_3099_ = l_Lean_addDecl(v_a_3098_, v___x_2937_, v___y_2906_, v___y_2907_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3139_; 
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v___x_3099_, 0);
lean_dec(v_unused_3140_);
v___x_3101_ = v___x_3099_;
v_isShared_3102_ = v_isSharedCheck_3139_;
goto v_resetjp_3100_;
}
else
{
lean_dec(v___x_3099_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3139_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v_env_3104_; lean_object* v_nextMacroScope_3105_; lean_object* v_ngen_3106_; lean_object* v_auxDeclNGen_3107_; lean_object* v_traceState_3108_; lean_object* v_messages_3109_; lean_object* v_infoState_3110_; lean_object* v_snapshotTasks_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3137_; 
v___x_3103_ = lean_st_ref_take(v___y_2907_);
v_env_3104_ = lean_ctor_get(v___x_3103_, 0);
v_nextMacroScope_3105_ = lean_ctor_get(v___x_3103_, 1);
v_ngen_3106_ = lean_ctor_get(v___x_3103_, 2);
v_auxDeclNGen_3107_ = lean_ctor_get(v___x_3103_, 3);
v_traceState_3108_ = lean_ctor_get(v___x_3103_, 4);
v_messages_3109_ = lean_ctor_get(v___x_3103_, 6);
v_infoState_3110_ = lean_ctor_get(v___x_3103_, 7);
v_snapshotTasks_3111_ = lean_ctor_get(v___x_3103_, 8);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; 
v_unused_3138_ = lean_ctor_get(v___x_3103_, 5);
lean_dec(v_unused_3138_);
v___x_3113_ = v___x_3103_;
v_isShared_3114_ = v_isSharedCheck_3137_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_snapshotTasks_3111_);
lean_inc(v_infoState_3110_);
lean_inc(v_messages_3109_);
lean_inc(v_traceState_3108_);
lean_inc(v_auxDeclNGen_3107_);
lean_inc(v_ngen_3106_);
lean_inc(v_nextMacroScope_3105_);
lean_inc(v_env_3104_);
lean_dec(v___x_3103_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3137_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = l_Lean_addProtected(v_env_3104_, v_brecOnEqName_2902_);
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 5, v___x_2971_);
lean_ctor_set(v___x_3113_, 0, v___x_3115_);
v___x_3117_ = v___x_3113_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_nextMacroScope_3105_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_ngen_3106_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_auxDeclNGen_3107_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v_traceState_3108_);
lean_ctor_set(v_reuseFailAlloc_3136_, 5, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3136_, 6, v_messages_3109_);
lean_ctor_set(v_reuseFailAlloc_3136_, 7, v_infoState_3110_);
lean_ctor_set(v_reuseFailAlloc_3136_, 8, v_snapshotTasks_3111_);
v___x_3117_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v_mctx_3120_; lean_object* v_zetaDeltaFVarIds_3121_; lean_object* v_postponed_3122_; lean_object* v_diag_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3134_; 
v___x_3118_ = lean_st_ref_set(v___y_2907_, v___x_3117_);
lean_dec(v___y_2907_);
v___x_3119_ = lean_st_ref_take(v___y_2905_);
v_mctx_3120_ = lean_ctor_get(v___x_3119_, 0);
v_zetaDeltaFVarIds_3121_ = lean_ctor_get(v___x_3119_, 2);
v_postponed_3122_ = lean_ctor_get(v___x_3119_, 3);
v_diag_3123_ = lean_ctor_get(v___x_3119_, 4);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3134_ == 0)
{
lean_object* v_unused_3135_; 
v_unused_3135_ = lean_ctor_get(v___x_3119_, 1);
lean_dec(v_unused_3135_);
v___x_3125_ = v___x_3119_;
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_diag_3123_);
lean_inc(v_postponed_3122_);
lean_inc(v_zetaDeltaFVarIds_3121_);
lean_inc(v_mctx_3120_);
lean_dec(v___x_3119_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3134_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set(v___x_3125_, 1, v___x_2983_);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_mctx_3120_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v___x_2983_);
lean_ctor_set(v_reuseFailAlloc_3133_, 2, v_zetaDeltaFVarIds_3121_);
lean_ctor_set(v_reuseFailAlloc_3133_, 3, v_postponed_3122_);
lean_ctor_set(v_reuseFailAlloc_3133_, 4, v_diag_3123_);
v___x_3128_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3129_ = lean_st_ref_set(v___y_2905_, v___x_3128_);
lean_dec(v___y_2905_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v___x_3081_);
v___x_3131_ = v___x_3101_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v___x_3081_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
}
}
else
{
lean_dec(v___y_2907_);
lean_dec(v___y_2905_);
lean_dec(v_brecOnEqName_2902_);
return v___x_3099_;
}
}
}
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3087_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_2955_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_levelParams_2898_);
v_a_3144_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3088_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3088_);
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
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_a_3085_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_levelParams_2898_);
v_a_3152_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3086_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3086_);
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
lean_dec(v_a_3074_);
lean_dec(v_a_3071_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_levelParams_2898_);
return v___x_3083_;
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_a_3074_);
lean_dec(v_a_3071_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_levelParams_2898_);
v_a_3160_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3079_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3079_);
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
lean_dec(v_a_3071_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_levelParams_2898_);
lean_dec_ref(v___x_2892_);
v_a_3168_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3073_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3073_);
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
lean_del_object(v___x_3006_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_levelParams_2898_);
lean_dec_ref(v___x_2892_);
v_a_3176_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3070_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3070_);
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
lean_del_object(v___x_3006_);
lean_dec(v_name_3004_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
v_a_3184_ = lean_ctor_get(v___x_3063_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3063_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3063_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3063_);
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
lean_dec(v_a_2996_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
return v___x_3002_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec(v_a_2992_);
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
v_a_3209_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_2993_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_2993_);
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
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
v_a_3217_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_2991_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_2991_);
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
else
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3232_; 
lean_dec_ref(v___x_2988_);
lean_del_object(v___x_2955_);
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
v_a_3225_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3232_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3232_ == 0)
{
v___x_3227_ = v___x_2989_;
v_isShared_3228_ = v_isSharedCheck_3232_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___x_2989_);
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
}
}
}
}
else
{
lean_dec(v_a_2945_);
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec(v_brecOnGoName_2897_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_a_2940_);
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v___x_2929_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec(v_brecOnGoName_2897_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
v_a_3244_ = lean_ctor_get(v___x_2941_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_2941_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_2941_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_2941_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec_ref(v___x_2936_);
lean_dec_ref(v___x_2930_);
lean_dec_ref(v___x_2929_);
lean_dec_ref(v___x_2923_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec(v_brecOnGoName_2897_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
v_a_3252_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_2939_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_2939_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec_ref(v___x_2930_);
lean_dec_ref(v___x_2929_);
lean_dec_ref(v___x_2927_);
lean_dec_ref(v___x_2925_);
lean_dec_ref(v___x_2923_);
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec(v_brecOnGoName_2897_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
v_a_3260_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_2933_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_2933_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_del_object(v___x_2917_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec(v_brecOnGoName_2897_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2884_);
v_a_3268_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_2920_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_2920_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
}
else
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3285_; 
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec_ref(v_fs_2903_);
lean_dec(v_brecOnEqName_2902_);
lean_dec(v_brecOnName_2900_);
lean_dec(v___x_2899_);
lean_dec(v_levelParams_2898_);
lean_dec(v_brecOnGoName_2897_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2892_);
lean_dec_ref(v___x_2891_);
lean_dec_ref(v___x_2890_);
lean_dec_ref(v___x_2886_);
lean_dec_ref(v___x_2884_);
lean_dec(v___x_2881_);
v_a_3278_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3280_ = v___x_2913_;
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_2913_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3285_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3283_; 
if (v_isShared_3281_ == 0)
{
v___x_3283_ = v___x_3280_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v_a_3278_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3286_ = _args[0];
lean_object* v_tail_3287_ = _args[1];
lean_object* v_recName_3288_ = _args[2];
lean_object* v___x_3289_ = _args[3];
lean_object* v___x_3290_ = _args[4];
lean_object* v___x_3291_ = _args[5];
lean_object* v_sz_3292_ = _args[6];
lean_object* v___x_3293_ = _args[7];
lean_object* v___x_3294_ = _args[8];
lean_object* v___x_3295_ = _args[9];
lean_object* v___x_3296_ = _args[10];
lean_object* v___x_3297_ = _args[11];
lean_object* v___x_3298_ = _args[12];
lean_object* v___x_3299_ = _args[13];
lean_object* v_val_3300_ = _args[14];
lean_object* v___x_3301_ = _args[15];
lean_object* v_brecOnGoName_3302_ = _args[16];
lean_object* v_levelParams_3303_ = _args[17];
lean_object* v___x_3304_ = _args[18];
lean_object* v_brecOnName_3305_ = _args[19];
lean_object* v___x_3306_ = _args[20];
lean_object* v_brecOnEqName_3307_ = _args[21];
lean_object* v_fs_3308_ = _args[22];
lean_object* v___y_3309_ = _args[23];
lean_object* v___y_3310_ = _args[24];
lean_object* v___y_3311_ = _args[25];
lean_object* v___y_3312_ = _args[26];
lean_object* v___y_3313_ = _args[27];
_start:
{
size_t v_sz_boxed_3314_; size_t v___x_31089__boxed_3315_; uint8_t v___x_31097__boxed_3316_; lean_object* v_res_3317_; 
v_sz_boxed_3314_ = lean_unbox_usize(v_sz_3292_);
lean_dec(v_sz_3292_);
v___x_31089__boxed_3315_ = lean_unbox_usize(v___x_3293_);
lean_dec(v___x_3293_);
v___x_31097__boxed_3316_ = lean_unbox(v___x_3301_);
v_res_3317_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3286_, v_tail_3287_, v_recName_3288_, v___x_3289_, v___x_3290_, v___x_3291_, v_sz_boxed_3314_, v___x_31089__boxed_3315_, v___x_3294_, v___x_3295_, v___x_3296_, v___x_3297_, v___x_3298_, v___x_3299_, v_val_3300_, v___x_31097__boxed_3316_, v_brecOnGoName_3302_, v_levelParams_3303_, v___x_3304_, v_brecOnName_3305_, v___x_3306_, v_brecOnEqName_3307_, v_fs_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___x_3306_);
lean_dec(v_val_3300_);
lean_dec(v___x_3298_);
lean_dec_ref(v___x_3294_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3318_, lean_object* v_a_3319_, uint8_t v___x_3320_, lean_object* v_f_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; uint8_t v___x_3329_; uint8_t v___x_3330_; lean_object* v___x_3331_; 
lean_inc_ref(v_targs_3318_);
v___x_3327_ = lean_array_push(v_targs_3318_, v_f_3321_);
v___x_3328_ = l_Lean_mkAppN(v_a_3319_, v_targs_3318_);
lean_dec_ref(v_targs_3318_);
v___x_3329_ = 0;
v___x_3330_ = 1;
v___x_3331_ = l_Lean_Meta_mkForallFVars(v___x_3327_, v___x_3328_, v___x_3329_, v___x_3320_, v___x_3320_, v___x_3330_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
lean_dec_ref(v___x_3327_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3332_, lean_object* v_a_3333_, lean_object* v___x_3334_, lean_object* v_f_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
uint8_t v___x_31807__boxed_3341_; lean_object* v_res_3342_; 
v___x_31807__boxed_3341_ = lean_unbox(v___x_3334_);
v_res_3342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3332_, v_a_3333_, v___x_31807__boxed_3341_, v_f_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3346_, uint8_t v___x_3347_, lean_object* v___x_3348_, lean_object* v_targs_3349_, lean_object* v_x_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v___x_3356_; lean_object* v___f_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3356_ = lean_box(v___x_3347_);
lean_inc_ref(v_targs_3349_);
v___f_3357_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3357_, 0, v_targs_3349_);
lean_closure_set(v___f_3357_, 1, v_a_3346_);
lean_closure_set(v___f_3357_, 2, v___x_3356_);
v___x_3358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3359_ = l_Lean_mkAppN(v___x_3348_, v_targs_3349_);
lean_dec_ref(v_targs_3349_);
v___x_3360_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3358_, v___x_3359_, v___f_3357_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_targs_3364_, lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
uint8_t v___x_31841__boxed_3371_; lean_object* v_res_3372_; 
v___x_31841__boxed_3371_ = lean_unbox(v___x_3362_);
v_res_3372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3361_, v___x_31841__boxed_3371_, v___x_3363_, v_targs_3364_, v_x_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec_ref(v_x_3365_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3373_, lean_object* v_x_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v___x_3380_; 
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v_a_3373_);
return v___x_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3381_, lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_){
_start:
{
lean_object* v_res_3388_; 
v_res_3388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3381_, v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
lean_dec(v___y_3384_);
lean_dec_ref(v___y_3383_);
lean_dec_ref(v_x_3382_);
return v_res_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v_as_3390_, size_t v_sz_3391_, size_t v_i_3392_, lean_object* v_b_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_usize_dec_lt(v_i_3392_, v_sz_3391_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v_b_3393_);
return v___x_3400_;
}
else
{
lean_object* v_snd_3401_; lean_object* v_fst_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3498_; 
v_snd_3401_ = lean_ctor_get(v_b_3393_, 1);
v_fst_3402_ = lean_ctor_get(v_b_3393_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_b_3393_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3404_ = v_b_3393_;
v_isShared_3405_ = v_isSharedCheck_3498_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_snd_3401_);
lean_inc(v_fst_3402_);
lean_dec(v_b_3393_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3498_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v_fst_3406_; lean_object* v_snd_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3497_; 
v_fst_3406_ = lean_ctor_get(v_snd_3401_, 0);
v_snd_3407_ = lean_ctor_get(v_snd_3401_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_snd_3401_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3409_ = v_snd_3401_;
v_isShared_3410_ = v_isSharedCheck_3497_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_snd_3407_);
lean_inc(v_fst_3406_);
lean_dec(v_snd_3401_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3497_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v_next_3419_; 
v_next_3419_ = lean_ctor_get(v_snd_3407_, 0);
lean_inc(v_next_3419_);
if (lean_obj_tag(v_next_3419_) == 0)
{
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
goto v___jp_3411_;
}
else
{
lean_object* v_upperBound_3420_; lean_object* v_val_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3496_; 
v_upperBound_3420_ = lean_ctor_get(v_snd_3407_, 1);
v_val_3421_ = lean_ctor_get(v_next_3419_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_next_3419_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3423_ = v_next_3419_;
v_isShared_3424_ = v_isSharedCheck_3496_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_val_3421_);
lean_dec(v_next_3419_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3496_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_nat_dec_lt(v_val_3421_, v_upperBound_3420_);
if (v___x_3425_ == 0)
{
lean_del_object(v___x_3423_);
lean_dec(v_val_3421_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
goto v___jp_3411_;
}
else
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3493_; 
lean_inc(v_upperBound_3420_);
lean_del_object(v___x_3409_);
lean_del_object(v___x_3404_);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_snd_3407_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; lean_object* v_unused_3495_; 
v_unused_3494_ = lean_ctor_get(v_snd_3407_, 1);
lean_dec(v_unused_3494_);
v_unused_3495_ = lean_ctor_get(v_snd_3407_, 0);
lean_dec(v_unused_3495_);
v___x_3427_ = v_snd_3407_;
v_isShared_3428_ = v_isSharedCheck_3493_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v_snd_3407_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3493_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v_array_3429_; lean_object* v_start_3430_; lean_object* v_stop_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
v_array_3429_ = lean_ctor_get(v_fst_3406_, 0);
v_start_3430_ = lean_ctor_get(v_fst_3406_, 1);
v_stop_3431_ = lean_ctor_get(v_fst_3406_, 2);
v___x_3432_ = lean_unsigned_to_nat(1u);
v___x_3433_ = lean_nat_add(v_val_3421_, v___x_3432_);
lean_dec(v_val_3421_);
lean_inc(v___x_3433_);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 0, v___x_3433_);
v___x_3435_ = v___x_3423_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3433_);
v___x_3435_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3437_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3435_);
v___x_3437_ = v___x_3427_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3435_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_upperBound_3420_);
v___x_3437_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_nat_dec_lt(v_start_3430_, v_stop_3431_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec(v___x_3433_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v_fst_3406_);
lean_ctor_set(v___x_3439_, 1, v___x_3437_);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_fst_3402_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
else
{
lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3487_; 
lean_inc(v_stop_3431_);
lean_inc(v_start_3430_);
lean_inc_ref(v_array_3429_);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_fst_3406_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; lean_object* v_unused_3489_; lean_object* v_unused_3490_; 
v_unused_3488_ = lean_ctor_get(v_fst_3406_, 2);
lean_dec(v_unused_3488_);
v_unused_3489_ = lean_ctor_get(v_fst_3406_, 1);
lean_dec(v_unused_3489_);
v_unused_3490_ = lean_ctor_get(v_fst_3406_, 0);
lean_dec(v_unused_3490_);
v___x_3443_ = v_fst_3406_;
v_isShared_3444_ = v_isSharedCheck_3487_;
goto v_resetjp_3442_;
}
else
{
lean_dec(v_fst_3406_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3487_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v_a_3445_; lean_object* v___x_3446_; 
v_a_3445_ = lean_array_uget_borrowed(v_as_3390_, v_i_3392_);
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc(v___y_3395_);
lean_inc_ref(v___y_3394_);
lean_inc(v_a_3445_);
v___x_3446_ = lean_infer_type(v_a_3445_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___f_3450_; uint8_t v___x_3451_; lean_object* v___x_3452_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = lean_array_fget_borrowed(v_array_3429_, v_start_3430_);
v___x_3449_ = lean_box(v___x_3438_);
lean_inc(v___x_3448_);
lean_inc(v_a_3445_);
v___f_3450_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3450_, 0, v_a_3445_);
lean_closure_set(v___f_3450_, 1, v___x_3449_);
lean_closure_set(v___f_3450_, 2, v___x_3448_);
v___x_3451_ = 0;
lean_inc(v___y_3397_);
lean_inc_ref(v___y_3396_);
lean_inc(v___y_3395_);
lean_inc_ref(v___y_3394_);
v___x_3452_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3447_, v___f_3450_, v___x_3451_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; lean_object* v___x_3457_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref(v___x_3452_);
v___f_3454_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3454_, 0, v_a_3453_);
v___x_3455_ = lean_nat_add(v_start_3430_, v___x_3432_);
lean_dec(v_start_3430_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 1, v___x_3455_);
v___x_3457_ = v___x_3443_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_array_3429_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v___x_3455_);
lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_stop_3431_);
v___x_3457_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; size_t v___x_3467_; size_t v___x_3468_; 
v___x_3458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3459_ = l_Nat_reprFast(v___x_3433_);
v___x_3460_ = lean_string_append(v___x_3458_, v___x_3459_);
lean_dec_ref(v___x_3459_);
v___x_3461_ = lean_box(0);
v___x_3462_ = l_Lean_Name_str___override(v___x_3461_, v___x_3460_);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v___f_3454_);
v___x_3464_ = lean_array_push(v_fst_3402_, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3457_);
lean_ctor_set(v___x_3465_, 1, v___x_3437_);
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = ((size_t)1ULL);
v___x_3468_ = lean_usize_add(v_i_3392_, v___x_3467_);
v_i_3392_ = v___x_3468_;
v_b_3393_ = v___x_3466_;
goto _start;
}
}
else
{
lean_object* v_a_3471_; lean_object* v___x_3473_; uint8_t v_isShared_3474_; uint8_t v_isSharedCheck_3478_; 
lean_del_object(v___x_3443_);
lean_dec_ref(v___x_3437_);
lean_dec(v___x_3433_);
lean_dec(v_stop_3431_);
lean_dec(v_start_3430_);
lean_dec_ref(v_array_3429_);
lean_dec(v_fst_3402_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
v_a_3471_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3473_ = v___x_3452_;
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
else
{
lean_inc(v_a_3471_);
lean_dec(v___x_3452_);
v___x_3473_ = lean_box(0);
v_isShared_3474_ = v_isSharedCheck_3478_;
goto v_resetjp_3472_;
}
v_resetjp_3472_:
{
lean_object* v___x_3476_; 
if (v_isShared_3474_ == 0)
{
v___x_3476_ = v___x_3473_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
v___x_3476_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
return v___x_3476_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_del_object(v___x_3443_);
lean_dec_ref(v___x_3437_);
lean_dec(v___x_3433_);
lean_dec(v_stop_3431_);
lean_dec(v_start_3430_);
lean_dec_ref(v_array_3429_);
lean_dec(v_fst_3402_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
v_a_3479_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3446_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3446_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
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
v___jp_3411_:
{
lean_object* v___x_3413_; 
if (v_isShared_3410_ == 0)
{
v___x_3413_ = v___x_3409_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_fst_3406_);
lean_ctor_set(v_reuseFailAlloc_3418_, 1, v_snd_3407_);
v___x_3413_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3415_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 1, v___x_3413_);
v___x_3415_ = v___x_3404_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_fst_3402_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
return v___x_3416_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v_as_3499_, lean_object* v_sz_3500_, lean_object* v_i_3501_, lean_object* v_b_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
size_t v_sz_boxed_3508_; size_t v_i_boxed_3509_; lean_object* v_res_3510_; 
v_sz_boxed_3508_ = lean_unbox_usize(v_sz_3500_);
lean_dec(v_sz_3500_);
v_i_boxed_3509_ = lean_unbox_usize(v_i_3501_);
lean_dec(v_i_3501_);
v_res_3510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v_as_3499_, v_sz_boxed_3508_, v_i_boxed_3509_, v_b_3502_, v___y_3503_, v___y_3504_, v___y_3505_, v___y_3506_);
lean_dec_ref(v_as_3499_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3511_, size_t v_i_3512_, lean_object* v_bs_3513_){
_start:
{
uint8_t v___x_3514_; 
v___x_3514_ = lean_usize_dec_lt(v_i_3512_, v_sz_3511_);
if (v___x_3514_ == 0)
{
return v_bs_3513_;
}
else
{
lean_object* v_v_3515_; lean_object* v_fst_3516_; lean_object* v_snd_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3533_; 
v_v_3515_ = lean_array_uget(v_bs_3513_, v_i_3512_);
v_fst_3516_ = lean_ctor_get(v_v_3515_, 0);
v_snd_3517_ = lean_ctor_get(v_v_3515_, 1);
v_isSharedCheck_3533_ = !lean_is_exclusive(v_v_3515_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3519_ = v_v_3515_;
v_isShared_3520_ = v_isSharedCheck_3533_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3517_);
lean_inc(v_fst_3516_);
lean_dec(v_v_3515_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3533_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v_bs_x27_3522_; uint8_t v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3521_ = lean_unsigned_to_nat(0u);
v_bs_x27_3522_ = lean_array_uset(v_bs_3513_, v_i_3512_, v___x_3521_);
v___x_3523_ = 0;
v___x_3524_ = lean_box(v___x_3523_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3524_);
v___x_3526_ = v___x_3519_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_snd_3517_);
v___x_3526_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3527_; size_t v___x_3528_; size_t v___x_3529_; lean_object* v___x_3530_; 
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v_fst_3516_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = ((size_t)1ULL);
v___x_3529_ = lean_usize_add(v_i_3512_, v___x_3528_);
v___x_3530_ = lean_array_uset(v_bs_x27_3522_, v_i_3512_, v___x_3527_);
v_i_3512_ = v___x_3529_;
v_bs_3513_ = v___x_3530_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3534_, lean_object* v_i_3535_, lean_object* v_bs_3536_){
_start:
{
size_t v_sz_boxed_3537_; size_t v_i_boxed_3538_; lean_object* v_res_3539_; 
v_sz_boxed_3537_ = lean_unbox_usize(v_sz_3534_);
lean_dec(v_sz_3534_);
v_i_boxed_3538_ = lean_unbox_usize(v_i_3535_);
lean_dec(v_i_3535_);
v_res_3539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3537_, v_i_boxed_3538_, v_bs_3536_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0(lean_object* v___x_3540_, lean_object* v_a_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_30650__overap_3548_; lean_object* v___x_3549_; 
v___x_3547_ = l_Lean_instInhabitedExpr;
v___x_30650__overap_3548_ = l_instInhabitedOfMonad___redArg(v___x_3540_, v___x_3547_);
v___x_3549_ = lean_apply_5(v___x_30650__overap_3548_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, lean_box(0));
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0___boxed(lean_object* v___x_3550_, lean_object* v_a_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_res_3557_; 
v_res_3557_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0(v___x_3550_, v_a_3551_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec_ref(v_a_3551_);
return v_res_3557_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_3558_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3560_ = l_ReaderT_instMonad___redArg(v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_acc_3565_, lean_object* v_declInfos_3566_, lean_object* v_k_3567_, lean_object* v_kind_3568_, lean_object* v_inst_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
uint8_t v_kind_boxed_3576_; lean_object* v_res_3577_; 
v_kind_boxed_3576_ = lean_unbox(v_kind_3568_);
v_res_3577_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0(v_acc_3565_, v_declInfos_3566_, v_k_3567_, v_kind_boxed_3576_, v_inst_3569_, v_b_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
return v_res_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(lean_object* v_acc_3578_, lean_object* v_declInfos_3579_, lean_object* v_k_3580_, uint8_t v_kind_3581_, lean_object* v_inst_3582_, lean_object* v_name_3583_, uint8_t v_bi_3584_, lean_object* v_type_3585_, uint8_t v_kind_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; 
v___x_3592_ = lean_box(v_kind_3581_);
v___f_3593_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3593_, 0, v_acc_3578_);
lean_closure_set(v___f_3593_, 1, v_declInfos_3579_);
lean_closure_set(v___f_3593_, 2, v_k_3580_);
lean_closure_set(v___f_3593_, 3, v___x_3592_);
lean_closure_set(v___f_3593_, 4, v_inst_3582_);
v___x_3594_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3583_, v_bi_3584_, v_type_3585_, v___f_3593_, v_kind_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3602_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3597_ = v___x_3594_;
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v___x_3594_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3602_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
return v___x_3600_;
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
v_a_3603_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3594_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3594_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(lean_object* v_declInfos_3611_, lean_object* v_k_3612_, uint8_t v_kind_3613_, lean_object* v_inst_3614_, lean_object* v_acc_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; lean_object* v_toApplicative_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3707_; 
v___x_3621_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1);
v_toApplicative_3622_ = lean_ctor_get(v___x_3621_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3621_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v___x_3621_, 1);
lean_dec(v_unused_3708_);
v___x_3624_ = v___x_3621_;
v_isShared_3625_ = v_isSharedCheck_3707_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_toApplicative_3622_);
lean_dec(v___x_3621_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3707_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v_toFunctor_3626_; lean_object* v_toSeq_3627_; lean_object* v_toSeqLeft_3628_; lean_object* v_toSeqRight_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3705_; 
v_toFunctor_3626_ = lean_ctor_get(v_toApplicative_3622_, 0);
v_toSeq_3627_ = lean_ctor_get(v_toApplicative_3622_, 2);
v_toSeqLeft_3628_ = lean_ctor_get(v_toApplicative_3622_, 3);
v_toSeqRight_3629_ = lean_ctor_get(v_toApplicative_3622_, 4);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_toApplicative_3622_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v_toApplicative_3622_, 1);
lean_dec(v_unused_3706_);
v___x_3631_ = v_toApplicative_3622_;
v_isShared_3632_ = v_isSharedCheck_3705_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_toSeqRight_3629_);
lean_inc(v_toSeqLeft_3628_);
lean_inc(v_toSeq_3627_);
lean_inc(v_toFunctor_3626_);
lean_dec(v_toApplicative_3622_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3705_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___f_3635_; lean_object* v___f_3636_; lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___f_3639_; lean_object* v___f_3640_; lean_object* v___x_3642_; 
v___f_3633_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__2));
v___f_3634_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__3));
lean_inc_ref(v_toFunctor_3626_);
v___f_3635_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3635_, 0, v_toFunctor_3626_);
v___f_3636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3636_, 0, v_toFunctor_3626_);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___f_3635_);
lean_ctor_set(v___x_3637_, 1, v___f_3636_);
v___f_3638_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3638_, 0, v_toSeqRight_3629_);
v___f_3639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3639_, 0, v_toSeqLeft_3628_);
v___f_3640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3640_, 0, v_toSeq_3627_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 4, v___f_3638_);
lean_ctor_set(v___x_3631_, 3, v___f_3639_);
lean_ctor_set(v___x_3631_, 2, v___f_3640_);
lean_ctor_set(v___x_3631_, 1, v___f_3633_);
lean_ctor_set(v___x_3631_, 0, v___x_3637_);
v___x_3642_ = v___x_3631_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3637_);
lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___f_3633_);
lean_ctor_set(v_reuseFailAlloc_3704_, 2, v___f_3640_);
lean_ctor_set(v_reuseFailAlloc_3704_, 3, v___f_3639_);
lean_ctor_set(v_reuseFailAlloc_3704_, 4, v___f_3638_);
v___x_3642_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
lean_object* v___x_3644_; 
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v___f_3634_);
lean_ctor_set(v___x_3624_, 0, v___x_3642_);
v___x_3644_ = v___x_3624_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v___f_3634_);
v___x_3644_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; lean_object* v_toApplicative_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3701_; 
v___x_3645_ = l_ReaderT_instMonad___redArg(v___x_3644_);
v_toApplicative_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v___x_3645_, 1);
lean_dec(v_unused_3702_);
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3701_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_toApplicative_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3701_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_toFunctor_3650_; lean_object* v_toSeq_3651_; lean_object* v_toSeqLeft_3652_; lean_object* v_toSeqRight_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3699_; 
v_toFunctor_3650_ = lean_ctor_get(v_toApplicative_3646_, 0);
v_toSeq_3651_ = lean_ctor_get(v_toApplicative_3646_, 2);
v_toSeqLeft_3652_ = lean_ctor_get(v_toApplicative_3646_, 3);
v_toSeqRight_3653_ = lean_ctor_get(v_toApplicative_3646_, 4);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_toApplicative_3646_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_toApplicative_3646_, 1);
lean_dec(v_unused_3700_);
v___x_3655_ = v_toApplicative_3646_;
v_isShared_3656_ = v_isSharedCheck_3699_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_toSeqRight_3653_);
lean_inc(v_toSeqLeft_3652_);
lean_inc(v_toSeq_3651_);
lean_inc(v_toFunctor_3650_);
lean_dec(v_toApplicative_3646_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3699_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___f_3657_; lean_object* v___f_3658_; lean_object* v___f_3659_; lean_object* v___f_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___f_3664_; lean_object* v___x_3666_; 
v___f_3657_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__4));
v___f_3658_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__5));
lean_inc_ref(v_toFunctor_3650_);
v___f_3659_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3659_, 0, v_toFunctor_3650_);
v___f_3660_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3660_, 0, v_toFunctor_3650_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___f_3659_);
lean_ctor_set(v___x_3661_, 1, v___f_3660_);
v___f_3662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3662_, 0, v_toSeqRight_3653_);
v___f_3663_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3663_, 0, v_toSeqLeft_3652_);
v___f_3664_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3664_, 0, v_toSeq_3651_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 4, v___f_3662_);
lean_ctor_set(v___x_3655_, 3, v___f_3663_);
lean_ctor_set(v___x_3655_, 2, v___f_3664_);
lean_ctor_set(v___x_3655_, 1, v___f_3657_);
lean_ctor_set(v___x_3655_, 0, v___x_3661_);
v___x_3666_ = v___x_3655_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v___f_3657_);
lean_ctor_set(v_reuseFailAlloc_3698_, 2, v___f_3664_);
lean_ctor_set(v_reuseFailAlloc_3698_, 3, v___f_3663_);
lean_ctor_set(v_reuseFailAlloc_3698_, 4, v___f_3662_);
v___x_3666_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v___f_3658_);
lean_ctor_set(v___x_3648_, 0, v___x_3666_);
v___x_3668_ = v___x_3648_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___f_3658_);
v___x_3668_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3669_ = lean_array_get_size(v_acc_3615_);
v___x_3670_ = lean_array_get_size(v_declInfos_3611_);
v___x_3671_ = lean_nat_dec_lt(v___x_3669_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
lean_dec_ref(v___x_3668_);
lean_dec(v_inst_3614_);
lean_dec_ref(v_declInfos_3611_);
v___x_3672_ = lean_apply_6(v_k_3612_, v_acc_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, lean_box(0));
return v___x_3672_;
}
else
{
lean_object* v___f_3673_; lean_object* v___x_3674_; uint8_t v___x_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v_snd_3681_; lean_object* v_fst_3682_; lean_object* v_fst_3683_; lean_object* v_snd_3684_; lean_object* v___x_3685_; 
v___f_3673_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3673_, 0, v___x_3668_);
v___x_3674_ = lean_box(0);
v___x_3675_ = 0;
v___f_3676_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3676_, 0, v___f_3673_);
v___x_3677_ = lean_box(v___x_3675_);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
lean_ctor_set(v___x_3678_, 1, v___f_3676_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3674_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_array_get_borrowed(v___x_3679_, v_declInfos_3611_, v___x_3669_);
v_snd_3681_ = lean_ctor_get(v___x_3680_, 1);
v_fst_3682_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_fst_3682_);
v_fst_3683_ = lean_ctor_get(v_snd_3681_, 0);
v_snd_3684_ = lean_ctor_get(v_snd_3681_, 1);
lean_inc(v_snd_3684_);
lean_inc(v___y_3619_);
lean_inc_ref(v___y_3618_);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc_ref(v_acc_3615_);
v___x_3685_ = lean_apply_6(v_snd_3684_, v_acc_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, lean_box(0));
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; uint8_t v___x_3687_; lean_object* v___x_3688_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref(v___x_3685_);
v___x_3687_ = lean_unbox(v_fst_3683_);
v___x_3688_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(v_acc_3615_, v_declInfos_3611_, v_k_3612_, v_kind_3613_, v_inst_3614_, v_fst_3682_, v___x_3687_, v_a_3686_, v_kind_3613_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
return v___x_3688_;
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_fst_3682_);
lean_dec(v___y_3619_);
lean_dec_ref(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec_ref(v_acc_3615_);
lean_dec(v_inst_3614_);
lean_dec_ref(v_k_3612_);
lean_dec_ref(v_declInfos_3611_);
v_a_3689_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3685_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3685_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0(lean_object* v_acc_3709_, lean_object* v_declInfos_3710_, lean_object* v_k_3711_, uint8_t v_kind_3712_, lean_object* v_inst_3713_, lean_object* v_b_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3720_ = lean_array_push(v_acc_3709_, v_b_3714_);
v___x_3721_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_3710_, v_k_3711_, v_kind_3712_, v_inst_3713_, v___x_3720_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___boxed(lean_object* v_acc_3722_, lean_object* v_declInfos_3723_, lean_object* v_k_3724_, lean_object* v_kind_3725_, lean_object* v_inst_3726_, lean_object* v_name_3727_, lean_object* v_bi_3728_, lean_object* v_type_3729_, lean_object* v_kind_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
uint8_t v_kind_boxed_3736_; uint8_t v_bi_boxed_3737_; uint8_t v_kind_boxed_3738_; lean_object* v_res_3739_; 
v_kind_boxed_3736_ = lean_unbox(v_kind_3725_);
v_bi_boxed_3737_ = lean_unbox(v_bi_3728_);
v_kind_boxed_3738_ = lean_unbox(v_kind_3730_);
v_res_3739_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(v_acc_3722_, v_declInfos_3723_, v_k_3724_, v_kind_boxed_3736_, v_inst_3726_, v_name_3727_, v_bi_boxed_3737_, v_type_3729_, v_kind_boxed_3738_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_declInfos_3740_, lean_object* v_k_3741_, lean_object* v_kind_3742_, lean_object* v_inst_3743_, lean_object* v_acc_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
uint8_t v_kind_boxed_3750_; lean_object* v_res_3751_; 
v_kind_boxed_3750_ = lean_unbox(v_kind_3742_);
v_res_3751_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_3740_, v_k_3741_, v_kind_boxed_3750_, v_inst_3743_, v_acc_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(lean_object* v_inst_3752_, lean_object* v_declInfos_3753_, lean_object* v_k_3754_, uint8_t v_kind_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3762_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_3753_, v_k_3754_, v_kind_3755_, v_inst_3752_, v___x_3761_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
return v___x_3762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg___boxed(lean_object* v_inst_3763_, lean_object* v_declInfos_3764_, lean_object* v_k_3765_, lean_object* v_kind_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
uint8_t v_kind_boxed_3772_; lean_object* v_res_3773_; 
v_kind_boxed_3772_ = lean_unbox(v_kind_3766_);
v_res_3773_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(v_inst_3763_, v_declInfos_3764_, v_k_3765_, v_kind_boxed_3772_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(lean_object* v_inst_3774_, lean_object* v_declInfos_3775_, lean_object* v_k_3776_, uint8_t v_kind_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
size_t v_sz_3783_; size_t v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v_sz_3783_ = lean_array_size(v_declInfos_3775_);
v___x_3784_ = ((size_t)0ULL);
v___x_3785_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3783_, v___x_3784_, v_declInfos_3775_);
v___x_3786_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(v_inst_3774_, v___x_3785_, v_k_3776_, v_kind_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg___boxed(lean_object* v_inst_3787_, lean_object* v_declInfos_3788_, lean_object* v_k_3789_, lean_object* v_kind_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
uint8_t v_kind_boxed_3796_; lean_object* v_res_3797_; 
v_kind_boxed_3796_ = lean_unbox(v_kind_3790_);
v_res_3797_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(v_inst_3787_, v_declInfos_3788_, v_k_3789_, v_kind_boxed_3796_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
return v_res_3797_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3799_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3800_ = lean_unsigned_to_nat(4u);
v___x_3801_ = lean_unsigned_to_nat(202u);
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3803_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3804_ = l_mkPanicMessageWithDecl(v___x_3803_, v___x_3802_, v___x_3801_, v___x_3800_, v___x_3799_);
return v___x_3804_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3811_ = l_Lean_stringToMessageData(v___x_3810_);
return v___x_3811_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3813_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3814_ = l_Lean_stringToMessageData(v___x_3813_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3817_, lean_object* v_numMotives_3818_, lean_object* v_numMinors_3819_, lean_object* v___x_3820_, lean_object* v_all_3821_, lean_object* v_head_3822_, lean_object* v_tail_3823_, lean_object* v_recName_3824_, lean_object* v_brecOnGoName_3825_, lean_object* v_levelParams_3826_, lean_object* v_brecOnName_3827_, lean_object* v_brecOnEqName_3828_, lean_object* v_type_3829_, lean_object* v_refArgs_3830_, lean_object* v_refBody_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; uint8_t v___x_3840_; 
v___x_3837_ = lean_nat_add(v_nParams_3817_, v_numMotives_3818_);
v___x_3838_ = lean_nat_add(v___x_3837_, v_numMinors_3819_);
v___x_3839_ = lean_array_get_size(v_refArgs_3830_);
v___x_3840_ = lean_nat_dec_lt(v___x_3838_, v___x_3839_);
if (v___x_3840_ == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
lean_dec_ref(v_refArgs_3830_);
lean_dec_ref(v_type_3829_);
lean_dec(v_brecOnEqName_3828_);
lean_dec(v_brecOnName_3827_);
lean_dec(v_levelParams_3826_);
lean_dec(v_brecOnGoName_3825_);
lean_dec(v_recName_3824_);
lean_dec(v_tail_3823_);
lean_dec(v_head_3822_);
lean_dec_ref(v_all_3821_);
lean_dec(v___x_3820_);
lean_dec(v_nParams_3817_);
v___x_3841_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3842_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3841_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
return v___x_3842_;
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3843_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3817_);
lean_inc_ref(v_refArgs_3830_);
v___x_3844_ = l_Array_toSubarray___redArg(v_refArgs_3830_, v___x_3843_, v_nParams_3817_);
lean_inc(v___x_3837_);
lean_inc_ref(v_refArgs_3830_);
v___x_3845_ = l_Array_toSubarray___redArg(v_refArgs_3830_, v_nParams_3817_, v___x_3837_);
v___x_3846_ = l_Subarray_copy___redArg(v___x_3845_);
v___x_3847_ = l_Lean_Expr_getAppFn(v_refBody_3831_);
v___x_3848_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3846_, v___x_3847_);
lean_dec_ref(v___x_3847_);
if (lean_obj_tag(v___x_3848_) == 1)
{
lean_object* v_val_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec_ref(v_type_3829_);
v_val_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_val_3849_);
lean_dec_ref(v___x_3848_);
v___x_3850_ = l_Lean_instInhabitedExpr;
v___x_3851_ = lean_unsigned_to_nat(1u);
v___x_3852_ = lean_nat_sub(v___x_3839_, v___x_3851_);
v___x_3853_ = lean_array_get(v___x_3850_, v_refArgs_3830_, v___x_3852_);
lean_inc(v___y_3835_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
lean_inc(v___x_3853_);
v___x_3854_ = lean_infer_type(v___x_3853_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3856_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_a_3855_);
lean_dec_ref(v___x_3854_);
lean_inc(v___y_3835_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
v___x_3856_ = lean_infer_type(v_a_3855_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
lean_inc(v___y_3835_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
v___x_3858_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3857_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref(v___x_3858_);
if (lean_obj_tag(v_a_3859_) == 1)
{
lean_object* v_val_3860_; lean_object* v___x_3861_; lean_object* v___f_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; size_t v_sz_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
v_val_3860_ = lean_ctor_get(v_a_3859_, 0);
lean_inc(v_val_3860_);
lean_dec_ref(v_a_3859_);
v___x_3861_ = l_Subarray_copy___redArg(v___x_3844_);
lean_inc_ref(v___x_3846_);
lean_inc_ref(v___x_3861_);
lean_inc(v___x_3820_);
v___f_3862_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3862_, 0, v___x_3820_);
lean_closure_set(v___f_3862_, 1, v___x_3861_);
lean_closure_set(v___f_3862_, 2, v___x_3846_);
lean_closure_set(v___f_3862_, 3, v_all_3821_);
lean_closure_set(v___f_3862_, 4, v___x_3843_);
lean_closure_set(v___f_3862_, 5, v___x_3851_);
v___x_3863_ = lean_array_get_size(v___x_3846_);
v___x_3864_ = l_Array_ofFn___redArg(v___x_3863_, v___f_3862_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3866_ = lean_array_get_size(v___x_3864_);
lean_inc_ref(v___x_3864_);
v___x_3867_ = l_Array_toSubarray___redArg(v___x_3864_, v___x_3843_, v___x_3866_);
v___x_3868_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3868_);
lean_ctor_set(v___x_3869_, 1, v___x_3863_);
lean_inc_ref(v___x_3867_);
v___x_3870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3867_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3865_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v_sz_3872_ = lean_array_size(v___x_3846_);
v___x_3873_ = ((size_t)0ULL);
lean_inc(v___y_3835_);
lean_inc_ref(v___y_3834_);
lean_inc(v___y_3833_);
lean_inc_ref(v___y_3832_);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3846_, v_sz_3872_, v___x_3873_, v___x_3871_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v_fst_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___f_3885_; lean_object* v___x_3886_; uint8_t v___x_3887_; lean_object* v___x_3888_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
v_fst_3876_ = lean_ctor_get(v_a_3875_, 0);
lean_inc(v_fst_3876_);
lean_dec(v_a_3875_);
lean_inc(v___x_3838_);
lean_inc_ref(v_refArgs_3830_);
v___x_3877_ = l_Array_toSubarray___redArg(v_refArgs_3830_, v___x_3837_, v___x_3838_);
v___x_3878_ = l_Subarray_copy___redArg(v___x_3877_);
v___x_3879_ = l_Array_toSubarray___redArg(v_refArgs_3830_, v___x_3838_, v___x_3852_);
v___x_3880_ = l_Subarray_copy___redArg(v___x_3879_);
v___x_3881_ = l_Lean_mkLevelMax(v_val_3860_, v_head_3822_);
v___x_3882_ = lean_box_usize(v_sz_3872_);
v___x_3883_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3884_ = lean_box(v___x_3840_);
v___f_3885_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3885_, 0, v___x_3881_);
lean_closure_set(v___f_3885_, 1, v_tail_3823_);
lean_closure_set(v___f_3885_, 2, v_recName_3824_);
lean_closure_set(v___f_3885_, 3, v___x_3861_);
lean_closure_set(v___f_3885_, 4, v___x_3867_);
lean_closure_set(v___f_3885_, 5, v___x_3846_);
lean_closure_set(v___f_3885_, 6, v___x_3882_);
lean_closure_set(v___f_3885_, 7, v___x_3883_);
lean_closure_set(v___f_3885_, 8, v___x_3878_);
lean_closure_set(v___f_3885_, 9, v___x_3864_);
lean_closure_set(v___f_3885_, 10, v___x_3880_);
lean_closure_set(v___f_3885_, 11, v___x_3853_);
lean_closure_set(v___f_3885_, 12, v___x_3851_);
lean_closure_set(v___f_3885_, 13, v___x_3850_);
lean_closure_set(v___f_3885_, 14, v_val_3849_);
lean_closure_set(v___f_3885_, 15, v___x_3884_);
lean_closure_set(v___f_3885_, 16, v_brecOnGoName_3825_);
lean_closure_set(v___f_3885_, 17, v_levelParams_3826_);
lean_closure_set(v___f_3885_, 18, v___x_3820_);
lean_closure_set(v___f_3885_, 19, v_brecOnName_3827_);
lean_closure_set(v___f_3885_, 20, v___x_3843_);
lean_closure_set(v___f_3885_, 21, v_brecOnEqName_3828_);
v___x_3886_ = lean_box(0);
v___x_3887_ = 0;
v___x_3888_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(v___x_3886_, v_fst_3876_, v___f_3885_, v___x_3887_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
return v___x_3888_;
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v___x_3867_);
lean_dec_ref(v___x_3864_);
lean_dec_ref(v___x_3861_);
lean_dec(v_val_3860_);
lean_dec(v___x_3853_);
lean_dec(v___x_3852_);
lean_dec(v_val_3849_);
lean_dec_ref(v___x_3846_);
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_refArgs_3830_);
lean_dec(v_brecOnEqName_3828_);
lean_dec(v_brecOnName_3827_);
lean_dec(v_levelParams_3826_);
lean_dec(v_brecOnGoName_3825_);
lean_dec(v_recName_3824_);
lean_dec(v_tail_3823_);
lean_dec(v_head_3822_);
lean_dec(v___x_3820_);
v_a_3889_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3874_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3874_);
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
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
lean_dec(v_a_3859_);
lean_dec(v___x_3852_);
lean_dec(v_val_3849_);
lean_dec_ref(v___x_3846_);
lean_dec_ref(v___x_3844_);
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
lean_dec_ref(v_refArgs_3830_);
lean_dec(v_brecOnEqName_3828_);
lean_dec(v_brecOnName_3827_);
lean_dec(v_levelParams_3826_);
lean_dec(v_brecOnGoName_3825_);
lean_dec(v_recName_3824_);
lean_dec(v_tail_3823_);
lean_dec(v_head_3822_);
lean_dec_ref(v_all_3821_);
lean_dec(v___x_3820_);
v___x_3897_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3898_ = l_Lean_MessageData_ofExpr(v___x_3853_);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3897_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3899_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
v___x_3902_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3901_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
return v___x_3902_;
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v___x_3853_);
lean_dec(v___x_3852_);
lean_dec(v_val_3849_);
lean_dec_ref(v___x_3846_);
lean_dec_ref(v___x_3844_);
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_refArgs_3830_);
lean_dec(v_brecOnEqName_3828_);
lean_dec(v_brecOnName_3827_);
lean_dec(v_levelParams_3826_);
lean_dec(v_brecOnGoName_3825_);
lean_dec(v_recName_3824_);
lean_dec(v_tail_3823_);
lean_dec(v_head_3822_);
lean_dec_ref(v_all_3821_);
lean_dec(v___x_3820_);
v_a_3903_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3858_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3858_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_dec(v___x_3853_);
lean_dec(v___x_3852_);
lean_dec(v_val_3849_);
lean_dec_ref(v___x_3846_);
lean_dec_ref(v___x_3844_);
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_refArgs_3830_);
lean_dec(v_brecOnEqName_3828_);
lean_dec(v_brecOnName_3827_);
lean_dec(v_levelParams_3826_);
lean_dec(v_brecOnGoName_3825_);
lean_dec(v_recName_3824_);
lean_dec(v_tail_3823_);
lean_dec(v_head_3822_);
lean_dec_ref(v_all_3821_);
lean_dec(v___x_3820_);
v_a_3911_ = lean_ctor_get(v___x_3856_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3856_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3856_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3856_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_dec(v___x_3853_);
lean_dec(v___x_3852_);
lean_dec(v_val_3849_);
lean_dec_ref(v___x_3846_);
lean_dec_ref(v___x_3844_);
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_refArgs_3830_);
lean_dec(v_brecOnEqName_3828_);
lean_dec(v_brecOnName_3827_);
lean_dec(v_levelParams_3826_);
lean_dec(v_brecOnGoName_3825_);
lean_dec(v_recName_3824_);
lean_dec(v_tail_3823_);
lean_dec(v_head_3822_);
lean_dec_ref(v_all_3821_);
lean_dec(v___x_3820_);
v_a_3919_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3854_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3854_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec(v___x_3848_);
lean_dec_ref(v___x_3844_);
lean_dec(v___x_3838_);
lean_dec(v___x_3837_);
lean_dec_ref(v_refArgs_3830_);
lean_dec(v_brecOnEqName_3828_);
lean_dec(v_brecOnName_3827_);
lean_dec(v_levelParams_3826_);
lean_dec(v_brecOnGoName_3825_);
lean_dec(v_recName_3824_);
lean_dec(v_tail_3823_);
lean_dec(v_head_3822_);
lean_dec_ref(v_all_3821_);
lean_dec(v___x_3820_);
v___x_3927_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3928_ = l_Lean_MessageData_ofExpr(v_type_3829_);
v___x_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3929_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = lean_array_to_list(v___x_3846_);
v___x_3933_ = lean_box(0);
v___x_3934_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3932_, v___x_3933_);
v___x_3935_ = l_Lean_MessageData_ofList(v___x_3934_);
v___x_3936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3931_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3936_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
return v___x_3937_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3938_ = _args[0];
lean_object* v_numMotives_3939_ = _args[1];
lean_object* v_numMinors_3940_ = _args[2];
lean_object* v___x_3941_ = _args[3];
lean_object* v_all_3942_ = _args[4];
lean_object* v_head_3943_ = _args[5];
lean_object* v_tail_3944_ = _args[6];
lean_object* v_recName_3945_ = _args[7];
lean_object* v_brecOnGoName_3946_ = _args[8];
lean_object* v_levelParams_3947_ = _args[9];
lean_object* v_brecOnName_3948_ = _args[10];
lean_object* v_brecOnEqName_3949_ = _args[11];
lean_object* v_type_3950_ = _args[12];
lean_object* v_refArgs_3951_ = _args[13];
lean_object* v_refBody_3952_ = _args[14];
lean_object* v___y_3953_ = _args[15];
lean_object* v___y_3954_ = _args[16];
lean_object* v___y_3955_ = _args[17];
lean_object* v___y_3956_ = _args[18];
lean_object* v___y_3957_ = _args[19];
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3938_, v_numMotives_3939_, v_numMinors_3940_, v___x_3941_, v_all_3942_, v_head_3943_, v_tail_3944_, v_recName_3945_, v_brecOnGoName_3946_, v_levelParams_3947_, v_brecOnName_3948_, v_brecOnEqName_3949_, v_type_3950_, v_refArgs_3951_, v_refBody_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec_ref(v_refBody_3952_);
lean_dec(v_numMinors_3940_);
lean_dec(v_numMotives_3939_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3961_, lean_object* v_nParams_3962_, lean_object* v_all_3963_, lean_object* v_brecOnName_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___x_3970_; 
lean_inc_ref(v_a_3967_);
lean_inc(v_recName_3961_);
v___x_3970_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3961_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_4002_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3973_ = v___x_3970_;
v_isShared_3974_ = v_isSharedCheck_4002_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3970_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_4002_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
if (lean_obj_tag(v_a_3971_) == 7)
{
lean_object* v_val_3975_; lean_object* v_toConstantVal_3976_; lean_object* v_numMotives_3977_; lean_object* v_numMinors_3978_; lean_object* v_levelParams_3979_; lean_object* v_type_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; 
lean_del_object(v___x_3973_);
v_val_3975_ = lean_ctor_get(v_a_3971_, 0);
lean_inc_ref(v_val_3975_);
lean_dec_ref(v_a_3971_);
v_toConstantVal_3976_ = lean_ctor_get(v_val_3975_, 0);
lean_inc_ref(v_toConstantVal_3976_);
v_numMotives_3977_ = lean_ctor_get(v_val_3975_, 4);
lean_inc(v_numMotives_3977_);
v_numMinors_3978_ = lean_ctor_get(v_val_3975_, 5);
lean_inc(v_numMinors_3978_);
lean_dec_ref(v_val_3975_);
v_levelParams_3979_ = lean_ctor_get(v_toConstantVal_3976_, 1);
lean_inc(v_levelParams_3979_);
v_type_3980_ = lean_ctor_get(v_toConstantVal_3976_, 2);
lean_inc_ref(v_type_3980_);
lean_dec_ref(v_toConstantVal_3976_);
v___x_3981_ = lean_box(0);
lean_inc(v_levelParams_3979_);
v___x_3982_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3979_, v___x_3981_);
if (lean_obj_tag(v___x_3982_) == 1)
{
lean_object* v_head_3983_; lean_object* v_tail_3984_; lean_object* v___x_3985_; lean_object* v_brecOnGoName_3986_; lean_object* v___x_3987_; lean_object* v_brecOnEqName_3988_; lean_object* v___f_3989_; uint8_t v___x_3990_; lean_object* v___x_3991_; 
v_head_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_head_3983_);
v_tail_3984_ = lean_ctor_get(v___x_3982_, 1);
lean_inc(v_tail_3984_);
v___x_3985_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc(v_brecOnName_3964_);
v_brecOnGoName_3986_ = l_Lean_Name_str___override(v_brecOnName_3964_, v___x_3985_);
v___x_3987_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
lean_inc(v_brecOnName_3964_);
v_brecOnEqName_3988_ = l_Lean_Name_str___override(v_brecOnName_3964_, v___x_3987_);
lean_inc_ref(v_type_3980_);
v___f_3989_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 20, 13);
lean_closure_set(v___f_3989_, 0, v_nParams_3962_);
lean_closure_set(v___f_3989_, 1, v_numMotives_3977_);
lean_closure_set(v___f_3989_, 2, v_numMinors_3978_);
lean_closure_set(v___f_3989_, 3, v___x_3982_);
lean_closure_set(v___f_3989_, 4, v_all_3963_);
lean_closure_set(v___f_3989_, 5, v_head_3983_);
lean_closure_set(v___f_3989_, 6, v_tail_3984_);
lean_closure_set(v___f_3989_, 7, v_recName_3961_);
lean_closure_set(v___f_3989_, 8, v_brecOnGoName_3986_);
lean_closure_set(v___f_3989_, 9, v_levelParams_3979_);
lean_closure_set(v___f_3989_, 10, v_brecOnName_3964_);
lean_closure_set(v___f_3989_, 11, v_brecOnEqName_3988_);
lean_closure_set(v___f_3989_, 12, v_type_3980_);
v___x_3990_ = 0;
v___x_3991_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3980_, v___f_3989_, v___x_3990_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
return v___x_3991_;
}
else
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
lean_dec(v___x_3982_);
lean_dec_ref(v_type_3980_);
lean_dec(v_levelParams_3979_);
lean_dec(v_numMinors_3978_);
lean_dec(v_numMotives_3977_);
lean_dec(v_brecOnName_3964_);
lean_dec_ref(v_all_3963_);
lean_dec(v_nParams_3962_);
v___x_3992_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3993_ = l_Lean_MessageData_ofName(v_recName_3961_);
v___x_3994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3996_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
return v___x_3997_;
}
}
else
{
lean_object* v___x_3998_; lean_object* v___x_4000_; 
lean_dec(v_a_3971_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_brecOnName_3964_);
lean_dec_ref(v_all_3963_);
lean_dec(v_nParams_3962_);
lean_dec(v_recName_3961_);
v___x_3998_ = lean_box(0);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 0, v___x_3998_);
v___x_4000_ = v___x_3973_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3998_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_brecOnName_3964_);
lean_dec_ref(v_all_3963_);
lean_dec(v_nParams_3962_);
lean_dec(v_recName_3961_);
v_a_4003_ = lean_ctor_get(v___x_3970_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3970_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3970_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_4011_, lean_object* v_nParams_4012_, lean_object* v_all_4013_, lean_object* v_brecOnName_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_4011_, v_nParams_4012_, v_all_4013_, v_brecOnName_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_00_u03b1_4021_, lean_object* v_inst_4022_, lean_object* v_declInfos_4023_, lean_object* v_k_4024_, uint8_t v_kind_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v___x_4031_; 
v___x_4031_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(v_inst_4022_, v_declInfos_4023_, v_k_4024_, v_kind_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_00_u03b1_4032_, lean_object* v_inst_4033_, lean_object* v_declInfos_4034_, lean_object* v_k_4035_, lean_object* v_kind_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
uint8_t v_kind_boxed_4042_; lean_object* v_res_4043_; 
v_kind_boxed_4042_ = lean_unbox(v_kind_4036_);
v_res_4043_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_00_u03b1_4032_, v_inst_4033_, v_declInfos_4034_, v_k_4035_, v_kind_boxed_4042_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_00_u03b1_4044_, lean_object* v_inst_4045_, lean_object* v_declInfos_4046_, lean_object* v_k_4047_, uint8_t v_kind_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; 
v___x_4054_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(v_inst_4045_, v_declInfos_4046_, v_k_4047_, v_kind_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_);
return v___x_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4055_, lean_object* v_inst_4056_, lean_object* v_declInfos_4057_, lean_object* v_k_4058_, lean_object* v_kind_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
uint8_t v_kind_boxed_4065_; lean_object* v_res_4066_; 
v_kind_boxed_4065_ = lean_unbox(v_kind_4059_);
v_res_4066_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_00_u03b1_4055_, v_inst_4056_, v_declInfos_4057_, v_k_4058_, v_kind_boxed_4065_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_00_u03b1_4067_, lean_object* v_acc_4068_, lean_object* v_declInfos_4069_, lean_object* v_k_4070_, uint8_t v_kind_4071_, lean_object* v_inst_4072_, lean_object* v_name_4073_, uint8_t v_bi_4074_, lean_object* v_type_4075_, uint8_t v_kind_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v___x_4082_; 
v___x_4082_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(v_acc_4068_, v_declInfos_4069_, v_k_4070_, v_kind_4071_, v_inst_4072_, v_name_4073_, v_bi_4074_, v_type_4075_, v_kind_4076_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4083_, lean_object* v_acc_4084_, lean_object* v_declInfos_4085_, lean_object* v_k_4086_, lean_object* v_kind_4087_, lean_object* v_inst_4088_, lean_object* v_name_4089_, lean_object* v_bi_4090_, lean_object* v_type_4091_, lean_object* v_kind_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
uint8_t v_kind_boxed_4098_; uint8_t v_bi_boxed_4099_; uint8_t v_kind_boxed_4100_; lean_object* v_res_4101_; 
v_kind_boxed_4098_ = lean_unbox(v_kind_4087_);
v_bi_boxed_4099_ = lean_unbox(v_bi_4090_);
v_kind_boxed_4100_ = lean_unbox(v_kind_4092_);
v_res_4101_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_00_u03b1_4083_, v_acc_4084_, v_declInfos_4085_, v_k_4086_, v_kind_boxed_4098_, v_inst_4088_, v_name_4089_, v_bi_boxed_4099_, v_type_4091_, v_kind_boxed_4100_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_00_u03b1_4102_, lean_object* v_declInfos_4103_, lean_object* v_k_4104_, uint8_t v_kind_4105_, lean_object* v_inst_4106_, lean_object* v_acc_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_){
_start:
{
lean_object* v___x_4113_; 
v___x_4113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_4103_, v_k_4104_, v_kind_4105_, v_inst_4106_, v_acc_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
return v___x_4113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_00_u03b1_4114_, lean_object* v_declInfos_4115_, lean_object* v_k_4116_, lean_object* v_kind_4117_, lean_object* v_inst_4118_, lean_object* v_acc_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
uint8_t v_kind_boxed_4125_; lean_object* v_res_4126_; 
v_kind_boxed_4125_ = lean_unbox(v_kind_4117_);
v_res_4126_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_00_u03b1_4114_, v_declInfos_4115_, v_k_4116_, v_kind_boxed_4125_, v_inst_4118_, v_acc_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_4127_, lean_object* v___x_4128_, lean_object* v___x_4129_, lean_object* v___x_4130_, lean_object* v___x_4131_, lean_object* v_a_4132_, lean_object* v_b_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
uint8_t v___x_4139_; 
v___x_4139_ = lean_nat_dec_lt(v_a_4132_, v_upperBound_4127_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; 
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v_a_4132_);
lean_dec_ref(v___x_4131_);
lean_dec(v___x_4130_);
lean_dec(v___x_4129_);
lean_dec(v___x_4128_);
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v_b_4133_);
return v___x_4140_;
}
else
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v___x_4141_ = lean_unsigned_to_nat(1u);
v___x_4142_ = lean_nat_add(v_a_4132_, v___x_4141_);
lean_dec(v_a_4132_);
lean_inc(v___x_4142_);
lean_inc(v___x_4128_);
v___x_4143_ = lean_name_append_index_after(v___x_4128_, v___x_4142_);
lean_inc(v___x_4142_);
lean_inc(v___x_4129_);
v___x_4144_ = lean_name_append_index_after(v___x_4129_, v___x_4142_);
lean_inc(v___y_4137_);
lean_inc_ref(v___y_4136_);
lean_inc(v___y_4135_);
lean_inc_ref(v___y_4134_);
lean_inc_ref(v___x_4131_);
lean_inc(v___x_4130_);
v___x_4145_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4143_, v___x_4130_, v___x_4131_, v___x_4144_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v___x_4146_; 
lean_dec_ref(v___x_4145_);
v___x_4146_ = lean_box(0);
v_a_4132_ = v___x_4142_;
v_b_4133_ = v___x_4146_;
goto _start;
}
else
{
lean_dec(v___x_4142_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec_ref(v___x_4131_);
lean_dec(v___x_4130_);
lean_dec(v___x_4129_);
lean_dec(v___x_4128_);
return v___x_4145_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_4148_, lean_object* v___x_4149_, lean_object* v___x_4150_, lean_object* v___x_4151_, lean_object* v___x_4152_, lean_object* v_a_4153_, lean_object* v_b_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v_res_4160_; 
v_res_4160_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4148_, v___x_4149_, v___x_4150_, v___x_4151_, v___x_4152_, v_a_4153_, v_b_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_);
lean_dec(v_upperBound_4148_);
return v_res_4160_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_options_4171_; uint8_t v_hasTrace_4172_; 
v_options_4171_ = lean_ctor_get(v_a_4168_, 2);
v_hasTrace_4172_ = lean_ctor_get_uint8(v_options_4171_, sizeof(void*)*1);
if (v_hasTrace_4172_ == 0)
{
lean_object* v___x_4173_; 
lean_inc_ref(v_a_4168_);
lean_inc(v_indName_4165_);
v___x_4173_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4239_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4176_ = v___x_4173_;
v_isShared_4177_ = v_isSharedCheck_4239_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4239_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
if (lean_obj_tag(v_a_4174_) == 5)
{
lean_object* v_val_4178_; uint8_t v_isRec_4179_; 
v_val_4178_ = lean_ctor_get(v_a_4174_, 0);
lean_inc_ref(v_val_4178_);
lean_dec_ref(v_a_4174_);
v_isRec_4179_ = lean_ctor_get_uint8(v_val_4178_, sizeof(void*)*6);
if (v_isRec_4179_ == 0)
{
lean_object* v___x_4180_; lean_object* v___x_4182_; 
lean_dec_ref(v_val_4178_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v___x_4180_ = lean_box(0);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4180_);
v___x_4182_ = v___x_4176_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4180_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
}
}
else
{
lean_object* v_toConstantVal_4184_; lean_object* v_numParams_4185_; lean_object* v_all_4186_; lean_object* v_numNested_4187_; lean_object* v_type_4188_; lean_object* v___x_4189_; 
lean_del_object(v___x_4176_);
v_toConstantVal_4184_ = lean_ctor_get(v_val_4178_, 0);
lean_inc_ref(v_toConstantVal_4184_);
v_numParams_4185_ = lean_ctor_get(v_val_4178_, 1);
lean_inc(v_numParams_4185_);
v_all_4186_ = lean_ctor_get(v_val_4178_, 3);
lean_inc(v_all_4186_);
v_numNested_4187_ = lean_ctor_get(v_val_4178_, 5);
lean_inc(v_numNested_4187_);
lean_dec_ref(v_val_4178_);
v_type_4188_ = lean_ctor_get(v_toConstantVal_4184_, 2);
lean_inc_ref(v_type_4188_);
lean_dec_ref(v_toConstantVal_4184_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
v___x_4189_ = l_Lean_Meta_isPropFormerType(v_type_4188_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4226_; 
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4192_ = v___x_4189_;
v_isShared_4193_ = v_isSharedCheck_4226_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4189_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4226_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
uint8_t v___x_4194_; 
v___x_4194_ = lean_unbox(v_a_4190_);
lean_dec(v_a_4190_);
if (v___x_4194_ == 0)
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
lean_del_object(v___x_4192_);
lean_inc(v_indName_4165_);
v___x_4195_ = l_Lean_mkRecName(v_indName_4165_);
lean_inc(v_indName_4165_);
v___x_4196_ = l_Lean_mkBRecOnName(v_indName_4165_);
lean_inc(v_all_4186_);
v___x_4197_ = lean_array_mk(v_all_4186_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
lean_inc(v___x_4196_);
lean_inc_ref(v___x_4197_);
lean_inc(v_numParams_4185_);
lean_inc(v___x_4195_);
v___x_4198_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4195_, v_numParams_4185_, v___x_4197_, v___x_4196_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4220_; 
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4220_ == 0)
{
lean_object* v_unused_4221_; 
v_unused_4221_ = lean_ctor_get(v___x_4198_, 0);
lean_dec(v_unused_4221_);
v___x_4200_ = v___x_4198_;
v_isShared_4201_ = v_isSharedCheck_4220_;
goto v_resetjp_4199_;
}
else
{
lean_dec(v___x_4198_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4220_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4202_ = lean_box(0);
v___x_4203_ = lean_unsigned_to_nat(0u);
v___x_4204_ = l_List_get_x21Internal___redArg(v___x_4202_, v_all_4186_, v___x_4203_);
lean_dec(v_all_4186_);
v___x_4205_ = lean_name_eq(v___x_4204_, v_indName_4165_);
lean_dec(v_indName_4165_);
lean_dec(v___x_4204_);
if (v___x_4205_ == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4208_; 
lean_dec_ref(v___x_4197_);
lean_dec(v___x_4196_);
lean_dec(v___x_4195_);
lean_dec(v_numNested_4187_);
lean_dec(v_numParams_4185_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
v___x_4206_ = lean_box(0);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4206_);
v___x_4208_ = v___x_4200_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
else
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_del_object(v___x_4200_);
v___x_4210_ = lean_box(0);
v___x_4211_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4187_, v___x_4195_, v___x_4196_, v_numParams_4185_, v___x_4197_, v___x_4203_, v___x_4210_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_numNested_4187_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4218_ == 0)
{
lean_object* v_unused_4219_; 
v_unused_4219_ = lean_ctor_get(v___x_4211_, 0);
lean_dec(v_unused_4219_);
v___x_4213_ = v___x_4211_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_dec(v___x_4211_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4210_);
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v___x_4210_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
else
{
return v___x_4211_;
}
}
}
}
else
{
lean_dec_ref(v___x_4197_);
lean_dec(v___x_4196_);
lean_dec(v___x_4195_);
lean_dec(v_numNested_4187_);
lean_dec(v_all_4186_);
lean_dec(v_numParams_4185_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
return v___x_4198_;
}
}
else
{
lean_object* v___x_4222_; lean_object* v___x_4224_; 
lean_dec(v_numNested_4187_);
lean_dec(v_all_4186_);
lean_dec(v_numParams_4185_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v___x_4222_ = lean_box(0);
if (v_isShared_4193_ == 0)
{
lean_ctor_set(v___x_4192_, 0, v___x_4222_);
v___x_4224_ = v___x_4192_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_numNested_4187_);
lean_dec(v_all_4186_);
lean_dec(v_numParams_4185_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v_a_4227_ = lean_ctor_get(v___x_4189_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4189_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4189_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4189_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
else
{
lean_object* v___x_4235_; lean_object* v___x_4237_; 
lean_dec(v_a_4174_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v___x_4235_ = lean_box(0);
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___x_4235_);
v___x_4237_ = v___x_4176_;
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
}
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v_a_4240_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4173_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4173_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4454_; 
v___x_4248_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4249_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v___x_4248_, v_a_4168_);
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4252_ = v___x_4249_;
v_isShared_4253_ = v_isSharedCheck_4454_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4249_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4454_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___f_4254_; lean_object* v___x_4255_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v_a_4259_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v_a_4275_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v_a_4282_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v_a_4287_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v_a_4300_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v_a_4305_; uint8_t v___x_4376_; 
lean_inc(v_indName_4165_);
v___f_4254_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4254_, 0, v_indName_4165_);
v___x_4255_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4376_ = lean_unbox(v_a_4250_);
if (v___x_4376_ == 0)
{
lean_object* v___x_4377_; uint8_t v___x_4378_; 
v___x_4377_ = l_Lean_trace_profiler;
v___x_4378_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_4171_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4379_; 
lean_dec_ref(v___f_4254_);
lean_del_object(v___x_4252_);
lean_dec(v_a_4250_);
lean_inc_ref(v_a_4168_);
lean_inc(v_indName_4165_);
v___x_4379_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4445_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4382_ = v___x_4379_;
v_isShared_4383_ = v_isSharedCheck_4445_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4379_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4445_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
if (lean_obj_tag(v_a_4380_) == 5)
{
lean_object* v_val_4384_; uint8_t v_isRec_4385_; 
v_val_4384_ = lean_ctor_get(v_a_4380_, 0);
lean_inc_ref(v_val_4384_);
lean_dec_ref(v_a_4380_);
v_isRec_4385_ = lean_ctor_get_uint8(v_val_4384_, sizeof(void*)*6);
if (v_isRec_4385_ == 0)
{
lean_object* v___x_4386_; lean_object* v___x_4388_; 
lean_dec_ref(v_val_4384_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v___x_4386_ = lean_box(0);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4386_);
v___x_4388_ = v___x_4382_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
else
{
lean_object* v_toConstantVal_4390_; lean_object* v_numParams_4391_; lean_object* v_all_4392_; lean_object* v_numNested_4393_; lean_object* v_type_4394_; lean_object* v___x_4395_; 
lean_del_object(v___x_4382_);
v_toConstantVal_4390_ = lean_ctor_get(v_val_4384_, 0);
lean_inc_ref(v_toConstantVal_4390_);
v_numParams_4391_ = lean_ctor_get(v_val_4384_, 1);
lean_inc(v_numParams_4391_);
v_all_4392_ = lean_ctor_get(v_val_4384_, 3);
lean_inc(v_all_4392_);
v_numNested_4393_ = lean_ctor_get(v_val_4384_, 5);
lean_inc(v_numNested_4393_);
lean_dec_ref(v_val_4384_);
v_type_4394_ = lean_ctor_get(v_toConstantVal_4390_, 2);
lean_inc_ref(v_type_4394_);
lean_dec_ref(v_toConstantVal_4390_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
v___x_4395_ = l_Lean_Meta_isPropFormerType(v_type_4394_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4432_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4398_ = v___x_4395_;
v_isShared_4399_ = v_isSharedCheck_4432_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___x_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4432_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
uint8_t v___x_4400_; 
v___x_4400_ = lean_unbox(v_a_4396_);
lean_dec(v_a_4396_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
lean_del_object(v___x_4398_);
lean_inc(v_indName_4165_);
v___x_4401_ = l_Lean_mkRecName(v_indName_4165_);
lean_inc(v_indName_4165_);
v___x_4402_ = l_Lean_mkBRecOnName(v_indName_4165_);
lean_inc(v_all_4392_);
v___x_4403_ = lean_array_mk(v_all_4392_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
lean_inc(v___x_4402_);
lean_inc_ref(v___x_4403_);
lean_inc(v_numParams_4391_);
lean_inc(v___x_4401_);
v___x_4404_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4401_, v_numParams_4391_, v___x_4403_, v___x_4402_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4426_; 
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4426_ == 0)
{
lean_object* v_unused_4427_; 
v_unused_4427_ = lean_ctor_get(v___x_4404_, 0);
lean_dec(v_unused_4427_);
v___x_4406_ = v___x_4404_;
v_isShared_4407_ = v_isSharedCheck_4426_;
goto v_resetjp_4405_;
}
else
{
lean_dec(v___x_4404_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4426_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; uint8_t v___x_4411_; 
v___x_4408_ = lean_box(0);
v___x_4409_ = lean_unsigned_to_nat(0u);
v___x_4410_ = l_List_get_x21Internal___redArg(v___x_4408_, v_all_4392_, v___x_4409_);
lean_dec(v_all_4392_);
v___x_4411_ = lean_name_eq(v___x_4410_, v_indName_4165_);
lean_dec(v_indName_4165_);
lean_dec(v___x_4410_);
if (v___x_4411_ == 0)
{
lean_object* v___x_4412_; lean_object* v___x_4414_; 
lean_dec_ref(v___x_4403_);
lean_dec(v___x_4402_);
lean_dec(v___x_4401_);
lean_dec(v_numNested_4393_);
lean_dec(v_numParams_4391_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
v___x_4412_ = lean_box(0);
if (v_isShared_4407_ == 0)
{
lean_ctor_set(v___x_4406_, 0, v___x_4412_);
v___x_4414_ = v___x_4406_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4417_; 
lean_del_object(v___x_4406_);
v___x_4416_ = lean_box(0);
v___x_4417_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4393_, v___x_4401_, v___x_4402_, v_numParams_4391_, v___x_4403_, v___x_4409_, v___x_4416_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_numNested_4393_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4424_ == 0)
{
lean_object* v_unused_4425_; 
v_unused_4425_ = lean_ctor_get(v___x_4417_, 0);
lean_dec(v_unused_4425_);
v___x_4419_ = v___x_4417_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_dec(v___x_4417_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 0, v___x_4416_);
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4416_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
else
{
return v___x_4417_;
}
}
}
}
else
{
lean_dec_ref(v___x_4403_);
lean_dec(v___x_4402_);
lean_dec(v___x_4401_);
lean_dec(v_numNested_4393_);
lean_dec(v_all_4392_);
lean_dec(v_numParams_4391_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
return v___x_4404_;
}
}
else
{
lean_object* v___x_4428_; lean_object* v___x_4430_; 
lean_dec(v_numNested_4393_);
lean_dec(v_all_4392_);
lean_dec(v_numParams_4391_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v___x_4428_ = lean_box(0);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v___x_4428_);
v___x_4430_ = v___x_4398_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_numNested_4393_);
lean_dec(v_all_4392_);
lean_dec(v_numParams_4391_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v_a_4433_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4395_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4395_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
else
{
lean_object* v___x_4441_; lean_object* v___x_4443_; 
lean_dec(v_a_4380_);
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v___x_4441_ = lean_box(0);
if (v_isShared_4383_ == 0)
{
lean_ctor_set(v___x_4382_, 0, v___x_4441_);
v___x_4443_ = v___x_4382_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_a_4169_);
lean_dec_ref(v_a_4168_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_indName_4165_);
v_a_4446_ = lean_ctor_get(v___x_4379_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4379_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4379_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4379_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
else
{
lean_inc_ref(v_options_4171_);
goto v___jp_4307_;
}
}
else
{
lean_inc_ref(v_options_4171_);
goto v___jp_4307_;
}
v___jp_4256_:
{
lean_object* v___x_4260_; double v___x_4261_; double v___x_4262_; double v___x_4263_; double v___x_4264_; double v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; 
v___x_4260_ = lean_io_mono_nanos_now();
v___x_4261_ = lean_float_of_nat(v___y_4258_);
v___x_4262_ = lean_float_once(&l_Lean_mkBelow___closed__4, &l_Lean_mkBelow___closed__4_once, _init_l_Lean_mkBelow___closed__4);
v___x_4263_ = lean_float_div(v___x_4261_, v___x_4262_);
v___x_4264_ = lean_float_of_nat(v___x_4260_);
v___x_4265_ = lean_float_div(v___x_4264_, v___x_4262_);
v___x_4266_ = lean_box_float(v___x_4263_);
v___x_4267_ = lean_box_float(v___x_4265_);
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4266_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v_a_4259_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = lean_unbox(v_a_4250_);
lean_dec(v_a_4250_);
v___x_4271_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_4248_, v_hasTrace_4172_, v___x_4255_, v_options_4171_, v___x_4270_, v___y_4257_, v___f_4254_, v___x_4269_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec_ref(v_options_4171_);
return v___x_4271_;
}
v___jp_4272_:
{
lean_object* v___x_4277_; 
if (v_isShared_4253_ == 0)
{
lean_ctor_set_tag(v___x_4252_, 1);
lean_ctor_set(v___x_4252_, 0, v_a_4275_);
v___x_4277_ = v___x_4252_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4275_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
v___y_4257_ = v___y_4273_;
v___y_4258_ = v___y_4274_;
v_a_4259_ = v___x_4277_;
goto v___jp_4256_;
}
}
v___jp_4279_:
{
lean_object* v___x_4283_; 
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v_a_4282_);
v___y_4257_ = v___y_4280_;
v___y_4258_ = v___y_4281_;
v_a_4259_ = v___x_4283_;
goto v___jp_4256_;
}
v___jp_4284_:
{
lean_object* v___x_4288_; double v___x_4289_; double v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; uint8_t v___x_4295_; lean_object* v___x_4296_; 
v___x_4288_ = lean_io_get_num_heartbeats();
v___x_4289_ = lean_float_of_nat(v___y_4286_);
v___x_4290_ = lean_float_of_nat(v___x_4288_);
v___x_4291_ = lean_box_float(v___x_4289_);
v___x_4292_ = lean_box_float(v___x_4290_);
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4291_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4294_, 0, v_a_4287_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = lean_unbox(v_a_4250_);
lean_dec(v_a_4250_);
v___x_4296_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_4248_, v_hasTrace_4172_, v___x_4255_, v_options_4171_, v___x_4295_, v___y_4285_, v___f_4254_, v___x_4294_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec_ref(v_options_4171_);
return v___x_4296_;
}
v___jp_4297_:
{
lean_object* v___x_4301_; 
v___x_4301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4301_, 0, v_a_4300_);
v___y_4285_ = v___y_4298_;
v___y_4286_ = v___y_4299_;
v_a_4287_ = v___x_4301_;
goto v___jp_4284_;
}
v___jp_4302_:
{
lean_object* v___x_4306_; 
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v_a_4305_);
v___y_4285_ = v___y_4303_;
v___y_4286_ = v___y_4304_;
v_a_4287_ = v___x_4306_;
goto v___jp_4284_;
}
v___jp_4307_:
{
lean_object* v___x_4308_; lean_object* v_a_4309_; lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4308_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v_a_4169_);
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref(v___x_4308_);
v___x_4310_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4311_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_4171_, v___x_4310_);
if (v___x_4311_ == 0)
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = lean_io_mono_nanos_now();
lean_inc_ref(v_a_4168_);
lean_inc(v_indName_4165_);
v___x_4313_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref(v___x_4313_);
if (lean_obj_tag(v_a_4314_) == 5)
{
lean_object* v_val_4315_; uint8_t v_isRec_4316_; 
v_val_4315_ = lean_ctor_get(v_a_4314_, 0);
lean_inc_ref(v_val_4315_);
lean_dec_ref(v_a_4314_);
v_isRec_4316_ = lean_ctor_get_uint8(v_val_4315_, sizeof(void*)*6);
if (v_isRec_4316_ == 0)
{
lean_object* v___x_4317_; 
lean_dec_ref(v_val_4315_);
lean_dec(v_indName_4165_);
v___x_4317_ = lean_box(0);
v___y_4273_ = v_a_4309_;
v___y_4274_ = v___x_4312_;
v_a_4275_ = v___x_4317_;
goto v___jp_4272_;
}
else
{
lean_object* v_toConstantVal_4318_; lean_object* v_numParams_4319_; lean_object* v_all_4320_; lean_object* v_numNested_4321_; lean_object* v_type_4322_; lean_object* v___x_4323_; 
v_toConstantVal_4318_ = lean_ctor_get(v_val_4315_, 0);
lean_inc_ref(v_toConstantVal_4318_);
v_numParams_4319_ = lean_ctor_get(v_val_4315_, 1);
lean_inc(v_numParams_4319_);
v_all_4320_ = lean_ctor_get(v_val_4315_, 3);
lean_inc(v_all_4320_);
v_numNested_4321_ = lean_ctor_get(v_val_4315_, 5);
lean_inc(v_numNested_4321_);
lean_dec_ref(v_val_4315_);
v_type_4322_ = lean_ctor_get(v_toConstantVal_4318_, 2);
lean_inc_ref(v_type_4322_);
lean_dec_ref(v_toConstantVal_4318_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
v___x_4323_ = l_Lean_Meta_isPropFormerType(v_type_4322_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; uint8_t v___x_4325_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref(v___x_4323_);
v___x_4325_ = lean_unbox(v_a_4324_);
lean_dec(v_a_4324_);
if (v___x_4325_ == 0)
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; 
lean_inc(v_indName_4165_);
v___x_4326_ = l_Lean_mkRecName(v_indName_4165_);
lean_inc(v_indName_4165_);
v___x_4327_ = l_Lean_mkBRecOnName(v_indName_4165_);
lean_inc(v_all_4320_);
v___x_4328_ = lean_array_mk(v_all_4320_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
lean_inc(v___x_4327_);
lean_inc_ref(v___x_4328_);
lean_inc(v_numParams_4319_);
lean_inc(v___x_4326_);
v___x_4329_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4326_, v_numParams_4319_, v___x_4328_, v___x_4327_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
lean_dec_ref(v___x_4329_);
v___x_4330_ = lean_box(0);
v___x_4331_ = lean_unsigned_to_nat(0u);
v___x_4332_ = l_List_get_x21Internal___redArg(v___x_4330_, v_all_4320_, v___x_4331_);
lean_dec(v_all_4320_);
v___x_4333_ = lean_name_eq(v___x_4332_, v_indName_4165_);
lean_dec(v_indName_4165_);
lean_dec(v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; 
lean_dec_ref(v___x_4328_);
lean_dec(v___x_4327_);
lean_dec(v___x_4326_);
lean_dec(v_numNested_4321_);
lean_dec(v_numParams_4319_);
v___x_4334_ = lean_box(0);
v___y_4273_ = v_a_4309_;
v___y_4274_ = v___x_4312_;
v_a_4275_ = v___x_4334_;
goto v___jp_4272_;
}
else
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_box(0);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
v___x_4336_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4321_, v___x_4326_, v___x_4327_, v_numParams_4319_, v___x_4328_, v___x_4331_, v___x_4335_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_numNested_4321_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_dec_ref(v___x_4336_);
v___y_4273_ = v_a_4309_;
v___y_4274_ = v___x_4312_;
v_a_4275_ = v___x_4335_;
goto v___jp_4272_;
}
else
{
lean_object* v_a_4337_; 
lean_del_object(v___x_4252_);
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref(v___x_4336_);
v___y_4280_ = v_a_4309_;
v___y_4281_ = v___x_4312_;
v_a_4282_ = v_a_4337_;
goto v___jp_4279_;
}
}
}
else
{
lean_dec_ref(v___x_4328_);
lean_dec(v___x_4327_);
lean_dec(v___x_4326_);
lean_dec(v_numNested_4321_);
lean_dec(v_all_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_indName_4165_);
if (lean_obj_tag(v___x_4329_) == 0)
{
lean_object* v_a_4338_; 
v_a_4338_ = lean_ctor_get(v___x_4329_, 0);
lean_inc(v_a_4338_);
lean_dec_ref(v___x_4329_);
v___y_4273_ = v_a_4309_;
v___y_4274_ = v___x_4312_;
v_a_4275_ = v_a_4338_;
goto v___jp_4272_;
}
else
{
lean_object* v_a_4339_; 
lean_del_object(v___x_4252_);
v_a_4339_ = lean_ctor_get(v___x_4329_, 0);
lean_inc(v_a_4339_);
lean_dec_ref(v___x_4329_);
v___y_4280_ = v_a_4309_;
v___y_4281_ = v___x_4312_;
v_a_4282_ = v_a_4339_;
goto v___jp_4279_;
}
}
}
else
{
lean_object* v___x_4340_; 
lean_dec(v_numNested_4321_);
lean_dec(v_all_4320_);
lean_dec(v_numParams_4319_);
lean_dec(v_indName_4165_);
v___x_4340_ = lean_box(0);
v___y_4273_ = v_a_4309_;
v___y_4274_ = v___x_4312_;
v_a_4275_ = v___x_4340_;
goto v___jp_4272_;
}
}
else
{
lean_object* v_a_4341_; 
lean_dec(v_numNested_4321_);
lean_dec(v_all_4320_);
lean_dec(v_numParams_4319_);
lean_del_object(v___x_4252_);
lean_dec(v_indName_4165_);
v_a_4341_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4341_);
lean_dec_ref(v___x_4323_);
v___y_4280_ = v_a_4309_;
v___y_4281_ = v___x_4312_;
v_a_4282_ = v_a_4341_;
goto v___jp_4279_;
}
}
}
else
{
lean_object* v___x_4342_; 
lean_dec(v_a_4314_);
lean_dec(v_indName_4165_);
v___x_4342_ = lean_box(0);
v___y_4273_ = v_a_4309_;
v___y_4274_ = v___x_4312_;
v_a_4275_ = v___x_4342_;
goto v___jp_4272_;
}
}
else
{
lean_object* v_a_4343_; 
lean_del_object(v___x_4252_);
lean_dec(v_indName_4165_);
v_a_4343_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4343_);
lean_dec_ref(v___x_4313_);
v___y_4280_ = v_a_4309_;
v___y_4281_ = v___x_4312_;
v_a_4282_ = v_a_4343_;
goto v___jp_4279_;
}
}
else
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
lean_del_object(v___x_4252_);
v___x_4344_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_a_4168_);
lean_inc(v_indName_4165_);
v___x_4345_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4345_) == 0)
{
lean_object* v_a_4346_; 
v_a_4346_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4346_);
lean_dec_ref(v___x_4345_);
if (lean_obj_tag(v_a_4346_) == 5)
{
lean_object* v_val_4347_; uint8_t v_isRec_4348_; 
v_val_4347_ = lean_ctor_get(v_a_4346_, 0);
lean_inc_ref(v_val_4347_);
lean_dec_ref(v_a_4346_);
v_isRec_4348_ = lean_ctor_get_uint8(v_val_4347_, sizeof(void*)*6);
if (v_isRec_4348_ == 0)
{
lean_object* v___x_4349_; 
lean_dec_ref(v_val_4347_);
lean_dec(v_indName_4165_);
v___x_4349_ = lean_box(0);
v___y_4298_ = v_a_4309_;
v___y_4299_ = v___x_4344_;
v_a_4300_ = v___x_4349_;
goto v___jp_4297_;
}
else
{
lean_object* v_toConstantVal_4350_; lean_object* v_numParams_4351_; lean_object* v_all_4352_; lean_object* v_numNested_4353_; lean_object* v_type_4354_; lean_object* v___x_4355_; 
v_toConstantVal_4350_ = lean_ctor_get(v_val_4347_, 0);
lean_inc_ref(v_toConstantVal_4350_);
v_numParams_4351_ = lean_ctor_get(v_val_4347_, 1);
lean_inc(v_numParams_4351_);
v_all_4352_ = lean_ctor_get(v_val_4347_, 3);
lean_inc(v_all_4352_);
v_numNested_4353_ = lean_ctor_get(v_val_4347_, 5);
lean_inc(v_numNested_4353_);
lean_dec_ref(v_val_4347_);
v_type_4354_ = lean_ctor_get(v_toConstantVal_4350_, 2);
lean_inc_ref(v_type_4354_);
lean_dec_ref(v_toConstantVal_4350_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
v___x_4355_ = l_Lean_Meta_isPropFormerType(v_type_4354_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; uint8_t v___x_4357_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref(v___x_4355_);
v___x_4357_ = lean_unbox(v_a_4356_);
lean_dec(v_a_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
lean_inc(v_indName_4165_);
v___x_4358_ = l_Lean_mkRecName(v_indName_4165_);
lean_inc(v_indName_4165_);
v___x_4359_ = l_Lean_mkBRecOnName(v_indName_4165_);
lean_inc(v_all_4352_);
v___x_4360_ = lean_array_mk(v_all_4352_);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
lean_inc(v___x_4359_);
lean_inc_ref(v___x_4360_);
lean_inc(v_numParams_4351_);
lean_inc(v___x_4358_);
v___x_4361_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4358_, v_numParams_4351_, v___x_4360_, v___x_4359_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
lean_dec_ref(v___x_4361_);
v___x_4362_ = lean_box(0);
v___x_4363_ = lean_unsigned_to_nat(0u);
v___x_4364_ = l_List_get_x21Internal___redArg(v___x_4362_, v_all_4352_, v___x_4363_);
lean_dec(v_all_4352_);
v___x_4365_ = lean_name_eq(v___x_4364_, v_indName_4165_);
lean_dec(v_indName_4165_);
lean_dec(v___x_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
lean_dec_ref(v___x_4360_);
lean_dec(v___x_4359_);
lean_dec(v___x_4358_);
lean_dec(v_numNested_4353_);
lean_dec(v_numParams_4351_);
v___x_4366_ = lean_box(0);
v___y_4298_ = v_a_4309_;
v___y_4299_ = v___x_4344_;
v_a_4300_ = v___x_4366_;
goto v___jp_4297_;
}
else
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = lean_box(0);
lean_inc(v_a_4169_);
lean_inc_ref(v_a_4168_);
lean_inc(v_a_4167_);
lean_inc_ref(v_a_4166_);
v___x_4368_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4353_, v___x_4358_, v___x_4359_, v_numParams_4351_, v___x_4360_, v___x_4363_, v___x_4367_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec(v_numNested_4353_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_dec_ref(v___x_4368_);
v___y_4298_ = v_a_4309_;
v___y_4299_ = v___x_4344_;
v_a_4300_ = v___x_4367_;
goto v___jp_4297_;
}
else
{
lean_object* v_a_4369_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref(v___x_4368_);
v___y_4303_ = v_a_4309_;
v___y_4304_ = v___x_4344_;
v_a_4305_ = v_a_4369_;
goto v___jp_4302_;
}
}
}
else
{
lean_dec_ref(v___x_4360_);
lean_dec(v___x_4359_);
lean_dec(v___x_4358_);
lean_dec(v_numNested_4353_);
lean_dec(v_all_4352_);
lean_dec(v_numParams_4351_);
lean_dec(v_indName_4165_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4370_; 
v_a_4370_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4370_);
lean_dec_ref(v___x_4361_);
v___y_4298_ = v_a_4309_;
v___y_4299_ = v___x_4344_;
v_a_4300_ = v_a_4370_;
goto v___jp_4297_;
}
else
{
lean_object* v_a_4371_; 
v_a_4371_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4371_);
lean_dec_ref(v___x_4361_);
v___y_4303_ = v_a_4309_;
v___y_4304_ = v___x_4344_;
v_a_4305_ = v_a_4371_;
goto v___jp_4302_;
}
}
}
else
{
lean_object* v___x_4372_; 
lean_dec(v_numNested_4353_);
lean_dec(v_all_4352_);
lean_dec(v_numParams_4351_);
lean_dec(v_indName_4165_);
v___x_4372_ = lean_box(0);
v___y_4298_ = v_a_4309_;
v___y_4299_ = v___x_4344_;
v_a_4300_ = v___x_4372_;
goto v___jp_4297_;
}
}
else
{
lean_object* v_a_4373_; 
lean_dec(v_numNested_4353_);
lean_dec(v_all_4352_);
lean_dec(v_numParams_4351_);
lean_dec(v_indName_4165_);
v_a_4373_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4373_);
lean_dec_ref(v___x_4355_);
v___y_4303_ = v_a_4309_;
v___y_4304_ = v___x_4344_;
v_a_4305_ = v_a_4373_;
goto v___jp_4302_;
}
}
}
else
{
lean_object* v___x_4374_; 
lean_dec(v_a_4346_);
lean_dec(v_indName_4165_);
v___x_4374_ = lean_box(0);
v___y_4298_ = v_a_4309_;
v___y_4299_ = v___x_4344_;
v_a_4300_ = v___x_4374_;
goto v___jp_4297_;
}
}
else
{
lean_object* v_a_4375_; 
lean_dec(v_indName_4165_);
v_a_4375_ = lean_ctor_get(v___x_4345_, 0);
lean_inc(v_a_4375_);
lean_dec_ref(v___x_4345_);
v___y_4303_ = v_a_4309_;
v___y_4304_ = v___x_4344_;
v_a_4305_ = v_a_4375_;
goto v___jp_4302_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_){
_start:
{
lean_object* v_res_4461_; 
v_res_4461_ = l_Lean_mkBRecOn(v_indName_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4462_, lean_object* v___x_4463_, lean_object* v___x_4464_, lean_object* v___x_4465_, lean_object* v___x_4466_, lean_object* v_inst_4467_, lean_object* v_R_4468_, lean_object* v_a_4469_, lean_object* v_b_4470_, lean_object* v_c_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4462_, v___x_4463_, v___x_4464_, v___x_4465_, v___x_4466_, v_a_4469_, v_b_4470_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4478_, lean_object* v___x_4479_, lean_object* v___x_4480_, lean_object* v___x_4481_, lean_object* v___x_4482_, lean_object* v_inst_4483_, lean_object* v_R_4484_, lean_object* v_a_4485_, lean_object* v_b_4486_, lean_object* v_c_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_res_4493_; 
v_res_4493_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4478_, v___x_4479_, v___x_4480_, v___x_4481_, v___x_4482_, v_inst_4483_, v_R_4484_, v_a_4485_, v_b_4486_, v_c_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec(v_upperBound_4478_);
return v_res_4493_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v___x_4539_ = lean_unsigned_to_nat(2304625798u);
v___x_4540_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4541_ = l_Lean_Name_num___override(v___x_4540_, v___x_4539_);
return v___x_4541_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4543_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4544_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4545_ = l_Lean_Name_str___override(v___x_4544_, v___x_4543_);
return v___x_4545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4547_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4548_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4549_ = l_Lean_Name_str___override(v___x_4548_, v___x_4547_);
return v___x_4549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4550_ = lean_unsigned_to_nat(2u);
v___x_4551_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4552_ = l_Lean_Name_num___override(v___x_4551_, v___x_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4554_; uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v___x_4554_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4555_ = 0;
v___x_4556_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4557_ = l_Lean_registerTraceClass(v___x_4554_, v___x_4555_, v___x_4556_);
return v___x_4557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4559_;
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
