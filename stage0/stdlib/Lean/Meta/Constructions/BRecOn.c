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
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__5;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_2106__boxed_100_; lean_object* v_res_101_; 
v___x_2106__boxed_100_ = lean_unbox(v___x_92_);
v_res_101_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__0(v_rlvl_91_, v___x_2106__boxed_100_, v_args_93_, v_x_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
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
uint8_t v___x_2261__boxed_251_; uint8_t v___x_2262__boxed_252_; lean_object* v_res_253_; 
v___x_2261__boxed_251_ = lean_unbox(v___x_239_);
v___x_2262__boxed_252_ = lean_unbox(v___x_240_);
v_res_253_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go___lam__1(v_arg__args_237_, v_arg__type_238_, v___x_2261__boxed_251_, v___x_2262__boxed_252_, v_prods_241_, v_rlvl_242_, v_motives_243_, v_tail_244_, v_arg_x27_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
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
lean_dec_ref(v___x_270_);
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
lean_dec_ref(v___x_278_);
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
lean_dec_ref(v_a_314_);
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
lean_dec_ref(v___x_323_);
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
lean_object* v___f_435_; lean_object* v___x_4991__overap_436_; lean_object* v___x_437_; 
v___f_435_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_4991__overap_436_ = lean_panic_fn_borrowed(v___f_435_, v_msg_429_);
lean_inc(v___y_433_);
lean_inc_ref(v___y_432_);
lean_inc(v___y_431_);
lean_inc_ref(v___y_430_);
v___x_437_ = lean_apply_5(v___x_4991__overap_436_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, lean_box(0));
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
lean_dec_ref(v___x_511_);
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
uint8_t v___x_9199__boxed_555_; lean_object* v_res_556_; 
v___x_9199__boxed_555_ = lean_unbox(v___x_547_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__3___lam__0(v___x_546_, v___x_9199__boxed_555_, v_targs_548_, v_x_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
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
lean_dec_ref(v___x_570_);
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
lean_dec_ref(v___x_699_);
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
lean_dec_ref(v___x_714_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref(v___x_720_);
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
lean_object* v___x_828_; lean_object* v_env_829_; lean_object* v_nextMacroScope_830_; lean_object* v_ngen_831_; lean_object* v_auxDeclNGen_832_; lean_object* v_traceState_833_; lean_object* v_messages_834_; lean_object* v_infoState_835_; lean_object* v_snapshotTasks_836_; lean_object* v_newDecls_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_866_; 
v___x_828_ = lean_st_ref_take(v___y_826_);
v_env_829_ = lean_ctor_get(v___x_828_, 0);
v_nextMacroScope_830_ = lean_ctor_get(v___x_828_, 1);
v_ngen_831_ = lean_ctor_get(v___x_828_, 2);
v_auxDeclNGen_832_ = lean_ctor_get(v___x_828_, 3);
v_traceState_833_ = lean_ctor_get(v___x_828_, 4);
v_messages_834_ = lean_ctor_get(v___x_828_, 6);
v_infoState_835_ = lean_ctor_get(v___x_828_, 7);
v_snapshotTasks_836_ = lean_ctor_get(v___x_828_, 8);
v_newDecls_837_ = lean_ctor_get(v___x_828_, 9);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v___x_828_, 5);
lean_dec(v_unused_867_);
v___x_839_ = v___x_828_;
v_isShared_840_ = v_isSharedCheck_866_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_newDecls_837_);
lean_inc(v_snapshotTasks_836_);
lean_inc(v_infoState_835_);
lean_inc(v_messages_834_);
lean_inc(v_traceState_833_);
lean_inc(v_auxDeclNGen_832_);
lean_inc(v_ngen_831_);
lean_inc(v_nextMacroScope_830_);
lean_inc(v_env_829_);
lean_dec(v___x_828_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_866_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_841_ = 0;
v___x_842_ = lean_box(0);
v___x_843_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_829_, v_declName_823_, v_s_824_, v___x_841_, v___x_842_);
v___x_844_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 5, v___x_844_);
lean_ctor_set(v___x_839_, 0, v___x_843_);
v___x_846_ = v___x_839_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_nextMacroScope_830_);
lean_ctor_set(v_reuseFailAlloc_865_, 2, v_ngen_831_);
lean_ctor_set(v_reuseFailAlloc_865_, 3, v_auxDeclNGen_832_);
lean_ctor_set(v_reuseFailAlloc_865_, 4, v_traceState_833_);
lean_ctor_set(v_reuseFailAlloc_865_, 5, v___x_844_);
lean_ctor_set(v_reuseFailAlloc_865_, 6, v_messages_834_);
lean_ctor_set(v_reuseFailAlloc_865_, 7, v_infoState_835_);
lean_ctor_set(v_reuseFailAlloc_865_, 8, v_snapshotTasks_836_);
lean_ctor_set(v_reuseFailAlloc_865_, 9, v_newDecls_837_);
v___x_846_ = v_reuseFailAlloc_865_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v_mctx_849_; lean_object* v_zetaDeltaFVarIds_850_; lean_object* v_postponed_851_; lean_object* v_diag_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_863_; 
v___x_847_ = lean_st_ref_set(v___y_826_, v___x_846_);
v___x_848_ = lean_st_ref_take(v___y_825_);
v_mctx_849_ = lean_ctor_get(v___x_848_, 0);
v_zetaDeltaFVarIds_850_ = lean_ctor_get(v___x_848_, 2);
v_postponed_851_ = lean_ctor_get(v___x_848_, 3);
v_diag_852_ = lean_ctor_get(v___x_848_, 4);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_863_ == 0)
{
lean_object* v_unused_864_; 
v_unused_864_ = lean_ctor_get(v___x_848_, 1);
lean_dec(v_unused_864_);
v___x_854_ = v___x_848_;
v_isShared_855_ = v_isSharedCheck_863_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_diag_852_);
lean_inc(v_postponed_851_);
lean_inc(v_zetaDeltaFVarIds_850_);
lean_inc(v_mctx_849_);
lean_dec(v___x_848_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_863_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_mctx_849_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_zetaDeltaFVarIds_850_);
lean_ctor_set(v_reuseFailAlloc_862_, 3, v_postponed_851_);
lean_ctor_set(v_reuseFailAlloc_862_, 4, v_diag_852_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_st_ref_set(v___y_825_, v___x_858_);
v___x_860_ = lean_box(0);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___boxed(lean_object* v_declName_868_, lean_object* v_s_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
uint8_t v_s_boxed_873_; lean_object* v_res_874_; 
v_s_boxed_873_ = lean_unbox(v_s_869_);
v_res_874_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_868_, v_s_boxed_873_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec(v___y_870_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(lean_object* v_declName_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v___x_881_; lean_object* v___x_882_; 
v___x_881_ = 0;
v___x_882_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg(v_declName_875_, v___x_881_, v___y_877_, v___y_879_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7___boxed(lean_object* v_declName_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_declName_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(lean_object* v_ref_890_, lean_object* v_msg_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_fileName_897_; lean_object* v_fileMap_898_; lean_object* v_options_899_; lean_object* v_currRecDepth_900_; lean_object* v_maxRecDepth_901_; lean_object* v_ref_902_; lean_object* v_currNamespace_903_; lean_object* v_openDecls_904_; lean_object* v_initHeartbeats_905_; lean_object* v_maxHeartbeats_906_; lean_object* v_quotContext_907_; lean_object* v_currMacroScope_908_; uint8_t v_diag_909_; lean_object* v_cancelTk_x3f_910_; uint8_t v_suppressElabErrors_911_; lean_object* v_inheritedTraceOptions_912_; lean_object* v_ref_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v_fileName_897_ = lean_ctor_get(v___y_894_, 0);
v_fileMap_898_ = lean_ctor_get(v___y_894_, 1);
v_options_899_ = lean_ctor_get(v___y_894_, 2);
v_currRecDepth_900_ = lean_ctor_get(v___y_894_, 3);
v_maxRecDepth_901_ = lean_ctor_get(v___y_894_, 4);
v_ref_902_ = lean_ctor_get(v___y_894_, 5);
v_currNamespace_903_ = lean_ctor_get(v___y_894_, 6);
v_openDecls_904_ = lean_ctor_get(v___y_894_, 7);
v_initHeartbeats_905_ = lean_ctor_get(v___y_894_, 8);
v_maxHeartbeats_906_ = lean_ctor_get(v___y_894_, 9);
v_quotContext_907_ = lean_ctor_get(v___y_894_, 10);
v_currMacroScope_908_ = lean_ctor_get(v___y_894_, 11);
v_diag_909_ = lean_ctor_get_uint8(v___y_894_, sizeof(void*)*14);
v_cancelTk_x3f_910_ = lean_ctor_get(v___y_894_, 12);
v_suppressElabErrors_911_ = lean_ctor_get_uint8(v___y_894_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_912_ = lean_ctor_get(v___y_894_, 13);
v_ref_913_ = l_Lean_replaceRef(v_ref_890_, v_ref_902_);
lean_inc_ref(v_inheritedTraceOptions_912_);
lean_inc(v_cancelTk_x3f_910_);
lean_inc(v_currMacroScope_908_);
lean_inc(v_quotContext_907_);
lean_inc(v_maxHeartbeats_906_);
lean_inc(v_initHeartbeats_905_);
lean_inc(v_openDecls_904_);
lean_inc(v_currNamespace_903_);
lean_inc(v_maxRecDepth_901_);
lean_inc(v_currRecDepth_900_);
lean_inc_ref(v_options_899_);
lean_inc_ref(v_fileMap_898_);
lean_inc_ref(v_fileName_897_);
v___x_914_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_914_, 0, v_fileName_897_);
lean_ctor_set(v___x_914_, 1, v_fileMap_898_);
lean_ctor_set(v___x_914_, 2, v_options_899_);
lean_ctor_set(v___x_914_, 3, v_currRecDepth_900_);
lean_ctor_set(v___x_914_, 4, v_maxRecDepth_901_);
lean_ctor_set(v___x_914_, 5, v_ref_913_);
lean_ctor_set(v___x_914_, 6, v_currNamespace_903_);
lean_ctor_set(v___x_914_, 7, v_openDecls_904_);
lean_ctor_set(v___x_914_, 8, v_initHeartbeats_905_);
lean_ctor_set(v___x_914_, 9, v_maxHeartbeats_906_);
lean_ctor_set(v___x_914_, 10, v_quotContext_907_);
lean_ctor_set(v___x_914_, 11, v_currMacroScope_908_);
lean_ctor_set(v___x_914_, 12, v_cancelTk_x3f_910_);
lean_ctor_set(v___x_914_, 13, v_inheritedTraceOptions_912_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*14, v_diag_909_);
lean_ctor_set_uint8(v___x_914_, sizeof(void*)*14 + 1, v_suppressElabErrors_911_);
v___x_915_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v_msg_891_, v___y_892_, v___y_893_, v___x_914_, v___y_895_);
lean_dec_ref(v___x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg___boxed(lean_object* v_ref_916_, lean_object* v_msg_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_916_, v_msg_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v_ref_916_);
return v_res_923_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_924_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__0);
v___x_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
return v___x_926_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_929_, 0, v___x_928_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
lean_ctor_set(v___x_929_, 2, v___x_928_);
lean_ctor_set(v___x_929_, 3, v___x_928_);
lean_ctor_set(v___x_929_, 4, v___x_927_);
lean_ctor_set(v___x_929_, 5, v___x_927_);
lean_ctor_set(v___x_929_, 6, v___x_927_);
lean_ctor_set(v___x_929_, 7, v___x_927_);
lean_ctor_set(v___x_929_, 8, v___x_927_);
lean_ctor_set(v___x_929_, 9, v___x_927_);
return v___x_929_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_unsigned_to_nat(32u);
v___x_931_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_933_ = ((size_t)5ULL);
v___x_934_ = lean_unsigned_to_nat(0u);
v___x_935_ = lean_unsigned_to_nat(32u);
v___x_936_ = lean_mk_empty_array_with_capacity(v___x_935_);
v___x_937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__3);
v___x_938_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_934_);
lean_ctor_set(v___x_938_, 3, v___x_934_);
lean_ctor_set_usize(v___x_938_, 4, v___x_933_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_939_ = lean_box(1);
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__4);
v___x_941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__1);
v___x_942_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
lean_ctor_set(v___x_942_, 2, v___x_939_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__6));
v___x_945_ = l_Lean_stringToMessageData(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__8));
v___x_948_ = l_Lean_stringToMessageData(v___x_947_);
return v___x_948_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__10));
v___x_951_ = l_Lean_stringToMessageData(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__12));
v___x_954_ = l_Lean_stringToMessageData(v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__14));
v___x_957_ = l_Lean_stringToMessageData(v___x_956_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__16));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_962_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___closed__18));
v___x_963_ = l_Lean_stringToMessageData(v___x_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(lean_object* v_msg_964_, lean_object* v_declHint_965_, lean_object* v___y_966_){
_start:
{
lean_object* v___x_968_; lean_object* v_env_969_; uint8_t v___x_970_; 
v___x_968_ = lean_st_ref_get(v___y_966_);
v_env_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc_ref(v_env_969_);
lean_dec(v___x_968_);
v___x_970_ = l_Lean_Name_isAnonymous(v_declHint_965_);
if (v___x_970_ == 0)
{
uint8_t v_isExporting_971_; 
v_isExporting_971_ = lean_ctor_get_uint8(v_env_969_, sizeof(void*)*8);
if (v_isExporting_971_ == 0)
{
lean_object* v___x_972_; 
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_965_);
v___x_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_972_, 0, v_msg_964_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; uint8_t v___x_974_; 
lean_inc_ref(v_env_969_);
v___x_973_ = l_Lean_Environment_setExporting(v_env_969_, v___x_970_);
lean_inc(v_declHint_965_);
lean_inc_ref(v___x_973_);
v___x_974_ = l_Lean_Environment_contains(v___x_973_, v_declHint_965_, v_isExporting_971_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; 
lean_dec_ref(v___x_973_);
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_965_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v_msg_964_);
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
lean_inc(v_declHint_965_);
v___x_980_ = l_Lean_MessageData_ofConstName(v_declHint_965_, v___x_970_);
v_c_981_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_981_, 0, v___x_979_);
lean_ctor_set(v_c_981_, 1, v___x_980_);
v___x_982_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_969_, v_declHint_965_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_965_);
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
lean_ctor_set(v___x_988_, 0, v_msg_964_);
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
v___x_995_ = l_Lean_Environment_header(v_env_969_);
lean_dec_ref(v_env_969_);
v___x_996_ = l_Lean_EnvironmentHeader_moduleNames(v___x_995_);
v_mod_997_ = lean_array_get(v___x_994_, v___x_996_, v_val_990_);
lean_dec(v_val_990_);
lean_dec_ref(v___x_996_);
v___x_998_ = l_Lean_isPrivateName(v_declHint_965_);
lean_dec(v_declHint_965_);
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
lean_ctor_set(v___x_1008_, 0, v_msg_964_);
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
lean_ctor_set(v___x_1021_, 0, v_msg_964_);
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
else
{
lean_object* v___x_1026_; 
lean_dec_ref(v_env_969_);
lean_dec(v_declHint_965_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_msg_964_);
return v___x_1026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg___boxed(lean_object* v_msg_1027_, lean_object* v_declHint_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1027_, v_declHint_1028_, v___y_1029_);
lean_dec(v___y_1029_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(lean_object* v_msg_1032_, lean_object* v_declHint_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_){
_start:
{
lean_object* v___x_1039_; lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1049_; 
v___x_1039_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12_spec__13___redArg(v_msg_1032_, v_declHint_1033_, v___y_1037_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1044_ = l_Lean_unknownIdentifierMessageTag;
v___x_1045_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_a_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1045_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12___boxed(lean_object* v_msg_1050_, lean_object* v_declHint_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1050_, v_declHint_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
return v_res_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(lean_object* v_ref_1058_, lean_object* v_msg_1059_, lean_object* v_declHint_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v___x_1066_; lean_object* v_a_1067_; lean_object* v___x_1068_; 
v___x_1066_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__12(v_msg_1059_, v_declHint_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_a_1067_);
lean_dec_ref(v___x_1066_);
v___x_1068_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11_spec__13___redArg(v_ref_1058_, v_a_1067_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg___boxed(lean_object* v_ref_1069_, lean_object* v_msg_1070_, lean_object* v_declHint_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1069_, v_msg_1070_, v_declHint_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_ref_1069_);
return v_res_1077_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1079_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_1080_ = l_Lean_stringToMessageData(v___x_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__2));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(lean_object* v_ref_1084_, lean_object* v_constName_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1091_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__1);
v___x_1092_ = 0;
lean_inc(v_constName_1085_);
v___x_1093_ = l_Lean_MessageData_ofConstName(v_constName_1085_, v___x_1092_);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1091_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___closed__3);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3_spec__11___redArg(v_ref_1084_, v___x_1096_, v_constName_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_ref_1098_, lean_object* v_constName_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1098_, v_constName_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v_ref_1098_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(lean_object* v_constName_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_ref_1112_; lean_object* v___x_1113_; 
v_ref_1112_ = lean_ctor_get(v___y_1109_, 5);
v___x_1113_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0_spec__3___redArg(v_ref_1112_, v_constName_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(lean_object* v_constName_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v_env_1128_; uint8_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1127_ = lean_st_ref_get(v___y_1125_);
v_env_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc_ref(v_env_1128_);
lean_dec(v___x_1127_);
v___x_1129_ = 0;
lean_inc(v_constName_1121_);
v___x_1130_ = l_Lean_Environment_find_x3f(v_env_1128_, v_constName_1121_, v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0_spec__0___redArg(v_constName_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
return v___x_1131_;
}
else
{
lean_object* v_val_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_constName_1121_);
v_val_1132_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1130_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_val_1132_);
lean_dec(v___x_1130_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 0);
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_val_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0___boxed(lean_object* v_constName_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_constName_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
return v_res_1146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1(void){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1148_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__0));
v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__2));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5(void){
_start:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1154_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__4));
v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(lean_object* v_recName_1156_, lean_object* v_nParams_1157_, lean_object* v_belowName_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1164_; 
lean_inc(v_recName_1156_);
v___x_1164_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_1156_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref(v___x_1164_);
if (lean_obj_tag(v_a_1165_) == 7)
{
lean_object* v_val_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1283_; 
v_val_1166_ = lean_ctor_get(v_a_1165_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1168_ = v_a_1165_;
v_isShared_1169_ = v_isSharedCheck_1283_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_val_1166_);
lean_dec(v_a_1165_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1283_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_toConstantVal_1170_; lean_object* v_numMotives_1171_; lean_object* v_numMinors_1172_; lean_object* v_levelParams_1173_; lean_object* v_type_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_toConstantVal_1170_ = lean_ctor_get(v_val_1166_, 0);
lean_inc_ref(v_toConstantVal_1170_);
v_numMotives_1171_ = lean_ctor_get(v_val_1166_, 4);
lean_inc(v_numMotives_1171_);
v_numMinors_1172_ = lean_ctor_get(v_val_1166_, 5);
lean_inc(v_numMinors_1172_);
lean_dec_ref(v_val_1166_);
v_levelParams_1173_ = lean_ctor_get(v_toConstantVal_1170_, 1);
lean_inc_n(v_levelParams_1173_, 2);
v_type_1174_ = lean_ctor_get(v_toConstantVal_1170_, 2);
lean_inc_ref(v_type_1174_);
lean_dec_ref(v_toConstantVal_1170_);
v___x_1175_ = lean_box(0);
v___x_1176_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1173_, v___x_1175_);
if (lean_obj_tag(v___x_1176_) == 1)
{
lean_object* v_head_1177_; lean_object* v_tail_1178_; lean_object* v___f_1179_; uint8_t v___x_1180_; lean_object* v___x_1181_; 
v_head_1177_ = lean_ctor_get(v___x_1176_, 0);
lean_inc(v_head_1177_);
v_tail_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc(v_tail_1178_);
lean_dec_ref(v___x_1176_);
v___f_1179_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___boxed), 15, 8);
lean_closure_set(v___f_1179_, 0, v_nParams_1157_);
lean_closure_set(v___f_1179_, 1, v_numMotives_1171_);
lean_closure_set(v___f_1179_, 2, v_numMinors_1172_);
lean_closure_set(v___f_1179_, 3, v_head_1177_);
lean_closure_set(v___f_1179_, 4, v_tail_1178_);
lean_closure_set(v___f_1179_, 5, v_recName_1156_);
lean_closure_set(v___f_1179_, 6, v_belowName_1158_);
lean_closure_set(v___f_1179_, 7, v_levelParams_1173_);
v___x_1180_ = 0;
v___x_1181_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_1174_, v___f_1179_, v___x_1180_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v___x_1184_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_n(v_a_1182_, 2);
lean_dec_ref(v___x_1181_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 1);
lean_ctor_set(v___x_1168_, 0, v_a_1182_);
v___x_1184_ = v___x_1168_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1182_);
v___x_1184_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_addDecl(v___x_1184_, v___x_1180_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_toConstantVal_1186_; lean_object* v_name_1187_; lean_object* v___x_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1266_; 
lean_dec_ref(v___x_1185_);
v_toConstantVal_1186_ = lean_ctor_get(v_a_1182_, 0);
lean_inc_ref(v_toConstantVal_1186_);
lean_dec(v_a_1182_);
v_name_1187_ = lean_ctor_get(v_toConstantVal_1186_, 0);
lean_inc_n(v_name_1187_, 2);
lean_dec_ref(v_toConstantVal_1186_);
v___x_1188_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_1187_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1188_, 0);
lean_dec(v_unused_1267_);
v___x_1190_ = v___x_1188_;
v_isShared_1191_ = v_isSharedCheck_1266_;
goto v_resetjp_1189_;
}
else
{
lean_dec(v___x_1188_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1266_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v___x_1192_; lean_object* v_env_1193_; lean_object* v_nextMacroScope_1194_; lean_object* v_ngen_1195_; lean_object* v_auxDeclNGen_1196_; lean_object* v_traceState_1197_; lean_object* v_messages_1198_; lean_object* v_infoState_1199_; lean_object* v_snapshotTasks_1200_; lean_object* v_newDecls_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1264_; 
v___x_1192_ = lean_st_ref_take(v_a_1162_);
v_env_1193_ = lean_ctor_get(v___x_1192_, 0);
v_nextMacroScope_1194_ = lean_ctor_get(v___x_1192_, 1);
v_ngen_1195_ = lean_ctor_get(v___x_1192_, 2);
v_auxDeclNGen_1196_ = lean_ctor_get(v___x_1192_, 3);
v_traceState_1197_ = lean_ctor_get(v___x_1192_, 4);
v_messages_1198_ = lean_ctor_get(v___x_1192_, 6);
v_infoState_1199_ = lean_ctor_get(v___x_1192_, 7);
v_snapshotTasks_1200_ = lean_ctor_get(v___x_1192_, 8);
v_newDecls_1201_ = lean_ctor_get(v___x_1192_, 9);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1192_, 5);
lean_dec(v_unused_1265_);
v___x_1203_ = v___x_1192_;
v_isShared_1204_ = v_isSharedCheck_1264_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_newDecls_1201_);
lean_inc(v_snapshotTasks_1200_);
lean_inc(v_infoState_1199_);
lean_inc(v_messages_1198_);
lean_inc(v_traceState_1197_);
lean_inc(v_auxDeclNGen_1196_);
lean_inc(v_ngen_1195_);
lean_inc(v_nextMacroScope_1194_);
lean_inc(v_env_1193_);
lean_dec(v___x_1192_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1264_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_inc(v_name_1187_);
v___x_1205_ = l_Lean_markAuxRecursor(v_env_1193_, v_name_1187_);
v___x_1206_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 5, v___x_1206_);
lean_ctor_set(v___x_1203_, 0, v___x_1205_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v_nextMacroScope_1194_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_ngen_1195_);
lean_ctor_set(v_reuseFailAlloc_1263_, 3, v_auxDeclNGen_1196_);
lean_ctor_set(v_reuseFailAlloc_1263_, 4, v_traceState_1197_);
lean_ctor_set(v_reuseFailAlloc_1263_, 5, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1263_, 6, v_messages_1198_);
lean_ctor_set(v_reuseFailAlloc_1263_, 7, v_infoState_1199_);
lean_ctor_set(v_reuseFailAlloc_1263_, 8, v_snapshotTasks_1200_);
lean_ctor_set(v_reuseFailAlloc_1263_, 9, v_newDecls_1201_);
v___x_1208_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v_mctx_1211_; lean_object* v_zetaDeltaFVarIds_1212_; lean_object* v_postponed_1213_; lean_object* v_diag_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1261_; 
v___x_1209_ = lean_st_ref_set(v_a_1162_, v___x_1208_);
v___x_1210_ = lean_st_ref_take(v_a_1160_);
v_mctx_1211_ = lean_ctor_get(v___x_1210_, 0);
v_zetaDeltaFVarIds_1212_ = lean_ctor_get(v___x_1210_, 2);
v_postponed_1213_ = lean_ctor_get(v___x_1210_, 3);
v_diag_1214_ = lean_ctor_get(v___x_1210_, 4);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1261_ == 0)
{
lean_object* v_unused_1262_; 
v_unused_1262_ = lean_ctor_get(v___x_1210_, 1);
lean_dec(v_unused_1262_);
v___x_1216_ = v___x_1210_;
v_isShared_1217_ = v_isSharedCheck_1261_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_diag_1214_);
lean_inc(v_postponed_1213_);
lean_inc(v_zetaDeltaFVarIds_1212_);
lean_inc(v_mctx_1211_);
lean_dec(v___x_1210_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1261_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_mctx_1211_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1260_, 2, v_zetaDeltaFVarIds_1212_);
lean_ctor_set(v_reuseFailAlloc_1260_, 3, v_postponed_1213_);
lean_ctor_set(v_reuseFailAlloc_1260_, 4, v_diag_1214_);
v___x_1220_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v_nextMacroScope_1224_; lean_object* v_ngen_1225_; lean_object* v_auxDeclNGen_1226_; lean_object* v_traceState_1227_; lean_object* v_messages_1228_; lean_object* v_infoState_1229_; lean_object* v_snapshotTasks_1230_; lean_object* v_newDecls_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1258_; 
v___x_1221_ = lean_st_ref_set(v_a_1160_, v___x_1220_);
v___x_1222_ = lean_st_ref_take(v_a_1162_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
v_nextMacroScope_1224_ = lean_ctor_get(v___x_1222_, 1);
v_ngen_1225_ = lean_ctor_get(v___x_1222_, 2);
v_auxDeclNGen_1226_ = lean_ctor_get(v___x_1222_, 3);
v_traceState_1227_ = lean_ctor_get(v___x_1222_, 4);
v_messages_1228_ = lean_ctor_get(v___x_1222_, 6);
v_infoState_1229_ = lean_ctor_get(v___x_1222_, 7);
v_snapshotTasks_1230_ = lean_ctor_get(v___x_1222_, 8);
v_newDecls_1231_ = lean_ctor_get(v___x_1222_, 9);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1258_ == 0)
{
lean_object* v_unused_1259_; 
v_unused_1259_ = lean_ctor_get(v___x_1222_, 5);
lean_dec(v_unused_1259_);
v___x_1233_ = v___x_1222_;
v_isShared_1234_ = v_isSharedCheck_1258_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_newDecls_1231_);
lean_inc(v_snapshotTasks_1230_);
lean_inc(v_infoState_1229_);
lean_inc(v_messages_1228_);
lean_inc(v_traceState_1227_);
lean_inc(v_auxDeclNGen_1226_);
lean_inc(v_ngen_1225_);
lean_inc(v_nextMacroScope_1224_);
lean_inc(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1258_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = l_Lean_addProtected(v_env_1223_, v_name_1187_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 5, v___x_1206_);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_nextMacroScope_1224_);
lean_ctor_set(v_reuseFailAlloc_1257_, 2, v_ngen_1225_);
lean_ctor_set(v_reuseFailAlloc_1257_, 3, v_auxDeclNGen_1226_);
lean_ctor_set(v_reuseFailAlloc_1257_, 4, v_traceState_1227_);
lean_ctor_set(v_reuseFailAlloc_1257_, 5, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1257_, 6, v_messages_1228_);
lean_ctor_set(v_reuseFailAlloc_1257_, 7, v_infoState_1229_);
lean_ctor_set(v_reuseFailAlloc_1257_, 8, v_snapshotTasks_1230_);
lean_ctor_set(v_reuseFailAlloc_1257_, 9, v_newDecls_1231_);
v___x_1237_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_mctx_1240_; lean_object* v_zetaDeltaFVarIds_1241_; lean_object* v_postponed_1242_; lean_object* v_diag_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1255_; 
v___x_1238_ = lean_st_ref_set(v_a_1162_, v___x_1237_);
v___x_1239_ = lean_st_ref_take(v_a_1160_);
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
lean_ctor_set(v___x_1245_, 1, v___x_1218_);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_mctx_1240_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1218_);
lean_ctor_set(v_reuseFailAlloc_1254_, 2, v_zetaDeltaFVarIds_1241_);
lean_ctor_set(v_reuseFailAlloc_1254_, 3, v_postponed_1242_);
lean_ctor_set(v_reuseFailAlloc_1254_, 4, v_diag_1243_);
v___x_1248_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1249_ = lean_st_ref_set(v_a_1160_, v___x_1248_);
v___x_1250_ = lean_box(0);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 0, v___x_1250_);
v___x_1252_ = v___x_1190_;
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
lean_dec(v_a_1182_);
return v___x_1185_;
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_del_object(v___x_1168_);
v_a_1269_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1181_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1181_);
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
lean_dec(v___x_1176_);
lean_dec_ref(v_type_1174_);
lean_dec(v_levelParams_1173_);
lean_dec(v_numMinors_1172_);
lean_dec(v_numMotives_1171_);
lean_del_object(v___x_1168_);
lean_dec(v_belowName_1158_);
lean_dec(v_nParams_1157_);
v___x_1277_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_1278_ = l_Lean_MessageData_ofName(v_recName_1156_);
v___x_1279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1277_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_1281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1279_);
lean_ctor_set(v___x_1281_, 1, v___x_1280_);
v___x_1282_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1281_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1282_;
}
}
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
lean_dec(v_a_1165_);
lean_dec(v_belowName_1158_);
lean_dec(v_nParams_1157_);
v___x_1284_ = l_Lean_MessageData_ofName(v_recName_1156_);
v___x_1285_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__5);
v___x_1286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1284_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
v___x_1287_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_1286_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1287_;
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_dec(v_belowName_1158_);
lean_dec(v_nParams_1157_);
lean_dec(v_recName_1156_);
v_a_1288_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1164_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1164_);
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
lean_object* v___x_1437_; lean_object* v_traceState_1438_; lean_object* v_traces_1439_; lean_object* v___x_1440_; lean_object* v_traceState_1441_; lean_object* v_env_1442_; lean_object* v_nextMacroScope_1443_; lean_object* v_ngen_1444_; lean_object* v_auxDeclNGen_1445_; lean_object* v_cache_1446_; lean_object* v_messages_1447_; lean_object* v_infoState_1448_; lean_object* v_snapshotTasks_1449_; lean_object* v_newDecls_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1469_; 
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
v_newDecls_1450_ = lean_ctor_get(v___x_1440_, 9);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1452_ = v___x_1440_;
v_isShared_1453_ = v_isSharedCheck_1469_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_newDecls_1450_);
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
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1469_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
uint64_t v_tid_1454_; lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1467_; 
v_tid_1454_ = lean_ctor_get_uint64(v_traceState_1441_, sizeof(void*)*1);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_traceState_1441_);
if (v_isSharedCheck_1467_ == 0)
{
lean_object* v_unused_1468_; 
v_unused_1468_ = lean_ctor_get(v_traceState_1441_, 0);
lean_dec(v_unused_1468_);
v___x_1456_ = v_traceState_1441_;
v_isShared_1457_ = v_isSharedCheck_1467_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v_traceState_1441_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1467_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1458_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___closed__1);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1458_);
v___x_1460_ = v___x_1456_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1458_);
lean_ctor_set_uint64(v_reuseFailAlloc_1466_, sizeof(void*)*1, v_tid_1454_);
v___x_1460_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
lean_object* v___x_1462_; 
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 4, v___x_1460_);
v___x_1462_ = v___x_1452_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_env_1442_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_nextMacroScope_1443_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_ngen_1444_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_auxDeclNGen_1445_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1465_, 5, v_cache_1446_);
lean_ctor_set(v_reuseFailAlloc_1465_, 6, v_messages_1447_);
lean_ctor_set(v_reuseFailAlloc_1465_, 7, v_infoState_1448_);
lean_ctor_set(v_reuseFailAlloc_1465_, 8, v_snapshotTasks_1449_);
lean_ctor_set(v_reuseFailAlloc_1465_, 9, v_newDecls_1450_);
v___x_1462_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_st_ref_set(v___y_1435_, v___x_1462_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_traces_1439_);
return v___x_1464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1470_);
lean_dec(v___y_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v___y_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___boxed(lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1(v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
return v_res_1484_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__2(lean_object* v_opts_1485_, lean_object* v_opt_1486_){
_start:
{
lean_object* v_name_1487_; lean_object* v_defValue_1488_; lean_object* v_map_1489_; lean_object* v___x_1490_; 
v_name_1487_ = lean_ctor_get(v_opt_1486_, 0);
v_defValue_1488_ = lean_ctor_get(v_opt_1486_, 1);
v_map_1489_ = lean_ctor_get(v_opts_1485_, 0);
v___x_1490_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1489_, v_name_1487_);
if (lean_obj_tag(v___x_1490_) == 0)
{
uint8_t v___x_1491_; 
v___x_1491_ = lean_unbox(v_defValue_1488_);
return v___x_1491_;
}
else
{
lean_object* v_val_1492_; 
v_val_1492_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1492_);
lean_dec_ref(v___x_1490_);
if (lean_obj_tag(v_val_1492_) == 1)
{
uint8_t v_v_1493_; 
v_v_1493_ = lean_ctor_get_uint8(v_val_1492_, 0);
lean_dec_ref(v_val_1492_);
return v_v_1493_;
}
else
{
uint8_t v___x_1494_; 
lean_dec(v_val_1492_);
v___x_1494_ = lean_unbox(v_defValue_1488_);
return v___x_1494_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__2___boxed(lean_object* v_opts_1495_, lean_object* v_opt_1496_){
_start:
{
uint8_t v_res_1497_; lean_object* v_r_1498_; 
v_res_1497_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1495_, v_opt_1496_);
lean_dec_ref(v_opt_1496_);
lean_dec_ref(v_opts_1495_);
v_r_1498_ = lean_box(v_res_1497_);
return v_r_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1499_, lean_object* v_x_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = l_Lean_MessageData_ofName(v_indName_1499_);
v___x_1507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_mkBelow___lam__0(v_indName_1508_, v_x_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_x_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg(lean_object* v_x_1516_){
_start:
{
if (lean_obj_tag(v_x_1516_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_a_1518_ = lean_ctor_get(v_x_1516_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_x_1516_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v_x_1516_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v_x_1516_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 1);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v_x_1516_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_x_1516_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v_x_1516_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v_x_1516_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 0);
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg___boxed(lean_object* v_x_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg(v_x_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(lean_object* v_e_1537_){
_start:
{
if (lean_obj_tag(v_e_1537_) == 0)
{
uint8_t v___x_1538_; 
v___x_1538_ = 2;
return v___x_1538_;
}
else
{
uint8_t v___x_1539_; 
v___x_1539_ = 0;
return v___x_1539_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3___boxed(lean_object* v_e_1540_){
_start:
{
uint8_t v_res_1541_; lean_object* v_r_1542_; 
v_res_1541_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_e_1540_);
lean_dec_ref(v_e_1540_);
v_r_1542_ = lean_box(v_res_1541_);
return v_r_1542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4_spec__5(size_t v_sz_1543_, size_t v_i_1544_, lean_object* v_bs_1545_){
_start:
{
uint8_t v___x_1546_; 
v___x_1546_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
if (v___x_1546_ == 0)
{
return v_bs_1545_;
}
else
{
lean_object* v_v_1547_; lean_object* v_msg_1548_; lean_object* v___x_1549_; lean_object* v_bs_x27_1550_; size_t v___x_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
v_v_1547_ = lean_array_uget_borrowed(v_bs_1545_, v_i_1544_);
v_msg_1548_ = lean_ctor_get(v_v_1547_, 1);
lean_inc_ref(v_msg_1548_);
v___x_1549_ = lean_unsigned_to_nat(0u);
v_bs_x27_1550_ = lean_array_uset(v_bs_1545_, v_i_1544_, v___x_1549_);
v___x_1551_ = ((size_t)1ULL);
v___x_1552_ = lean_usize_add(v_i_1544_, v___x_1551_);
v___x_1553_ = lean_array_uset(v_bs_x27_1550_, v_i_1544_, v_msg_1548_);
v_i_1544_ = v___x_1552_;
v_bs_1545_ = v___x_1553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_1555_, lean_object* v_i_1556_, lean_object* v_bs_1557_){
_start:
{
size_t v_sz_boxed_1558_; size_t v_i_boxed_1559_; lean_object* v_res_1560_; 
v_sz_boxed_1558_ = lean_unbox_usize(v_sz_1555_);
lean_dec(v_sz_1555_);
v_i_boxed_1559_ = lean_unbox_usize(v_i_1556_);
lean_dec(v_i_1556_);
v_res_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4_spec__5(v_sz_boxed_1558_, v_i_boxed_1559_, v_bs_1557_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(lean_object* v_oldTraces_1561_, lean_object* v_data_1562_, lean_object* v_ref_1563_, lean_object* v_msg_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_fileName_1570_; lean_object* v_fileMap_1571_; lean_object* v_options_1572_; lean_object* v_currRecDepth_1573_; lean_object* v_maxRecDepth_1574_; lean_object* v_ref_1575_; lean_object* v_currNamespace_1576_; lean_object* v_openDecls_1577_; lean_object* v_initHeartbeats_1578_; lean_object* v_maxHeartbeats_1579_; lean_object* v_quotContext_1580_; lean_object* v_currMacroScope_1581_; uint8_t v_diag_1582_; lean_object* v_cancelTk_x3f_1583_; uint8_t v_suppressElabErrors_1584_; lean_object* v_inheritedTraceOptions_1585_; lean_object* v___x_1586_; lean_object* v_traceState_1587_; lean_object* v_traces_1588_; lean_object* v_ref_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; lean_object* v_msg_1595_; lean_object* v___x_1596_; lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1635_; 
v_fileName_1570_ = lean_ctor_get(v___y_1567_, 0);
v_fileMap_1571_ = lean_ctor_get(v___y_1567_, 1);
v_options_1572_ = lean_ctor_get(v___y_1567_, 2);
v_currRecDepth_1573_ = lean_ctor_get(v___y_1567_, 3);
v_maxRecDepth_1574_ = lean_ctor_get(v___y_1567_, 4);
v_ref_1575_ = lean_ctor_get(v___y_1567_, 5);
v_currNamespace_1576_ = lean_ctor_get(v___y_1567_, 6);
v_openDecls_1577_ = lean_ctor_get(v___y_1567_, 7);
v_initHeartbeats_1578_ = lean_ctor_get(v___y_1567_, 8);
v_maxHeartbeats_1579_ = lean_ctor_get(v___y_1567_, 9);
v_quotContext_1580_ = lean_ctor_get(v___y_1567_, 10);
v_currMacroScope_1581_ = lean_ctor_get(v___y_1567_, 11);
v_diag_1582_ = lean_ctor_get_uint8(v___y_1567_, sizeof(void*)*14);
v_cancelTk_x3f_1583_ = lean_ctor_get(v___y_1567_, 12);
v_suppressElabErrors_1584_ = lean_ctor_get_uint8(v___y_1567_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1585_ = lean_ctor_get(v___y_1567_, 13);
v___x_1586_ = lean_st_ref_get(v___y_1568_);
v_traceState_1587_ = lean_ctor_get(v___x_1586_, 4);
lean_inc_ref(v_traceState_1587_);
lean_dec(v___x_1586_);
v_traces_1588_ = lean_ctor_get(v_traceState_1587_, 0);
lean_inc_ref(v_traces_1588_);
lean_dec_ref(v_traceState_1587_);
v_ref_1589_ = l_Lean_replaceRef(v_ref_1563_, v_ref_1575_);
lean_inc_ref(v_inheritedTraceOptions_1585_);
lean_inc(v_cancelTk_x3f_1583_);
lean_inc(v_currMacroScope_1581_);
lean_inc(v_quotContext_1580_);
lean_inc(v_maxHeartbeats_1579_);
lean_inc(v_initHeartbeats_1578_);
lean_inc(v_openDecls_1577_);
lean_inc(v_currNamespace_1576_);
lean_inc(v_maxRecDepth_1574_);
lean_inc(v_currRecDepth_1573_);
lean_inc_ref(v_options_1572_);
lean_inc_ref(v_fileMap_1571_);
lean_inc_ref(v_fileName_1570_);
v___x_1590_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1590_, 0, v_fileName_1570_);
lean_ctor_set(v___x_1590_, 1, v_fileMap_1571_);
lean_ctor_set(v___x_1590_, 2, v_options_1572_);
lean_ctor_set(v___x_1590_, 3, v_currRecDepth_1573_);
lean_ctor_set(v___x_1590_, 4, v_maxRecDepth_1574_);
lean_ctor_set(v___x_1590_, 5, v_ref_1589_);
lean_ctor_set(v___x_1590_, 6, v_currNamespace_1576_);
lean_ctor_set(v___x_1590_, 7, v_openDecls_1577_);
lean_ctor_set(v___x_1590_, 8, v_initHeartbeats_1578_);
lean_ctor_set(v___x_1590_, 9, v_maxHeartbeats_1579_);
lean_ctor_set(v___x_1590_, 10, v_quotContext_1580_);
lean_ctor_set(v___x_1590_, 11, v_currMacroScope_1581_);
lean_ctor_set(v___x_1590_, 12, v_cancelTk_x3f_1583_);
lean_ctor_set(v___x_1590_, 13, v_inheritedTraceOptions_1585_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*14, v_diag_1582_);
lean_ctor_set_uint8(v___x_1590_, sizeof(void*)*14 + 1, v_suppressElabErrors_1584_);
v___x_1591_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1588_);
lean_dec_ref(v_traces_1588_);
v_sz_1592_ = lean_array_size(v___x_1591_);
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4_spec__5(v_sz_1592_, v___x_1593_, v___x_1591_);
v_msg_1595_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1595_, 0, v_data_1562_);
lean_ctor_set(v_msg_1595_, 1, v_msg_1564_);
lean_ctor_set(v_msg_1595_, 2, v___x_1594_);
v___x_1596_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1595_, v___y_1565_, v___y_1566_, v___x_1590_, v___y_1568_);
lean_dec_ref(v___x_1590_);
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
lean_object* v___x_1601_; lean_object* v_traceState_1602_; lean_object* v_env_1603_; lean_object* v_nextMacroScope_1604_; lean_object* v_ngen_1605_; lean_object* v_auxDeclNGen_1606_; lean_object* v_cache_1607_; lean_object* v_messages_1608_; lean_object* v_infoState_1609_; lean_object* v_snapshotTasks_1610_; lean_object* v_newDecls_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1634_; 
v___x_1601_ = lean_st_ref_take(v___y_1568_);
v_traceState_1602_ = lean_ctor_get(v___x_1601_, 4);
v_env_1603_ = lean_ctor_get(v___x_1601_, 0);
v_nextMacroScope_1604_ = lean_ctor_get(v___x_1601_, 1);
v_ngen_1605_ = lean_ctor_get(v___x_1601_, 2);
v_auxDeclNGen_1606_ = lean_ctor_get(v___x_1601_, 3);
v_cache_1607_ = lean_ctor_get(v___x_1601_, 5);
v_messages_1608_ = lean_ctor_get(v___x_1601_, 6);
v_infoState_1609_ = lean_ctor_get(v___x_1601_, 7);
v_snapshotTasks_1610_ = lean_ctor_get(v___x_1601_, 8);
v_newDecls_1611_ = lean_ctor_get(v___x_1601_, 9);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1613_ = v___x_1601_;
v_isShared_1614_ = v_isSharedCheck_1634_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_newDecls_1611_);
lean_inc(v_snapshotTasks_1610_);
lean_inc(v_infoState_1609_);
lean_inc(v_messages_1608_);
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
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1619_, 0, v_ref_1563_);
lean_ctor_set(v___x_1619_, 1, v_a_1597_);
v___x_1620_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1561_, v___x_1619_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1620_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1620_);
lean_ctor_set_uint64(v_reuseFailAlloc_1631_, sizeof(void*)*1, v_tid_1615_);
v___x_1622_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1624_; 
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 4, v___x_1622_);
v___x_1624_ = v___x_1613_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_env_1603_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v_nextMacroScope_1604_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_ngen_1605_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_auxDeclNGen_1606_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1630_, 5, v_cache_1607_);
lean_ctor_set(v_reuseFailAlloc_1630_, 6, v_messages_1608_);
lean_ctor_set(v_reuseFailAlloc_1630_, 7, v_infoState_1609_);
lean_ctor_set(v_reuseFailAlloc_1630_, 8, v_snapshotTasks_1610_);
lean_ctor_set(v_reuseFailAlloc_1630_, 9, v_newDecls_1611_);
v___x_1624_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1625_ = lean_st_ref_set(v___y_1568_, v___x_1624_);
v___x_1626_ = lean_box(0);
if (v_isShared_1600_ == 0)
{
lean_ctor_set(v___x_1599_, 0, v___x_1626_);
v___x_1628_ = v___x_1599_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4___boxed(lean_object* v_oldTraces_1636_, lean_object* v_data_1637_, lean_object* v_ref_1638_, lean_object* v_msg_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_oldTraces_1636_, v_data_1637_, v_ref_1638_, v_msg_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(lean_object* v_opts_1646_, lean_object* v_opt_1647_){
_start:
{
lean_object* v_name_1648_; lean_object* v_defValue_1649_; lean_object* v_map_1650_; lean_object* v___x_1651_; 
v_name_1648_ = lean_ctor_get(v_opt_1647_, 0);
v_defValue_1649_ = lean_ctor_get(v_opt_1647_, 1);
v_map_1650_ = lean_ctor_get(v_opts_1646_, 0);
v___x_1651_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1650_, v_name_1648_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_inc(v_defValue_1649_);
return v_defValue_1649_;
}
else
{
lean_object* v_val_1652_; 
v_val_1652_ = lean_ctor_get(v___x_1651_, 0);
lean_inc(v_val_1652_);
lean_dec_ref(v___x_1651_);
if (lean_obj_tag(v_val_1652_) == 3)
{
lean_object* v_v_1653_; 
v_v_1653_ = lean_ctor_get(v_val_1652_, 0);
lean_inc(v_v_1653_);
lean_dec_ref(v_val_1652_);
return v_v_1653_;
}
else
{
lean_dec(v_val_1652_);
lean_inc(v_defValue_1649_);
return v_defValue_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6___boxed(lean_object* v_opts_1654_, lean_object* v_opt_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1654_, v_opt_1655_);
lean_dec_ref(v_opt_1655_);
lean_dec_ref(v_opts_1654_);
return v_res_1656_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__0));
v___x_1659_ = l_Lean_stringToMessageData(v___x_1658_);
return v___x_1659_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2(void){
_start:
{
lean_object* v___x_1660_; double v___x_1661_; 
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = lean_float_of_nat(v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__4(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__3));
v___x_1664_ = l_Lean_stringToMessageData(v___x_1663_);
return v___x_1664_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__5(void){
_start:
{
lean_object* v___x_1665_; double v___x_1666_; 
v___x_1665_ = lean_unsigned_to_nat(1000u);
v___x_1666_ = lean_float_of_nat(v___x_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(lean_object* v_cls_1667_, uint8_t v_collapsed_1668_, lean_object* v_tag_1669_, lean_object* v_opts_1670_, uint8_t v_clsEnabled_1671_, lean_object* v_oldTraces_1672_, lean_object* v_msg_1673_, lean_object* v_resStartStop_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_fst_1680_; lean_object* v_snd_1681_; lean_object* v___x_1683_; uint8_t v_isShared_1684_; uint8_t v_isSharedCheck_1772_; 
v_fst_1680_ = lean_ctor_get(v_resStartStop_1674_, 0);
v_snd_1681_ = lean_ctor_get(v_resStartStop_1674_, 1);
v_isSharedCheck_1772_ = !lean_is_exclusive(v_resStartStop_1674_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1683_ = v_resStartStop_1674_;
v_isShared_1684_ = v_isSharedCheck_1772_;
goto v_resetjp_1682_;
}
else
{
lean_inc(v_snd_1681_);
lean_inc(v_fst_1680_);
lean_dec(v_resStartStop_1674_);
v___x_1683_ = lean_box(0);
v_isShared_1684_ = v_isSharedCheck_1772_;
goto v_resetjp_1682_;
}
v_resetjp_1682_:
{
lean_object* v___y_1686_; lean_object* v___y_1687_; lean_object* v_data_1688_; lean_object* v_fst_1691_; lean_object* v_snd_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1771_; 
v_fst_1691_ = lean_ctor_get(v_snd_1681_, 0);
v_snd_1692_ = lean_ctor_get(v_snd_1681_, 1);
v_isSharedCheck_1771_ = !lean_is_exclusive(v_snd_1681_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1694_ = v_snd_1681_;
v_isShared_1695_ = v_isSharedCheck_1771_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_snd_1692_);
lean_inc(v_fst_1691_);
lean_dec(v_snd_1681_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1771_;
goto v_resetjp_1693_;
}
v___jp_1685_:
{
lean_object* v___x_1689_; 
lean_inc(v___y_1686_);
v___x_1689_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__4(v_oldTraces_1672_, v_data_1688_, v___y_1686_, v___y_1687_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v___x_1690_; 
lean_dec_ref(v___x_1689_);
v___x_1690_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg(v_fst_1680_);
return v___x_1690_;
}
else
{
lean_dec(v_fst_1680_);
return v___x_1689_;
}
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; uint8_t v___x_1697_; lean_object* v___y_1699_; lean_object* v_a_1700_; uint8_t v___y_1724_; double v___y_1756_; 
v___x_1696_ = l_Lean_trace_profiler;
v___x_1697_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1670_, v___x_1696_);
if (v___x_1697_ == 0)
{
v___y_1724_ = v___x_1697_;
goto v___jp_1723_;
}
else
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1762_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_opts_1670_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v___x_1764_; double v___x_1765_; double v___x_1766_; double v___x_1767_; 
v___x_1763_ = l_Lean_trace_profiler_threshold;
v___x_1764_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1670_, v___x_1763_);
v___x_1765_ = lean_float_of_nat(v___x_1764_);
v___x_1766_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__5);
v___x_1767_ = lean_float_div(v___x_1765_, v___x_1766_);
v___y_1756_ = v___x_1767_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1769_; double v___x_1770_; 
v___x_1768_ = l_Lean_trace_profiler_threshold;
v___x_1769_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__6(v_opts_1670_, v___x_1768_);
v___x_1770_ = lean_float_of_nat(v___x_1769_);
v___y_1756_ = v___x_1770_;
goto v___jp_1755_;
}
}
v___jp_1698_:
{
uint8_t v_result_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
v_result_1701_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__3(v_fst_1680_);
v___x_1702_ = l_Lean_TraceResult_toEmoji(v_result_1701_);
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
v___x_1704_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__1);
if (v_isShared_1695_ == 0)
{
lean_ctor_set_tag(v___x_1694_, 7);
lean_ctor_set(v___x_1694_, 1, v___x_1704_);
lean_ctor_set(v___x_1694_, 0, v___x_1703_);
v___x_1706_ = v___x_1694_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v_m_1708_; 
if (v_isShared_1684_ == 0)
{
lean_ctor_set_tag(v___x_1683_, 7);
lean_ctor_set(v___x_1683_, 1, v_a_1700_);
lean_ctor_set(v___x_1683_, 0, v___x_1706_);
v_m_1708_ = v___x_1683_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1700_);
v_m_1708_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; double v___x_1711_; lean_object* v_data_1712_; 
v___x_1709_ = lean_box(v_result_1701_);
v___x_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
v___x_1711_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__2);
lean_inc_ref(v_tag_1669_);
lean_inc_ref(v___x_1710_);
lean_inc(v_cls_1667_);
v_data_1712_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1712_, 0, v_cls_1667_);
lean_ctor_set(v_data_1712_, 1, v___x_1710_);
lean_ctor_set(v_data_1712_, 2, v_tag_1669_);
lean_ctor_set_float(v_data_1712_, sizeof(void*)*3, v___x_1711_);
lean_ctor_set_float(v_data_1712_, sizeof(void*)*3 + 8, v___x_1711_);
lean_ctor_set_uint8(v_data_1712_, sizeof(void*)*3 + 16, v_collapsed_1668_);
if (v___x_1697_ == 0)
{
lean_dec_ref(v___x_1710_);
lean_dec(v_snd_1692_);
lean_dec(v_fst_1691_);
lean_dec_ref(v_tag_1669_);
lean_dec(v_cls_1667_);
v___y_1686_ = v___y_1699_;
v___y_1687_ = v_m_1708_;
v_data_1688_ = v_data_1712_;
goto v___jp_1685_;
}
else
{
lean_object* v_data_1713_; double v___x_1714_; double v___x_1715_; 
lean_dec_ref(v_data_1712_);
v_data_1713_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1713_, 0, v_cls_1667_);
lean_ctor_set(v_data_1713_, 1, v___x_1710_);
lean_ctor_set(v_data_1713_, 2, v_tag_1669_);
v___x_1714_ = lean_unbox_float(v_fst_1691_);
lean_dec(v_fst_1691_);
lean_ctor_set_float(v_data_1713_, sizeof(void*)*3, v___x_1714_);
v___x_1715_ = lean_unbox_float(v_snd_1692_);
lean_dec(v_snd_1692_);
lean_ctor_set_float(v_data_1713_, sizeof(void*)*3 + 8, v___x_1715_);
lean_ctor_set_uint8(v_data_1713_, sizeof(void*)*3 + 16, v_collapsed_1668_);
v___y_1686_ = v___y_1699_;
v___y_1687_ = v_m_1708_;
v_data_1688_ = v_data_1713_;
goto v___jp_1685_;
}
}
}
}
v___jp_1718_:
{
lean_object* v_ref_1719_; lean_object* v___x_1720_; 
v_ref_1719_ = lean_ctor_get(v___y_1677_, 5);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
lean_inc(v_fst_1680_);
v___x_1720_ = lean_apply_6(v_msg_1673_, v_fst_1680_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, lean_box(0));
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
v___y_1699_ = v_ref_1719_;
v_a_1700_ = v_a_1721_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1722_; 
lean_dec_ref(v___x_1720_);
v___x_1722_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___closed__4);
v___y_1699_ = v_ref_1719_;
v_a_1700_ = v___x_1722_;
goto v___jp_1698_;
}
}
v___jp_1723_:
{
if (v_clsEnabled_1671_ == 0)
{
if (v___y_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v_traceState_1726_; lean_object* v_env_1727_; lean_object* v_nextMacroScope_1728_; lean_object* v_ngen_1729_; lean_object* v_auxDeclNGen_1730_; lean_object* v_cache_1731_; lean_object* v_messages_1732_; lean_object* v_infoState_1733_; lean_object* v_snapshotTasks_1734_; lean_object* v_newDecls_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1754_; 
lean_del_object(v___x_1694_);
lean_dec(v_snd_1692_);
lean_dec(v_fst_1691_);
lean_del_object(v___x_1683_);
lean_dec_ref(v_msg_1673_);
lean_dec_ref(v_tag_1669_);
lean_dec(v_cls_1667_);
v___x_1725_ = lean_st_ref_take(v___y_1678_);
v_traceState_1726_ = lean_ctor_get(v___x_1725_, 4);
v_env_1727_ = lean_ctor_get(v___x_1725_, 0);
v_nextMacroScope_1728_ = lean_ctor_get(v___x_1725_, 1);
v_ngen_1729_ = lean_ctor_get(v___x_1725_, 2);
v_auxDeclNGen_1730_ = lean_ctor_get(v___x_1725_, 3);
v_cache_1731_ = lean_ctor_get(v___x_1725_, 5);
v_messages_1732_ = lean_ctor_get(v___x_1725_, 6);
v_infoState_1733_ = lean_ctor_get(v___x_1725_, 7);
v_snapshotTasks_1734_ = lean_ctor_get(v___x_1725_, 8);
v_newDecls_1735_ = lean_ctor_get(v___x_1725_, 9);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1737_ = v___x_1725_;
v_isShared_1738_ = v_isSharedCheck_1754_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_newDecls_1735_);
lean_inc(v_snapshotTasks_1734_);
lean_inc(v_infoState_1733_);
lean_inc(v_messages_1732_);
lean_inc(v_cache_1731_);
lean_inc(v_traceState_1726_);
lean_inc(v_auxDeclNGen_1730_);
lean_inc(v_ngen_1729_);
lean_inc(v_nextMacroScope_1728_);
lean_inc(v_env_1727_);
lean_dec(v___x_1725_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1754_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
uint64_t v_tid_1739_; lean_object* v_traces_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1753_; 
v_tid_1739_ = lean_ctor_get_uint64(v_traceState_1726_, sizeof(void*)*1);
v_traces_1740_ = lean_ctor_get(v_traceState_1726_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_traceState_1726_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1742_ = v_traceState_1726_;
v_isShared_1743_ = v_isSharedCheck_1753_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_traces_1740_);
lean_dec(v_traceState_1726_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1753_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1672_, v_traces_1740_);
lean_dec_ref(v_traces_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v___x_1744_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v___x_1744_);
lean_ctor_set_uint64(v_reuseFailAlloc_1752_, sizeof(void*)*1, v_tid_1739_);
v___x_1746_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1748_; 
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 4, v___x_1746_);
v___x_1748_ = v___x_1737_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_env_1727_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_nextMacroScope_1728_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_ngen_1729_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v_auxDeclNGen_1730_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1751_, 5, v_cache_1731_);
lean_ctor_set(v_reuseFailAlloc_1751_, 6, v_messages_1732_);
lean_ctor_set(v_reuseFailAlloc_1751_, 7, v_infoState_1733_);
lean_ctor_set(v_reuseFailAlloc_1751_, 8, v_snapshotTasks_1734_);
lean_ctor_set(v_reuseFailAlloc_1751_, 9, v_newDecls_1735_);
v___x_1748_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_st_ref_set(v___y_1678_, v___x_1748_);
v___x_1750_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg(v_fst_1680_);
return v___x_1750_;
}
}
}
}
}
else
{
goto v___jp_1718_;
}
}
else
{
goto v___jp_1718_;
}
}
v___jp_1755_:
{
double v___x_1757_; double v___x_1758_; double v___x_1759_; uint8_t v___x_1760_; 
v___x_1757_ = lean_unbox_float(v_snd_1692_);
v___x_1758_ = lean_unbox_float(v_fst_1691_);
v___x_1759_ = lean_float_sub(v___x_1757_, v___x_1758_);
v___x_1760_ = lean_float_decLt(v___y_1756_, v___x_1759_);
v___y_1724_ = v___x_1760_;
goto v___jp_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_cls_1773_, lean_object* v_collapsed_1774_, lean_object* v_tag_1775_, lean_object* v_opts_1776_, lean_object* v_clsEnabled_1777_, lean_object* v_oldTraces_1778_, lean_object* v_msg_1779_, lean_object* v_resStartStop_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
uint8_t v_collapsed_boxed_1786_; uint8_t v_clsEnabled_boxed_1787_; lean_object* v_res_1788_; 
v_collapsed_boxed_1786_ = lean_unbox(v_collapsed_1774_);
v_clsEnabled_boxed_1787_ = lean_unbox(v_clsEnabled_1777_);
v_res_1788_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v_cls_1773_, v_collapsed_boxed_1786_, v_tag_1775_, v_opts_1776_, v_clsEnabled_boxed_1787_, v_oldTraces_1778_, v_msg_1779_, v_resStartStop_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v_opts_1776_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1789_, lean_object* v___x_1790_, lean_object* v___x_1791_, lean_object* v___x_1792_, lean_object* v_a_1793_, lean_object* v_b_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_lt(v_a_1793_, v_upperBound_1789_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_dec(v_a_1793_);
lean_dec(v___x_1792_);
lean_dec(v___x_1791_);
lean_dec(v___x_1790_);
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_b_1794_);
return v___x_1801_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1802_ = lean_unsigned_to_nat(1u);
v___x_1803_ = lean_nat_add(v_a_1793_, v___x_1802_);
lean_dec(v_a_1793_);
lean_inc_n(v___x_1803_, 2);
lean_inc(v___x_1790_);
v___x_1804_ = lean_name_append_index_after(v___x_1790_, v___x_1803_);
lean_inc(v___x_1791_);
v___x_1805_ = lean_name_append_index_after(v___x_1791_, v___x_1803_);
lean_inc(v___x_1792_);
v___x_1806_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1804_, v___x_1792_, v___x_1805_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v___x_1806_);
v___x_1807_ = lean_box(0);
v_a_1793_ = v___x_1803_;
v_b_1794_ = v___x_1807_;
goto _start;
}
else
{
lean_dec(v___x_1803_);
lean_dec(v___x_1792_);
lean_dec(v___x_1791_);
lean_dec(v___x_1790_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1809_, lean_object* v___x_1810_, lean_object* v___x_1811_, lean_object* v___x_1812_, lean_object* v_a_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1809_, v___x_1810_, v___x_1811_, v___x_1812_, v_a_1813_, v_b_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v_upperBound_1809_);
return v_res_1820_;
}
}
static lean_object* _init_l_Lean_mkBelow___closed__6(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1831_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_1832_ = l_Lean_Name_append(v___x_1831_, v___x_1830_);
return v___x_1832_;
}
}
static double _init_l_Lean_mkBelow___closed__7(void){
_start:
{
lean_object* v___x_1833_; double v___x_1834_; 
v___x_1833_ = lean_unsigned_to_nat(1000000000u);
v___x_1834_ = lean_float_of_nat(v___x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_options_1841_; uint8_t v_hasTrace_1842_; 
v_options_1841_ = lean_ctor_get(v_a_1838_, 2);
v_hasTrace_1842_ = lean_ctor_get_uint8(v_options_1841_, sizeof(void*)*1);
if (v_hasTrace_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_inc(v_indName_1835_);
v___x_1843_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1908_; 
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1846_ = v___x_1843_;
v_isShared_1847_ = v_isSharedCheck_1908_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_a_1844_);
lean_dec(v___x_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1908_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
if (lean_obj_tag(v_a_1844_) == 5)
{
lean_object* v_val_1848_; uint8_t v_isRec_1849_; 
v_val_1848_ = lean_ctor_get(v_a_1844_, 0);
lean_inc_ref(v_val_1848_);
lean_dec_ref(v_a_1844_);
v_isRec_1849_ = lean_ctor_get_uint8(v_val_1848_, sizeof(void*)*6);
if (v_isRec_1849_ == 0)
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_dec_ref(v_val_1848_);
lean_dec(v_indName_1835_);
v___x_1850_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1850_);
v___x_1852_ = v___x_1846_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v_toConstantVal_1854_; lean_object* v_numParams_1855_; lean_object* v_all_1856_; lean_object* v_numNested_1857_; lean_object* v_type_1858_; lean_object* v___x_1859_; 
lean_del_object(v___x_1846_);
v_toConstantVal_1854_ = lean_ctor_get(v_val_1848_, 0);
lean_inc_ref(v_toConstantVal_1854_);
v_numParams_1855_ = lean_ctor_get(v_val_1848_, 1);
lean_inc(v_numParams_1855_);
v_all_1856_ = lean_ctor_get(v_val_1848_, 3);
lean_inc(v_all_1856_);
v_numNested_1857_ = lean_ctor_get(v_val_1848_, 5);
lean_inc(v_numNested_1857_);
lean_dec_ref(v_val_1848_);
v_type_1858_ = lean_ctor_get(v_toConstantVal_1854_, 2);
lean_inc_ref(v_type_1858_);
lean_dec_ref(v_toConstantVal_1854_);
v___x_1859_ = l_Lean_Meta_isPropFormerType(v_type_1858_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1895_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1862_ = v___x_1859_;
v_isShared_1863_ = v_isSharedCheck_1895_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1859_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1895_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
uint8_t v___x_1864_; 
v___x_1864_ = lean_unbox(v_a_1860_);
lean_dec(v_a_1860_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
lean_del_object(v___x_1862_);
lean_inc_n(v_indName_1835_, 2);
v___x_1865_ = l_Lean_mkRecName(v_indName_1835_);
v___x_1866_ = l_Lean_mkBelowName(v_indName_1835_);
lean_inc(v___x_1866_);
lean_inc(v_numParams_1855_);
lean_inc(v___x_1865_);
v___x_1867_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1865_, v_numParams_1855_, v___x_1866_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1889_; 
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v___x_1867_, 0);
lean_dec(v_unused_1890_);
v___x_1869_ = v___x_1867_;
v_isShared_1870_ = v_isSharedCheck_1889_;
goto v_resetjp_1868_;
}
else
{
lean_dec(v___x_1867_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1889_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = l_List_get_x21Internal___redArg(v___x_1871_, v_all_1856_, v___x_1872_);
lean_dec(v_all_1856_);
v___x_1874_ = lean_name_eq(v___x_1873_, v_indName_1835_);
lean_dec(v_indName_1835_);
lean_dec(v___x_1873_);
if (v___x_1874_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1877_; 
lean_dec(v___x_1866_);
lean_dec(v___x_1865_);
lean_dec(v_numNested_1857_);
lean_dec(v_numParams_1855_);
v___x_1875_ = lean_box(0);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1875_);
v___x_1877_ = v___x_1869_;
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
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_del_object(v___x_1869_);
v___x_1879_ = lean_box(0);
v___x_1880_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1857_, v___x_1865_, v___x_1866_, v_numParams_1855_, v___x_1872_, v___x_1879_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_numNested_1857_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1887_ == 0)
{
lean_object* v_unused_1888_; 
v_unused_1888_ = lean_ctor_get(v___x_1880_, 0);
lean_dec(v_unused_1888_);
v___x_1882_ = v___x_1880_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_dec(v___x_1880_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1879_);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1879_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
else
{
return v___x_1880_;
}
}
}
}
else
{
lean_dec(v___x_1866_);
lean_dec(v___x_1865_);
lean_dec(v_numNested_1857_);
lean_dec(v_all_1856_);
lean_dec(v_numParams_1855_);
lean_dec(v_indName_1835_);
return v___x_1867_;
}
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
lean_dec(v_numNested_1857_);
lean_dec(v_all_1856_);
lean_dec(v_numParams_1855_);
lean_dec(v_indName_1835_);
v___x_1891_ = lean_box(0);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 0, v___x_1891_);
v___x_1893_ = v___x_1862_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_dec(v_numNested_1857_);
lean_dec(v_all_1856_);
lean_dec(v_numParams_1855_);
lean_dec(v_indName_1835_);
v_a_1896_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1859_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1859_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
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
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec(v_a_1844_);
lean_dec(v_indName_1835_);
v___x_1904_ = lean_box(0);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1904_);
v___x_1906_ = v___x_1846_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_indName_1835_);
v_a_1909_ = lean_ctor_get(v___x_1843_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1843_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1843_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1843_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; uint8_t v___x_1922_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v_a_1926_; lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v_a_1941_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v_a_1946_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v_a_1951_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v_a_1963_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v_a_1968_; 
v_inheritedTraceOptions_1917_ = lean_ctor_get(v_a_1838_, 13);
lean_inc(v_indName_1835_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1918_, 0, v_indName_1835_);
v___x_1919_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1920_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_1921_ = lean_obj_once(&l_Lean_mkBelow___closed__6, &l_Lean_mkBelow___closed__6_once, _init_l_Lean_mkBelow___closed__6);
v___x_1922_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1917_, v_options_1841_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = l_Lean_trace_profiler;
v___x_2038_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1841_, v___x_2037_);
if (v___x_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec_ref(v___f_1918_);
lean_inc(v_indName_1835_);
v___x_2039_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2104_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2042_ = v___x_2039_;
v_isShared_2043_ = v_isSharedCheck_2104_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2039_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2104_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
if (lean_obj_tag(v_a_2040_) == 5)
{
lean_object* v_val_2044_; uint8_t v_isRec_2045_; 
v_val_2044_ = lean_ctor_get(v_a_2040_, 0);
lean_inc_ref(v_val_2044_);
lean_dec_ref(v_a_2040_);
v_isRec_2045_ = lean_ctor_get_uint8(v_val_2044_, sizeof(void*)*6);
if (v_isRec_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec_ref(v_val_2044_);
lean_dec(v_indName_1835_);
v___x_2046_ = lean_box(0);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2046_);
v___x_2048_ = v___x_2042_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
else
{
lean_object* v_toConstantVal_2050_; lean_object* v_numParams_2051_; lean_object* v_all_2052_; lean_object* v_numNested_2053_; lean_object* v_type_2054_; lean_object* v___x_2055_; 
lean_del_object(v___x_2042_);
v_toConstantVal_2050_ = lean_ctor_get(v_val_2044_, 0);
lean_inc_ref(v_toConstantVal_2050_);
v_numParams_2051_ = lean_ctor_get(v_val_2044_, 1);
lean_inc(v_numParams_2051_);
v_all_2052_ = lean_ctor_get(v_val_2044_, 3);
lean_inc(v_all_2052_);
v_numNested_2053_ = lean_ctor_get(v_val_2044_, 5);
lean_inc(v_numNested_2053_);
lean_dec_ref(v_val_2044_);
v_type_2054_ = lean_ctor_get(v_toConstantVal_2050_, 2);
lean_inc_ref(v_type_2054_);
lean_dec_ref(v_toConstantVal_2050_);
v___x_2055_ = l_Lean_Meta_isPropFormerType(v_type_2054_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2091_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2091_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2091_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_unbox(v_a_2056_);
lean_dec(v_a_2056_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_del_object(v___x_2058_);
lean_inc_n(v_indName_1835_, 2);
v___x_2061_ = l_Lean_mkRecName(v_indName_1835_);
v___x_2062_ = l_Lean_mkBelowName(v_indName_1835_);
lean_inc(v___x_2062_);
lean_inc(v_numParams_2051_);
lean_inc(v___x_2061_);
v___x_2063_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2061_, v_numParams_2051_, v___x_2062_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2085_; 
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2063_, 0);
lean_dec(v_unused_2086_);
v___x_2065_ = v___x_2063_;
v_isShared_2066_ = v_isSharedCheck_2085_;
goto v_resetjp_2064_;
}
else
{
lean_dec(v___x_2063_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2085_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2067_ = lean_box(0);
v___x_2068_ = lean_unsigned_to_nat(0u);
v___x_2069_ = l_List_get_x21Internal___redArg(v___x_2067_, v_all_2052_, v___x_2068_);
lean_dec(v_all_2052_);
v___x_2070_ = lean_name_eq(v___x_2069_, v_indName_1835_);
lean_dec(v_indName_1835_);
lean_dec(v___x_2069_);
if (v___x_2070_ == 0)
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec(v___x_2062_);
lean_dec(v___x_2061_);
lean_dec(v_numNested_2053_);
lean_dec(v_numParams_2051_);
v___x_2071_ = lean_box(0);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2071_);
v___x_2073_ = v___x_2065_;
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
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
lean_del_object(v___x_2065_);
v___x_2075_ = lean_box(0);
v___x_2076_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2053_, v___x_2061_, v___x_2062_, v_numParams_2051_, v___x_2068_, v___x_2075_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_numNested_2053_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2083_; 
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2076_, 0);
lean_dec(v_unused_2084_);
v___x_2078_ = v___x_2076_;
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
else
{
lean_dec(v___x_2076_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2083_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2081_; 
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2075_);
v___x_2081_ = v___x_2078_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2075_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
return v___x_2076_;
}
}
}
}
else
{
lean_dec(v___x_2062_);
lean_dec(v___x_2061_);
lean_dec(v_numNested_2053_);
lean_dec(v_all_2052_);
lean_dec(v_numParams_2051_);
lean_dec(v_indName_1835_);
return v___x_2063_;
}
}
else
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
lean_dec(v_numNested_2053_);
lean_dec(v_all_2052_);
lean_dec(v_numParams_2051_);
lean_dec(v_indName_1835_);
v___x_2087_ = lean_box(0);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2087_);
v___x_2089_ = v___x_2058_;
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
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_numNested_2053_);
lean_dec(v_all_2052_);
lean_dec(v_numParams_2051_);
lean_dec(v_indName_1835_);
v_a_2092_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2055_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2055_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec(v_a_2040_);
lean_dec(v_indName_1835_);
v___x_2100_ = lean_box(0);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2100_);
v___x_2102_ = v___x_2042_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec(v_indName_1835_);
v_a_2105_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2039_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2039_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
goto v___jp_1970_;
}
}
else
{
goto v___jp_1970_;
}
v___jp_1923_:
{
lean_object* v___x_1927_; double v___x_1928_; double v___x_1929_; double v___x_1930_; double v___x_1931_; double v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1927_ = lean_io_mono_nanos_now();
v___x_1928_ = lean_float_of_nat(v___y_1924_);
v___x_1929_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_1930_ = lean_float_div(v___x_1928_, v___x_1929_);
v___x_1931_ = lean_float_of_nat(v___x_1927_);
v___x_1932_ = lean_float_div(v___x_1931_, v___x_1929_);
v___x_1933_ = lean_box_float(v___x_1930_);
v___x_1934_ = lean_box_float(v___x_1932_);
v___x_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1936_, 0, v_a_1926_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1919_, v_hasTrace_1842_, v___x_1920_, v_options_1841_, v___x_1922_, v___y_1925_, v___f_1918_, v___x_1936_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1937_;
}
v___jp_1938_:
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_a_1941_);
v___y_1924_ = v___y_1939_;
v___y_1925_ = v___y_1940_;
v_a_1926_ = v___x_1942_;
goto v___jp_1923_;
}
v___jp_1943_:
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_a_1946_);
v___y_1924_ = v___y_1944_;
v___y_1925_ = v___y_1945_;
v_a_1926_ = v___x_1947_;
goto v___jp_1923_;
}
v___jp_1948_:
{
lean_object* v___x_1952_; double v___x_1953_; double v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v___x_1952_ = lean_io_get_num_heartbeats();
v___x_1953_ = lean_float_of_nat(v___y_1949_);
v___x_1954_ = lean_float_of_nat(v___x_1952_);
v___x_1955_ = lean_box_float(v___x_1953_);
v___x_1956_ = lean_box_float(v___x_1954_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v_a_1951_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_1919_, v_hasTrace_1842_, v___x_1920_, v_options_1841_, v___x_1922_, v___y_1950_, v___f_1918_, v___x_1958_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
return v___x_1959_;
}
v___jp_1960_:
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_a_1963_);
v___y_1949_ = v___y_1961_;
v___y_1950_ = v___y_1962_;
v_a_1951_ = v___x_1964_;
goto v___jp_1948_;
}
v___jp_1965_:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_a_1968_);
v___y_1949_ = v___y_1966_;
v___y_1950_ = v___y_1967_;
v_a_1951_ = v___x_1969_;
goto v___jp_1948_;
}
v___jp_1970_:
{
lean_object* v___x_1971_; lean_object* v_a_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1971_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_1839_);
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1974_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_1841_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1835_);
v___x_1976_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; 
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
if (lean_obj_tag(v_a_1977_) == 5)
{
lean_object* v_val_1978_; uint8_t v_isRec_1979_; 
v_val_1978_ = lean_ctor_get(v_a_1977_, 0);
lean_inc_ref(v_val_1978_);
lean_dec_ref(v_a_1977_);
v_isRec_1979_ = lean_ctor_get_uint8(v_val_1978_, sizeof(void*)*6);
if (v_isRec_1979_ == 0)
{
lean_object* v___x_1980_; 
lean_dec_ref(v_val_1978_);
lean_dec(v_indName_1835_);
v___x_1980_ = lean_box(0);
v___y_1939_ = v___x_1975_;
v___y_1940_ = v_a_1972_;
v_a_1941_ = v___x_1980_;
goto v___jp_1938_;
}
else
{
lean_object* v_toConstantVal_1981_; lean_object* v_numParams_1982_; lean_object* v_all_1983_; lean_object* v_numNested_1984_; lean_object* v_type_1985_; lean_object* v___x_1986_; 
v_toConstantVal_1981_ = lean_ctor_get(v_val_1978_, 0);
lean_inc_ref(v_toConstantVal_1981_);
v_numParams_1982_ = lean_ctor_get(v_val_1978_, 1);
lean_inc(v_numParams_1982_);
v_all_1983_ = lean_ctor_get(v_val_1978_, 3);
lean_inc(v_all_1983_);
v_numNested_1984_ = lean_ctor_get(v_val_1978_, 5);
lean_inc(v_numNested_1984_);
lean_dec_ref(v_val_1978_);
v_type_1985_ = lean_ctor_get(v_toConstantVal_1981_, 2);
lean_inc_ref(v_type_1985_);
lean_dec_ref(v_toConstantVal_1981_);
v___x_1986_ = l_Lean_Meta_isPropFormerType(v_type_1985_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; uint8_t v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref(v___x_1986_);
v___x_1988_ = lean_unbox(v_a_1987_);
lean_dec(v_a_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_inc_n(v_indName_1835_, 2);
v___x_1989_ = l_Lean_mkRecName(v_indName_1835_);
v___x_1990_ = l_Lean_mkBelowName(v_indName_1835_);
lean_inc(v___x_1990_);
lean_inc(v_numParams_1982_);
lean_inc(v___x_1989_);
v___x_1991_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1989_, v_numParams_1982_, v___x_1990_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
lean_dec_ref(v___x_1991_);
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = l_List_get_x21Internal___redArg(v___x_1992_, v_all_1983_, v___x_1993_);
lean_dec(v_all_1983_);
v___x_1995_ = lean_name_eq(v___x_1994_, v_indName_1835_);
lean_dec(v_indName_1835_);
lean_dec(v___x_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec(v___x_1990_);
lean_dec(v___x_1989_);
lean_dec(v_numNested_1984_);
lean_dec(v_numParams_1982_);
v___x_1996_ = lean_box(0);
v___y_1939_ = v___x_1975_;
v___y_1940_ = v_a_1972_;
v_a_1941_ = v___x_1996_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = lean_box(0);
v___x_1998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1984_, v___x_1989_, v___x_1990_, v_numParams_1982_, v___x_1993_, v___x_1997_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_numNested_1984_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_dec_ref(v___x_1998_);
v___y_1939_ = v___x_1975_;
v___y_1940_ = v_a_1972_;
v_a_1941_ = v___x_1997_;
goto v___jp_1938_;
}
else
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___y_1944_ = v___x_1975_;
v___y_1945_ = v_a_1972_;
v_a_1946_ = v_a_1999_;
goto v___jp_1943_;
}
}
}
else
{
lean_dec(v___x_1990_);
lean_dec(v___x_1989_);
lean_dec(v_numNested_1984_);
lean_dec(v_all_1983_);
lean_dec(v_numParams_1982_);
lean_dec(v_indName_1835_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___x_1991_);
v___y_1939_ = v___x_1975_;
v___y_1940_ = v_a_1972_;
v_a_1941_ = v_a_2000_;
goto v___jp_1938_;
}
else
{
lean_object* v_a_2001_; 
v_a_2001_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_1991_);
v___y_1944_ = v___x_1975_;
v___y_1945_ = v_a_1972_;
v_a_1946_ = v_a_2001_;
goto v___jp_1943_;
}
}
}
else
{
lean_object* v___x_2002_; 
lean_dec(v_numNested_1984_);
lean_dec(v_all_1983_);
lean_dec(v_numParams_1982_);
lean_dec(v_indName_1835_);
v___x_2002_ = lean_box(0);
v___y_1939_ = v___x_1975_;
v___y_1940_ = v_a_1972_;
v_a_1941_ = v___x_2002_;
goto v___jp_1938_;
}
}
else
{
lean_object* v_a_2003_; 
lean_dec(v_numNested_1984_);
lean_dec(v_all_1983_);
lean_dec(v_numParams_1982_);
lean_dec(v_indName_1835_);
v_a_2003_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_1986_);
v___y_1944_ = v___x_1975_;
v___y_1945_ = v_a_1972_;
v_a_1946_ = v_a_2003_;
goto v___jp_1943_;
}
}
}
else
{
lean_object* v___x_2004_; 
lean_dec(v_a_1977_);
lean_dec(v_indName_1835_);
v___x_2004_ = lean_box(0);
v___y_1939_ = v___x_1975_;
v___y_1940_ = v_a_1972_;
v_a_1941_ = v___x_2004_;
goto v___jp_1938_;
}
}
else
{
lean_object* v_a_2005_; 
lean_dec(v_indName_1835_);
v_a_2005_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_1976_);
v___y_1944_ = v___x_1975_;
v___y_1945_ = v_a_1972_;
v_a_1946_ = v_a_2005_;
goto v___jp_1943_;
}
}
else
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1835_);
v___x_2007_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
if (lean_obj_tag(v_a_2008_) == 5)
{
lean_object* v_val_2009_; uint8_t v_isRec_2010_; 
v_val_2009_ = lean_ctor_get(v_a_2008_, 0);
lean_inc_ref(v_val_2009_);
lean_dec_ref(v_a_2008_);
v_isRec_2010_ = lean_ctor_get_uint8(v_val_2009_, sizeof(void*)*6);
if (v_isRec_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec_ref(v_val_2009_);
lean_dec(v_indName_1835_);
v___x_2011_ = lean_box(0);
v___y_1961_ = v___x_2006_;
v___y_1962_ = v_a_1972_;
v_a_1963_ = v___x_2011_;
goto v___jp_1960_;
}
else
{
lean_object* v_toConstantVal_2012_; lean_object* v_numParams_2013_; lean_object* v_all_2014_; lean_object* v_numNested_2015_; lean_object* v_type_2016_; lean_object* v___x_2017_; 
v_toConstantVal_2012_ = lean_ctor_get(v_val_2009_, 0);
lean_inc_ref(v_toConstantVal_2012_);
v_numParams_2013_ = lean_ctor_get(v_val_2009_, 1);
lean_inc(v_numParams_2013_);
v_all_2014_ = lean_ctor_get(v_val_2009_, 3);
lean_inc(v_all_2014_);
v_numNested_2015_ = lean_ctor_get(v_val_2009_, 5);
lean_inc(v_numNested_2015_);
lean_dec_ref(v_val_2009_);
v_type_2016_ = lean_ctor_get(v_toConstantVal_2012_, 2);
lean_inc_ref(v_type_2016_);
lean_dec_ref(v_toConstantVal_2012_);
v___x_2017_ = l_Lean_Meta_isPropFormerType(v_type_2016_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; uint8_t v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref(v___x_2017_);
v___x_2019_ = lean_unbox(v_a_2018_);
lean_dec(v_a_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_inc_n(v_indName_1835_, 2);
v___x_2020_ = l_Lean_mkRecName(v_indName_1835_);
v___x_2021_ = l_Lean_mkBelowName(v_indName_1835_);
lean_inc(v___x_2021_);
lean_inc(v_numParams_2013_);
lean_inc(v___x_2020_);
v___x_2022_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2020_, v_numParams_2013_, v___x_2021_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
lean_dec_ref(v___x_2022_);
v___x_2023_ = lean_box(0);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = l_List_get_x21Internal___redArg(v___x_2023_, v_all_2014_, v___x_2024_);
lean_dec(v_all_2014_);
v___x_2026_ = lean_name_eq(v___x_2025_, v_indName_1835_);
lean_dec(v_indName_1835_);
lean_dec(v___x_2025_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
lean_dec(v___x_2021_);
lean_dec(v___x_2020_);
lean_dec(v_numNested_2015_);
lean_dec(v_numParams_2013_);
v___x_2027_ = lean_box(0);
v___y_1961_ = v___x_2006_;
v___y_1962_ = v_a_1972_;
v_a_1963_ = v___x_2027_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2015_, v___x_2020_, v___x_2021_, v_numParams_2013_, v___x_2024_, v___x_2028_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
lean_dec(v_numNested_2015_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_dec_ref(v___x_2029_);
v___y_1961_ = v___x_2006_;
v___y_1962_ = v_a_1972_;
v_a_1963_ = v___x_2028_;
goto v___jp_1960_;
}
else
{
lean_object* v_a_2030_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref(v___x_2029_);
v___y_1966_ = v___x_2006_;
v___y_1967_ = v_a_1972_;
v_a_1968_ = v_a_2030_;
goto v___jp_1965_;
}
}
}
else
{
lean_dec(v___x_2021_);
lean_dec(v___x_2020_);
lean_dec(v_numNested_2015_);
lean_dec(v_all_2014_);
lean_dec(v_numParams_2013_);
lean_dec(v_indName_1835_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2031_; 
v_a_2031_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2022_);
v___y_1961_ = v___x_2006_;
v___y_1962_ = v_a_1972_;
v_a_1963_ = v_a_2031_;
goto v___jp_1960_;
}
else
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2022_);
v___y_1966_ = v___x_2006_;
v___y_1967_ = v_a_1972_;
v_a_1968_ = v_a_2032_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v___x_2033_; 
lean_dec(v_numNested_2015_);
lean_dec(v_all_2014_);
lean_dec(v_numParams_2013_);
lean_dec(v_indName_1835_);
v___x_2033_ = lean_box(0);
v___y_1961_ = v___x_2006_;
v___y_1962_ = v_a_1972_;
v_a_1963_ = v___x_2033_;
goto v___jp_1960_;
}
}
else
{
lean_object* v_a_2034_; 
lean_dec(v_numNested_2015_);
lean_dec(v_all_2014_);
lean_dec(v_numParams_2013_);
lean_dec(v_indName_1835_);
v_a_2034_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2017_);
v___y_1966_ = v___x_2006_;
v___y_1967_ = v_a_1972_;
v_a_1968_ = v_a_2034_;
goto v___jp_1965_;
}
}
}
else
{
lean_object* v___x_2035_; 
lean_dec(v_a_2008_);
lean_dec(v_indName_1835_);
v___x_2035_ = lean_box(0);
v___y_1961_ = v___x_2006_;
v___y_1962_ = v_a_1972_;
v_a_1963_ = v___x_2035_;
goto v___jp_1960_;
}
}
else
{
lean_object* v_a_2036_; 
lean_dec(v_indName_1835_);
v_a_2036_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2036_);
lean_dec_ref(v___x_2007_);
v___y_1966_ = v___x_2006_;
v___y_1967_ = v_a_1972_;
v_a_1968_ = v_a_2036_;
goto v___jp_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_mkBelow(v_indName_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
lean_dec(v_a_2115_);
lean_dec_ref(v_a_2114_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2120_, lean_object* v___x_2121_, lean_object* v___x_2122_, lean_object* v___x_2123_, lean_object* v_inst_2124_, lean_object* v_R_2125_, lean_object* v_a_2126_, lean_object* v_b_2127_, lean_object* v_c_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2120_, v___x_2121_, v___x_2122_, v___x_2123_, v_a_2126_, v_b_2127_, v___y_2129_, v___y_2130_, v___y_2131_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2135_, lean_object* v___x_2136_, lean_object* v___x_2137_, lean_object* v___x_2138_, lean_object* v_inst_2139_, lean_object* v_R_2140_, lean_object* v_a_2141_, lean_object* v_b_2142_, lean_object* v_c_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2135_, v___x_2136_, v___x_2137_, v___x_2138_, v_inst_2139_, v_R_2140_, v_a_2141_, v_b_2142_, v_c_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v___y_2144_);
lean_dec(v_upperBound_2135_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(lean_object* v_00_u03b1_2150_, lean_object* v_x_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___redArg(v_x_2151_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_x_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3_spec__5(v_00_u03b1_2158_, v_x_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2166_, lean_object* v_a_2167_){
_start:
{
if (lean_obj_tag(v_a_2166_) == 0)
{
lean_object* v___x_2168_; 
v___x_2168_ = l_List_reverse___redArg(v_a_2167_);
return v___x_2168_;
}
else
{
lean_object* v_head_2169_; lean_object* v_tail_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2179_; 
v_head_2169_ = lean_ctor_get(v_a_2166_, 0);
v_tail_2170_ = lean_ctor_get(v_a_2166_, 1);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_a_2166_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2172_ = v_a_2166_;
v_isShared_2173_ = v_isSharedCheck_2179_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_tail_2170_);
lean_inc(v_head_2169_);
lean_dec(v_a_2166_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2179_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2174_; lean_object* v___x_2176_; 
v___x_2174_ = l_Lean_MessageData_ofExpr(v_head_2169_);
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v_a_2167_);
lean_ctor_set(v___x_2172_, 0, v___x_2174_);
v___x_2176_ = v___x_2172_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2174_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2167_);
v___x_2176_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
v_a_2166_ = v_tail_2170_;
v_a_2167_ = v___x_2176_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2180_, lean_object* v_v_2181_, lean_object* v_i_2182_){
_start:
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = lean_array_get_size(v_xs_2180_);
v___x_2184_ = lean_nat_dec_lt(v_i_2182_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec(v_i_2182_);
v___x_2185_ = lean_box(0);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = lean_array_fget_borrowed(v_xs_2180_, v_i_2182_);
v___x_2187_ = lean_expr_eqv(v___x_2186_, v_v_2181_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_add(v_i_2182_, v___x_2188_);
lean_dec(v_i_2182_);
v_i_2182_ = v___x_2189_;
goto _start;
}
else
{
lean_object* v___x_2191_; 
v___x_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_i_2182_);
return v___x_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2192_, lean_object* v_v_2193_, lean_object* v_i_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2192_, v_v_2193_, v_i_2194_);
lean_dec_ref(v_v_2193_);
lean_dec_ref(v_xs_2192_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2196_, lean_object* v_v_2197_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_unsigned_to_nat(0u);
v___x_2199_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2196_, v_v_2197_, v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2200_, lean_object* v_v_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2200_, v_v_2201_);
lean_dec_ref(v_v_2201_);
lean_dec_ref(v_xs_2200_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2203_, lean_object* v_v_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2203_, v_v_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v___x_2206_; 
v___x_2206_ = lean_box(0);
return v___x_2206_;
}
else
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
v_val_2207_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2205_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v___x_2205_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_val_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2215_, lean_object* v_v_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2215_, v_v_2216_);
lean_dec_ref(v_v_2216_);
lean_dec_ref(v_xs_2215_);
return v_res_2217_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2220_ = l_Lean_stringToMessageData(v___x_2219_);
return v___x_2220_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2222_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2223_ = l_Lean_stringToMessageData(v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2224_, lean_object* v_prods_2225_, lean_object* v_motives_2226_, lean_object* v_fs_2227_, lean_object* v_minor__type_2228_, lean_object* v_x_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
if (lean_obj_tag(v_x_2229_) == 5)
{
lean_object* v_fn_2237_; lean_object* v_arg_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_fn_2237_ = lean_ctor_get(v_x_2229_, 0);
lean_inc_ref(v_fn_2237_);
v_arg_2238_ = lean_ctor_get(v_x_2229_, 1);
lean_inc_ref(v_arg_2238_);
lean_dec_ref(v_x_2229_);
v___x_2239_ = lean_array_set(v_x_2230_, v_x_2231_, v_arg_2238_);
v___x_2240_ = lean_unsigned_to_nat(1u);
v___x_2241_ = lean_nat_sub(v_x_2231_, v___x_2240_);
lean_dec(v_x_2231_);
v_x_2229_ = v_fn_2237_;
v_x_2230_ = v___x_2239_;
v_x_2231_ = v___x_2241_;
goto _start;
}
else
{
lean_object* v___x_2243_; 
lean_dec(v_x_2231_);
v___x_2243_ = l_Lean_Meta_PProdN_mk(v_rlvl_2224_, v_prods_2225_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; lean_object* v___x_2245_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2226_, v_x_2229_);
lean_dec_ref(v_x_2229_);
if (lean_obj_tag(v___x_2245_) == 1)
{
lean_object* v_val_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_dec_ref(v_minor__type_2228_);
lean_dec_ref(v_motives_2226_);
v_val_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_val_2246_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = l_Lean_instInhabitedExpr;
v___x_2248_ = lean_array_get_borrowed(v___x_2247_, v_fs_2227_, v_val_2246_);
lean_dec(v_val_2246_);
lean_inc(v_a_2244_);
v___x_2249_ = lean_array_push(v_x_2230_, v_a_2244_);
lean_inc(v___x_2248_);
v___x_2250_ = l_Lean_mkAppN(v___x_2248_, v___x_2249_);
lean_dec_ref(v___x_2249_);
v___x_2251_ = l_Lean_Meta_mkPProdMk(v___x_2250_, v_a_2244_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2251_;
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
lean_dec(v___x_2245_);
lean_dec(v_a_2244_);
lean_dec_ref(v_x_2230_);
v___x_2252_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2253_ = l_Lean_MessageData_ofExpr(v_minor__type_2228_);
v___x_2254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2252_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
v___x_2255_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_array_to_list(v_motives_2226_);
v___x_2258_ = lean_box(0);
v___x_2259_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2257_, v___x_2258_);
v___x_2260_ = l_Lean_MessageData_ofList(v___x_2259_);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2256_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2261_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
return v___x_2262_;
}
}
else
{
lean_dec_ref(v_x_2230_);
lean_dec_ref(v_x_2229_);
lean_dec_ref(v_minor__type_2228_);
lean_dec_ref(v_motives_2226_);
return v___x_2243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2263_, lean_object* v_prods_2264_, lean_object* v_motives_2265_, lean_object* v_fs_2266_, lean_object* v_minor__type_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2263_, v_prods_2264_, v_motives_2265_, v_fs_2266_, v_minor__type_2267_, v_x_2268_, v_x_2269_, v_x_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_fs_2266_);
return v_res_2276_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2277_; lean_object* v_dummy_2278_; 
v___x_2277_ = lean_box(0);
v_dummy_2278_ = l_Lean_Expr_sort___override(v___x_2277_);
return v_dummy_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2279_, lean_object* v_head_2280_, lean_object* v_belows_2281_, lean_object* v_prods_2282_, lean_object* v_rlvl_2283_, lean_object* v_fs_2284_, lean_object* v_minor__type_2285_, lean_object* v_tail_2286_, lean_object* v_arg__args_2287_, lean_object* v_arg__type_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2279_, v_head_2280_, v_belows_2281_, v_prods_2282_, v_rlvl_2283_, v_fs_2284_, v_minor__type_2285_, v_tail_2286_, v_arg__args_2287_, v_arg__type_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
lean_dec(v___y_2292_);
lean_dec_ref(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_arg__args_2287_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2295_, lean_object* v_motives_2296_, lean_object* v_belows_2297_, lean_object* v_fs_2298_, lean_object* v_minor__type_2299_, lean_object* v_prods_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_){
_start:
{
if (lean_obj_tag(v_a_2301_) == 0)
{
lean_object* v_dummy_2307_; lean_object* v_nargs_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; 
lean_dec_ref(v_belows_2297_);
v_dummy_2307_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2308_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2299_);
lean_inc(v_nargs_2308_);
v___x_2309_ = lean_mk_array(v_nargs_2308_, v_dummy_2307_);
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_nat_sub(v_nargs_2308_, v___x_2310_);
lean_dec(v_nargs_2308_);
lean_inc_ref(v_minor__type_2299_);
v___x_2312_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2295_, v_prods_2300_, v_motives_2296_, v_fs_2298_, v_minor__type_2299_, v_minor__type_2299_, v___x_2309_, v___x_2311_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
lean_dec_ref(v_fs_2298_);
return v___x_2312_;
}
else
{
lean_object* v_head_2313_; lean_object* v_tail_2314_; lean_object* v___x_2315_; 
v_head_2313_ = lean_ctor_get(v_a_2301_, 0);
lean_inc_n(v_head_2313_, 2);
v_tail_2314_ = lean_ctor_get(v_a_2301_, 1);
lean_inc(v_tail_2314_);
lean_dec_ref(v_a_2301_);
lean_inc(v_a_2305_);
lean_inc_ref(v_a_2304_);
lean_inc(v_a_2303_);
lean_inc_ref(v_a_2302_);
v___x_2315_ = lean_infer_type(v_head_2313_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___f_2317_; uint8_t v___x_2318_; lean_object* v___x_2319_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
v___f_2317_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2317_, 0, v_motives_2296_);
lean_closure_set(v___f_2317_, 1, v_head_2313_);
lean_closure_set(v___f_2317_, 2, v_belows_2297_);
lean_closure_set(v___f_2317_, 3, v_prods_2300_);
lean_closure_set(v___f_2317_, 4, v_rlvl_2295_);
lean_closure_set(v___f_2317_, 5, v_fs_2298_);
lean_closure_set(v___f_2317_, 6, v_minor__type_2299_);
lean_closure_set(v___f_2317_, 7, v_tail_2314_);
v___x_2318_ = 0;
v___x_2319_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2316_, v___f_2317_, v___x_2318_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_);
return v___x_2319_;
}
else
{
lean_dec(v_tail_2314_);
lean_dec(v_head_2313_);
lean_dec_ref(v_prods_2300_);
lean_dec_ref(v_minor__type_2299_);
lean_dec_ref(v_fs_2298_);
lean_dec_ref(v_belows_2297_);
lean_dec_ref(v_motives_2296_);
lean_dec(v_rlvl_2295_);
return v___x_2315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2320_, lean_object* v_rlvl_2321_, lean_object* v_motives_2322_, lean_object* v_belows_2323_, lean_object* v_fs_2324_, lean_object* v_minor__type_2325_, lean_object* v_tail_2326_, uint8_t v___x_2327_, uint8_t v___x_2328_, uint8_t v___x_2329_, lean_object* v_arg_x27_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
lean_inc_ref(v_arg_x27_2330_);
v___x_2336_ = lean_array_push(v_prods_2320_, v_arg_x27_2330_);
v___x_2337_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2321_, v_motives_2322_, v_belows_2323_, v_fs_2324_, v_minor__type_2325_, v___x_2336_, v_tail_2326_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref(v___x_2337_);
v___x_2339_ = lean_unsigned_to_nat(1u);
v___x_2340_ = lean_mk_empty_array_with_capacity(v___x_2339_);
v___x_2341_ = lean_array_push(v___x_2340_, v_arg_x27_2330_);
v___x_2342_ = l_Lean_Meta_mkLambdaFVars(v___x_2341_, v_a_2338_, v___x_2327_, v___x_2328_, v___x_2327_, v___x_2328_, v___x_2329_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
lean_dec_ref(v___x_2341_);
return v___x_2342_;
}
else
{
lean_dec_ref(v_arg_x27_2330_);
return v___x_2337_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2343_, lean_object* v_rlvl_2344_, lean_object* v_motives_2345_, lean_object* v_belows_2346_, lean_object* v_fs_2347_, lean_object* v_minor__type_2348_, lean_object* v_tail_2349_, lean_object* v___x_2350_, lean_object* v___x_2351_, lean_object* v___x_2352_, lean_object* v_arg_x27_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v___x_1776__boxed_2359_; uint8_t v___x_1777__boxed_2360_; uint8_t v___x_1778__boxed_2361_; lean_object* v_res_2362_; 
v___x_1776__boxed_2359_ = lean_unbox(v___x_2350_);
v___x_1777__boxed_2360_ = lean_unbox(v___x_2351_);
v___x_1778__boxed_2361_ = lean_unbox(v___x_2352_);
v_res_2362_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2343_, v_rlvl_2344_, v_motives_2345_, v_belows_2346_, v_fs_2347_, v_minor__type_2348_, v_tail_2349_, v___x_1776__boxed_2359_, v___x_1777__boxed_2360_, v___x_1778__boxed_2361_, v_arg_x27_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2363_, lean_object* v_head_2364_, lean_object* v_belows_2365_, lean_object* v_arg__type_2366_, lean_object* v_prods_2367_, lean_object* v_rlvl_2368_, lean_object* v_fs_2369_, lean_object* v_minor__type_2370_, lean_object* v_tail_2371_, lean_object* v_arg__args_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
if (lean_obj_tag(v_x_2373_) == 5)
{
lean_object* v_fn_2381_; lean_object* v_arg_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v_fn_2381_ = lean_ctor_get(v_x_2373_, 0);
lean_inc_ref(v_fn_2381_);
v_arg_2382_ = lean_ctor_get(v_x_2373_, 1);
lean_inc_ref(v_arg_2382_);
lean_dec_ref(v_x_2373_);
v___x_2383_ = lean_array_set(v_x_2374_, v_x_2375_, v_arg_2382_);
v___x_2384_ = lean_unsigned_to_nat(1u);
v___x_2385_ = lean_nat_sub(v_x_2375_, v___x_2384_);
lean_dec(v_x_2375_);
v_x_2373_ = v_fn_2381_;
v_x_2374_ = v___x_2383_;
v_x_2375_ = v___x_2385_;
goto _start;
}
else
{
lean_object* v___x_2387_; 
lean_dec(v_x_2375_);
v___x_2387_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2363_, v_x_2373_);
lean_dec_ref(v_x_2373_);
if (lean_obj_tag(v___x_2387_) == 1)
{
lean_object* v_val_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v_val_2388_ = lean_ctor_get(v___x_2387_, 0);
lean_inc(v_val_2388_);
lean_dec_ref(v___x_2387_);
v___x_2389_ = l_Lean_Expr_fvarId_x21(v_head_2364_);
lean_dec_ref(v_head_2364_);
v___x_2390_ = l_Lean_FVarId_getUserName___redArg(v___x_2389_, v___y_2376_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2390_);
v___x_2392_ = l_Lean_instInhabitedExpr;
v___x_2393_ = lean_array_get_borrowed(v___x_2392_, v_belows_2365_, v_val_2388_);
lean_dec(v_val_2388_);
lean_inc(v___x_2393_);
v___x_2394_ = l_Lean_mkAppN(v___x_2393_, v_x_2374_);
lean_dec_ref(v_x_2374_);
v___x_2395_ = l_Lean_Meta_mkPProd(v_arg__type_2366_, v___x_2394_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; uint8_t v___x_2397_; uint8_t v___x_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref(v___x_2395_);
v___x_2397_ = 0;
v___x_2398_ = 1;
v___x_2399_ = 1;
v___x_2400_ = l_Lean_Meta_mkForallFVars(v_arg__args_2372_, v_a_2396_, v___x_2397_, v___x_2398_, v___x_2398_, v___x_2399_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___f_2405_; lean_object* v___x_2406_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = lean_box(v___x_2397_);
v___x_2403_ = lean_box(v___x_2398_);
v___x_2404_ = lean_box(v___x_2399_);
v___f_2405_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2405_, 0, v_prods_2367_);
lean_closure_set(v___f_2405_, 1, v_rlvl_2368_);
lean_closure_set(v___f_2405_, 2, v_motives_2363_);
lean_closure_set(v___f_2405_, 3, v_belows_2365_);
lean_closure_set(v___f_2405_, 4, v_fs_2369_);
lean_closure_set(v___f_2405_, 5, v_minor__type_2370_);
lean_closure_set(v___f_2405_, 6, v_tail_2371_);
lean_closure_set(v___f_2405_, 7, v___x_2402_);
lean_closure_set(v___f_2405_, 8, v___x_2403_);
lean_closure_set(v___f_2405_, 9, v___x_2404_);
v___x_2406_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2391_, v_a_2401_, v___f_2405_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2406_;
}
else
{
lean_dec(v_a_2391_);
lean_dec(v_tail_2371_);
lean_dec_ref(v_minor__type_2370_);
lean_dec_ref(v_fs_2369_);
lean_dec(v_rlvl_2368_);
lean_dec_ref(v_prods_2367_);
lean_dec_ref(v_belows_2365_);
lean_dec_ref(v_motives_2363_);
return v___x_2400_;
}
}
else
{
lean_dec(v_a_2391_);
lean_dec(v_tail_2371_);
lean_dec_ref(v_minor__type_2370_);
lean_dec_ref(v_fs_2369_);
lean_dec(v_rlvl_2368_);
lean_dec_ref(v_prods_2367_);
lean_dec_ref(v_belows_2365_);
lean_dec_ref(v_motives_2363_);
return v___x_2395_;
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
lean_dec(v_val_2388_);
lean_dec_ref(v_x_2374_);
lean_dec(v_tail_2371_);
lean_dec_ref(v_minor__type_2370_);
lean_dec_ref(v_fs_2369_);
lean_dec(v_rlvl_2368_);
lean_dec_ref(v_prods_2367_);
lean_dec_ref(v_arg__type_2366_);
lean_dec_ref(v_belows_2365_);
lean_dec_ref(v_motives_2363_);
v_a_2407_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2390_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2390_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
else
{
lean_object* v___x_2415_; 
lean_dec(v___x_2387_);
lean_dec_ref(v_x_2374_);
lean_dec_ref(v_arg__type_2366_);
v___x_2415_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2368_, v_motives_2363_, v_belows_2365_, v_fs_2369_, v_minor__type_2370_, v_prods_2367_, v_tail_2371_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; uint8_t v___x_2421_; uint8_t v___x_2422_; lean_object* v___x_2423_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref(v___x_2415_);
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = lean_mk_empty_array_with_capacity(v___x_2417_);
v___x_2419_ = lean_array_push(v___x_2418_, v_head_2364_);
v___x_2420_ = 0;
v___x_2421_ = 1;
v___x_2422_ = 1;
v___x_2423_ = l_Lean_Meta_mkLambdaFVars(v___x_2419_, v_a_2416_, v___x_2420_, v___x_2421_, v___x_2420_, v___x_2421_, v___x_2422_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec_ref(v___x_2419_);
return v___x_2423_;
}
else
{
lean_dec_ref(v_head_2364_);
return v___x_2415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2424_, lean_object* v_head_2425_, lean_object* v_belows_2426_, lean_object* v_prods_2427_, lean_object* v_rlvl_2428_, lean_object* v_fs_2429_, lean_object* v_minor__type_2430_, lean_object* v_tail_2431_, lean_object* v_arg__args_2432_, lean_object* v_arg__type_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_dummy_2439_; lean_object* v_nargs_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v_dummy_2439_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2440_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2433_);
lean_inc(v_nargs_2440_);
v___x_2441_ = lean_mk_array(v_nargs_2440_, v_dummy_2439_);
v___x_2442_ = lean_unsigned_to_nat(1u);
v___x_2443_ = lean_nat_sub(v_nargs_2440_, v___x_2442_);
lean_dec(v_nargs_2440_);
lean_inc_ref(v_arg__type_2433_);
v___x_2444_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2424_, v_head_2425_, v_belows_2426_, v_arg__type_2433_, v_prods_2427_, v_rlvl_2428_, v_fs_2429_, v_minor__type_2430_, v_tail_2431_, v_arg__args_2432_, v_arg__type_2433_, v___x_2441_, v___x_2443_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2445_, lean_object* v_motives_2446_, lean_object* v_belows_2447_, lean_object* v_fs_2448_, lean_object* v_minor__type_2449_, lean_object* v_prods_2450_, lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_, lean_object* v_a_2455_, lean_object* v_a_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2445_, v_motives_2446_, v_belows_2447_, v_fs_2448_, v_minor__type_2449_, v_prods_2450_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_);
lean_dec(v_a_2455_);
lean_dec_ref(v_a_2454_);
lean_dec(v_a_2453_);
lean_dec_ref(v_a_2452_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2458_ = _args[0];
lean_object* v_head_2459_ = _args[1];
lean_object* v_belows_2460_ = _args[2];
lean_object* v_arg__type_2461_ = _args[3];
lean_object* v_prods_2462_ = _args[4];
lean_object* v_rlvl_2463_ = _args[5];
lean_object* v_fs_2464_ = _args[6];
lean_object* v_minor__type_2465_ = _args[7];
lean_object* v_tail_2466_ = _args[8];
lean_object* v_arg__args_2467_ = _args[9];
lean_object* v_x_2468_ = _args[10];
lean_object* v_x_2469_ = _args[11];
lean_object* v_x_2470_ = _args[12];
lean_object* v___y_2471_ = _args[13];
lean_object* v___y_2472_ = _args[14];
lean_object* v___y_2473_ = _args[15];
lean_object* v___y_2474_ = _args[16];
lean_object* v___y_2475_ = _args[17];
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2458_, v_head_2459_, v_belows_2460_, v_arg__type_2461_, v_prods_2462_, v_rlvl_2463_, v_fs_2464_, v_minor__type_2465_, v_tail_2466_, v_arg__args_2467_, v_x_2468_, v_x_2469_, v_x_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec_ref(v_arg__args_2467_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2477_, lean_object* v_motives_2478_, lean_object* v_belows_2479_, lean_object* v_fs_2480_, lean_object* v_minor__args_2481_, lean_object* v_minor__type_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2489_ = lean_array_to_list(v_minor__args_2481_);
v___x_2490_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2477_, v_motives_2478_, v_belows_2479_, v_fs_2480_, v_minor__type_2482_, v___x_2488_, v___x_2489_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2491_, lean_object* v_motives_2492_, lean_object* v_belows_2493_, lean_object* v_fs_2494_, lean_object* v_minor__args_2495_, lean_object* v_minor__type_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2491_, v_motives_2492_, v_belows_2493_, v_fs_2494_, v_minor__args_2495_, v_minor__type_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2503_, lean_object* v_motives_2504_, lean_object* v_belows_2505_, lean_object* v_fs_2506_, lean_object* v_minorType_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v___f_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
v___f_2513_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2513_, 0, v_rlvl_2503_);
lean_closure_set(v___f_2513_, 1, v_motives_2504_);
lean_closure_set(v___f_2513_, 2, v_belows_2505_);
lean_closure_set(v___f_2513_, 3, v_fs_2506_);
v___x_2514_ = 0;
v___x_2515_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2507_, v___f_2513_, v___x_2514_, v_a_2508_, v_a_2509_, v_a_2510_, v_a_2511_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2516_, lean_object* v_motives_2517_, lean_object* v_belows_2518_, lean_object* v_fs_2519_, lean_object* v_minorType_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2516_, v_motives_2517_, v_belows_2518_, v_fs_2519_, v_minorType_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
lean_dec(v_a_2524_);
lean_dec_ref(v_a_2523_);
lean_dec(v_a_2522_);
lean_dec_ref(v_a_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___f_2533_; lean_object* v___x_27549__overap_2534_; lean_object* v___x_2535_; 
v___f_2533_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27549__overap_2534_ = lean_panic_fn_borrowed(v___f_2533_, v_msg_2527_);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
v___x_2535_ = lean_apply_5(v___x_27549__overap_2534_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, lean_box(0));
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v___x_2546_; 
v___x_2546_ = l_Lean_Expr_hasMVar(v_e_2543_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v_e_2543_);
return v___x_2547_;
}
else
{
lean_object* v___x_2548_; lean_object* v_mctx_2549_; lean_object* v___x_2550_; lean_object* v_fst_2551_; lean_object* v_snd_2552_; lean_object* v___x_2553_; lean_object* v_cache_2554_; lean_object* v_zetaDeltaFVarIds_2555_; lean_object* v_postponed_2556_; lean_object* v_diag_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2566_; 
v___x_2548_ = lean_st_ref_get(v___y_2544_);
v_mctx_2549_ = lean_ctor_get(v___x_2548_, 0);
lean_inc_ref(v_mctx_2549_);
lean_dec(v___x_2548_);
v___x_2550_ = l_Lean_instantiateMVarsCore(v_mctx_2549_, v_e_2543_);
v_fst_2551_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_fst_2551_);
v_snd_2552_ = lean_ctor_get(v___x_2550_, 1);
lean_inc(v_snd_2552_);
lean_dec_ref(v___x_2550_);
v___x_2553_ = lean_st_ref_take(v___y_2544_);
v_cache_2554_ = lean_ctor_get(v___x_2553_, 1);
v_zetaDeltaFVarIds_2555_ = lean_ctor_get(v___x_2553_, 2);
v_postponed_2556_ = lean_ctor_get(v___x_2553_, 3);
v_diag_2557_ = lean_ctor_get(v___x_2553_, 4);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v___x_2553_, 0);
lean_dec(v_unused_2567_);
v___x_2559_ = v___x_2553_;
v_isShared_2560_ = v_isSharedCheck_2566_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_diag_2557_);
lean_inc(v_postponed_2556_);
lean_inc(v_zetaDeltaFVarIds_2555_);
lean_inc(v_cache_2554_);
lean_dec(v___x_2553_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2566_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v_snd_2552_);
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_snd_2552_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_cache_2554_);
lean_ctor_set(v_reuseFailAlloc_2565_, 2, v_zetaDeltaFVarIds_2555_);
lean_ctor_set(v_reuseFailAlloc_2565_, 3, v_postponed_2556_);
lean_ctor_set(v_reuseFailAlloc_2565_, 4, v_diag_2557_);
v___x_2562_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_st_ref_set(v___y_2544_, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2564_, 0, v_fst_2551_);
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2568_, v___y_2569_);
lean_dec(v___y_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2572_, v___y_2574_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; lean_object* v_env_2590_; lean_object* v_toConstantVal_2591_; lean_object* v_value_2592_; lean_object* v_all_2593_; uint8_t v___y_2595_; lean_object* v_type_2603_; uint8_t v___x_2604_; 
v___x_2589_ = lean_st_ref_get(v___y_2587_);
v_env_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc_ref_n(v_env_2590_, 2);
lean_dec(v___x_2589_);
v_toConstantVal_2591_ = lean_ctor_get(v_thm_2586_, 0);
v_value_2592_ = lean_ctor_get(v_thm_2586_, 1);
v_all_2593_ = lean_ctor_get(v_thm_2586_, 2);
v_type_2603_ = lean_ctor_get(v_toConstantVal_2591_, 2);
v___x_2604_ = l_Lean_Environment_hasUnsafe(v_env_2590_, v_type_2603_);
if (v___x_2604_ == 0)
{
uint8_t v___x_2605_; 
v___x_2605_ = l_Lean_Environment_hasUnsafe(v_env_2590_, v_value_2592_);
v___y_2595_ = v___x_2605_;
goto v___jp_2594_;
}
else
{
lean_dec_ref(v_env_2590_);
v___y_2595_ = v___x_2604_;
goto v___jp_2594_;
}
v___jp_2594_:
{
if (v___y_2595_ == 0)
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2596_, 0, v_thm_2586_);
v___x_2597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
else
{
lean_object* v___x_2598_; uint8_t v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
lean_inc(v_all_2593_);
lean_inc_ref(v_value_2592_);
lean_inc_ref(v_toConstantVal_2591_);
lean_dec_ref(v_thm_2586_);
v___x_2598_ = lean_box(0);
v___x_2599_ = 0;
v___x_2600_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2600_, 0, v_toConstantVal_2591_);
lean_ctor_set(v___x_2600_, 1, v_value_2592_);
lean_ctor_set(v___x_2600_, 2, v___x_2598_);
lean_ctor_set(v___x_2600_, 3, v_all_2593_);
lean_ctor_set_uint8(v___x_2600_, sizeof(void*)*4, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2601_);
return v___x_2602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2606_, v___y_2607_);
lean_dec(v___y_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2610_, v___y_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2625_, lean_object* v___x_2626_, lean_object* v___x_2627_, lean_object* v_all_2628_, lean_object* v___x_2629_, lean_object* v___x_2630_, lean_object* v_x_2631_){
_start:
{
lean_object* v___y_2633_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2637_ = lean_array_get_size(v_all_2628_);
v___x_2638_ = lean_nat_dec_lt(v_x_2631_, v___x_2637_);
if (v___x_2638_ == 0)
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2639_ = lean_box(0);
v___x_2640_ = lean_array_get_borrowed(v___x_2639_, v_all_2628_, v___x_2629_);
v___x_2641_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2642_ = lean_nat_sub(v_x_2631_, v___x_2637_);
v___x_2643_ = lean_nat_add(v___x_2642_, v___x_2630_);
lean_dec(v___x_2642_);
v___x_2644_ = l_Nat_reprFast(v___x_2643_);
v___x_2645_ = lean_string_append(v___x_2641_, v___x_2644_);
lean_dec_ref(v___x_2644_);
lean_inc(v___x_2640_);
v___x_2646_ = l_Lean_Name_str___override(v___x_2640_, v___x_2645_);
v___y_2633_ = v___x_2646_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_array_fget_borrowed(v_all_2628_, v_x_2631_);
lean_inc(v___x_2647_);
v___x_2648_ = l_Lean_mkBelowName(v___x_2647_);
v___y_2633_ = v___x_2648_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2634_ = l_Lean_Expr_const___override(v___y_2633_, v___x_2625_);
v___x_2635_ = l_Array_append___redArg(v___x_2626_, v___x_2627_);
v___x_2636_ = l_Lean_mkAppN(v___x_2634_, v___x_2635_);
lean_dec_ref(v___x_2635_);
return v___x_2636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2649_, lean_object* v___x_2650_, lean_object* v___x_2651_, lean_object* v_all_2652_, lean_object* v___x_2653_, lean_object* v___x_2654_, lean_object* v_x_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2649_, v___x_2650_, v___x_2651_, v_all_2652_, v___x_2653_, v___x_2654_, v_x_2655_);
lean_dec(v_x_2655_);
lean_dec(v___x_2654_);
lean_dec(v___x_2653_);
lean_dec_ref(v_all_2652_);
lean_dec_ref(v___x_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2657_, lean_object* v___x_2658_, uint8_t v___x_2659_, lean_object* v_targs_2660_, lean_object* v_x_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = l_Lean_mkAppN(v_a_2657_, v_targs_2660_);
v___x_2668_ = l_Lean_mkAppN(v___x_2658_, v_targs_2660_);
v___x_2669_ = l_Lean_Meta_mkPProd(v___x_2667_, v___x_2668_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; uint8_t v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref(v___x_2669_);
v___x_2671_ = 0;
v___x_2672_ = 1;
v___x_2673_ = l_Lean_Meta_mkLambdaFVars(v_targs_2660_, v_a_2670_, v___x_2671_, v___x_2659_, v___x_2671_, v___x_2659_, v___x_2672_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
return v___x_2673_;
}
else
{
return v___x_2669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2674_, lean_object* v___x_2675_, lean_object* v___x_2676_, lean_object* v_targs_2677_, lean_object* v_x_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_){
_start:
{
uint8_t v___x_30712__boxed_2684_; lean_object* v_res_2685_; 
v___x_30712__boxed_2684_ = lean_unbox(v___x_2676_);
v_res_2685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2674_, v___x_2675_, v___x_30712__boxed_2684_, v_targs_2677_, v_x_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
lean_dec_ref(v_x_2678_);
lean_dec_ref(v_targs_2677_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v_as_2686_, size_t v_sz_2687_, size_t v_i_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
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
lean_object* v_snd_2697_; lean_object* v_fst_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2754_; 
v_snd_2697_ = lean_ctor_get(v_b_2689_, 1);
v_fst_2698_ = lean_ctor_get(v_b_2689_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v_b_2689_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2700_ = v_b_2689_;
v_isShared_2701_ = v_isSharedCheck_2754_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_snd_2697_);
lean_inc(v_fst_2698_);
lean_dec(v_b_2689_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2754_;
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
lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2750_; 
lean_inc(v_stop_2704_);
lean_inc(v_start_2703_);
lean_inc_ref(v_array_2702_);
v_isSharedCheck_2750_ = !lean_is_exclusive(v_snd_2697_);
if (v_isSharedCheck_2750_ == 0)
{
lean_object* v_unused_2751_; lean_object* v_unused_2752_; lean_object* v_unused_2753_; 
v_unused_2751_ = lean_ctor_get(v_snd_2697_, 2);
lean_dec(v_unused_2751_);
v_unused_2752_ = lean_ctor_get(v_snd_2697_, 1);
lean_dec(v_unused_2752_);
v_unused_2753_ = lean_ctor_get(v_snd_2697_, 0);
lean_dec(v_unused_2753_);
v___x_2711_ = v_snd_2697_;
v_isShared_2712_ = v_isSharedCheck_2750_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v_snd_2697_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2750_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_array_uget_borrowed(v_as_2686_, v_i_2688_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v_a_2713_);
v___x_2714_ = lean_infer_type(v_a_2713_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___f_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; 
v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
lean_inc(v_a_2715_);
lean_dec_ref(v___x_2714_);
v___x_2716_ = lean_array_fget_borrowed(v_array_2702_, v_start_2703_);
v___x_2717_ = lean_box(v___x_2705_);
lean_inc(v___x_2716_);
lean_inc(v_a_2713_);
v___f_2718_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2718_, 0, v_a_2713_);
lean_closure_set(v___f_2718_, 1, v___x_2716_);
lean_closure_set(v___f_2718_, 2, v___x_2717_);
v___x_2719_ = 0;
v___x_2720_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2715_, v___f_2718_, v___x_2719_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2725_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref(v___x_2720_);
v___x_2722_ = lean_unsigned_to_nat(1u);
v___x_2723_ = lean_nat_add(v_start_2703_, v___x_2722_);
lean_dec(v_start_2703_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v___x_2723_);
v___x_2725_ = v___x_2711_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_array_2702_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v_stop_2704_);
v___x_2725_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = l_Lean_Expr_app___override(v_fst_2698_, v_a_2721_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2725_);
lean_ctor_set(v___x_2700_, 0, v___x_2726_);
v___x_2728_ = v___x_2700_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2726_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2725_);
v___x_2728_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
size_t v___x_2729_; size_t v___x_2730_; 
v___x_2729_ = ((size_t)1ULL);
v___x_2730_ = lean_usize_add(v_i_2688_, v___x_2729_);
v_i_2688_ = v___x_2730_;
v_b_2689_ = v___x_2728_;
goto _start;
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_del_object(v___x_2711_);
lean_dec(v_stop_2704_);
lean_dec(v_start_2703_);
lean_dec_ref(v_array_2702_);
lean_del_object(v___x_2700_);
lean_dec(v_fst_2698_);
v_a_2734_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2720_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2720_);
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
lean_del_object(v___x_2711_);
lean_dec(v_stop_2704_);
lean_dec(v_start_2703_);
lean_dec_ref(v_array_2702_);
lean_del_object(v___x_2700_);
lean_dec(v_fst_2698_);
v_a_2742_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2714_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2714_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v_as_2755_, lean_object* v_sz_2756_, lean_object* v_i_2757_, lean_object* v_b_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
size_t v_sz_boxed_2764_; size_t v_i_boxed_2765_; lean_object* v_res_2766_; 
v_sz_boxed_2764_ = lean_unbox_usize(v_sz_2756_);
lean_dec(v_sz_2756_);
v_i_boxed_2765_ = lean_unbox_usize(v_i_2757_);
lean_dec(v_i_2757_);
v_res_2766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v_as_2755_, v_sz_boxed_2764_, v_i_boxed_2765_, v_b_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec_ref(v_as_2755_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2767_, size_t v_sz_2768_, size_t v_i_2769_, lean_object* v_b_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_usize_dec_lt(v_i_2769_, v_sz_2768_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_b_2770_);
return v___x_2777_;
}
else
{
lean_object* v_a_2778_; lean_object* v_toInductionSubgoal_2779_; lean_object* v_mvarId_2780_; uint8_t v___x_2781_; lean_object* v___x_2782_; 
v_a_2778_ = lean_array_uget_borrowed(v_as_2767_, v_i_2769_);
v_toInductionSubgoal_2779_ = lean_ctor_get(v_a_2778_, 0);
v_mvarId_2780_ = lean_ctor_get(v_toInductionSubgoal_2779_, 0);
v___x_2781_ = 0;
lean_inc(v_mvarId_2780_);
v___x_2782_ = l_Lean_MVarId_refl(v_mvarId_2780_, v___x_2781_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v___x_2783_; size_t v___x_2784_; size_t v___x_2785_; 
lean_dec_ref(v___x_2782_);
v___x_2783_ = lean_box(0);
v___x_2784_ = ((size_t)1ULL);
v___x_2785_ = lean_usize_add(v_i_2769_, v___x_2784_);
v_i_2769_ = v___x_2785_;
v_b_2770_ = v___x_2783_;
goto _start;
}
else
{
return v___x_2782_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2787_, lean_object* v_sz_2788_, lean_object* v_i_2789_, lean_object* v_b_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
size_t v_sz_boxed_2796_; size_t v_i_boxed_2797_; lean_object* v_res_2798_; 
v_sz_boxed_2796_ = lean_unbox_usize(v_sz_2788_);
lean_dec(v_sz_2788_);
v_i_boxed_2797_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_res_2798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2787_, v_sz_boxed_2796_, v_i_boxed_2797_, v_b_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec_ref(v_as_2787_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2799_, lean_object* v___x_2800_, lean_object* v___x_2801_, lean_object* v_fs_2802_, lean_object* v_as_2803_, size_t v_sz_2804_, size_t v_i_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
uint8_t v___x_2812_; 
v___x_2812_ = lean_usize_dec_lt(v_i_2805_, v_sz_2804_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
lean_dec_ref(v_fs_2802_);
lean_dec_ref(v___x_2801_);
lean_dec_ref(v___x_2800_);
lean_dec(v___x_2799_);
v___x_2813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2813_, 0, v_b_2806_);
return v___x_2813_;
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2815_; 
v_a_2814_ = lean_array_uget_borrowed(v_as_2803_, v_i_2805_);
lean_inc(v___y_2810_);
lean_inc_ref(v___y_2809_);
lean_inc(v___y_2808_);
lean_inc_ref(v___y_2807_);
lean_inc(v_a_2814_);
v___x_2815_ = lean_infer_type(v_a_2814_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref(v___x_2815_);
lean_inc_ref(v_fs_2802_);
lean_inc_ref(v___x_2801_);
lean_inc_ref(v___x_2800_);
lean_inc(v___x_2799_);
v___x_2817_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2799_, v___x_2800_, v___x_2801_, v_fs_2802_, v_a_2816_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2819_; size_t v___x_2820_; size_t v___x_2821_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref(v___x_2817_);
v___x_2819_ = l_Lean_Expr_app___override(v_b_2806_, v_a_2818_);
v___x_2820_ = ((size_t)1ULL);
v___x_2821_ = lean_usize_add(v_i_2805_, v___x_2820_);
v_i_2805_ = v___x_2821_;
v_b_2806_ = v___x_2819_;
goto _start;
}
else
{
lean_dec_ref(v_b_2806_);
lean_dec_ref(v_fs_2802_);
lean_dec_ref(v___x_2801_);
lean_dec_ref(v___x_2800_);
lean_dec(v___x_2799_);
return v___x_2817_;
}
}
else
{
lean_dec_ref(v_b_2806_);
lean_dec_ref(v_fs_2802_);
lean_dec_ref(v___x_2801_);
lean_dec_ref(v___x_2800_);
lean_dec(v___x_2799_);
return v___x_2815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2823_, lean_object* v___x_2824_, lean_object* v___x_2825_, lean_object* v_fs_2826_, lean_object* v_as_2827_, lean_object* v_sz_2828_, lean_object* v_i_2829_, lean_object* v_b_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
size_t v_sz_boxed_2836_; size_t v_i_boxed_2837_; lean_object* v_res_2838_; 
v_sz_boxed_2836_ = lean_unbox_usize(v_sz_2828_);
lean_dec(v_sz_2828_);
v_i_boxed_2837_ = lean_unbox_usize(v_i_2829_);
lean_dec(v_i_2829_);
v_res_2838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2823_, v___x_2824_, v___x_2825_, v_fs_2826_, v_as_2827_, v_sz_boxed_2836_, v_i_boxed_2837_, v_b_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec_ref(v_as_2827_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2839_, lean_object* v_tail_2840_, lean_object* v_recName_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v___x_2844_, size_t v_sz_2845_, size_t v___x_2846_, lean_object* v___x_2847_, lean_object* v___x_2848_, lean_object* v___x_2849_, lean_object* v___x_2850_, lean_object* v___x_2851_, lean_object* v___x_2852_, lean_object* v_val_2853_, uint8_t v___x_2854_, lean_object* v_brecOnGoName_2855_, lean_object* v_levelParams_2856_, lean_object* v___x_2857_, lean_object* v_brecOnName_2858_, lean_object* v___x_2859_, lean_object* v_brecOnEqName_2860_, lean_object* v_fs_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_inc(v___x_2839_);
v___x_2867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2839_);
lean_ctor_set(v___x_2867_, 1, v_tail_2840_);
v___x_2868_ = l_Lean_Expr_const___override(v_recName_2841_, v___x_2867_);
v___x_2869_ = l_Lean_mkAppN(v___x_2868_, v___x_2842_);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
lean_ctor_set(v___x_2870_, 1, v___x_2843_);
v___x_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2844_, v_sz_2845_, v___x_2846_, v___x_2870_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v_fst_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_3238_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
v_fst_2873_ = lean_ctor_get(v_a_2872_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v_a_2872_);
if (v_isSharedCheck_3238_ == 0)
{
lean_object* v_unused_3239_; 
v_unused_3239_ = lean_ctor_get(v_a_2872_, 1);
lean_dec(v_unused_3239_);
v___x_2875_ = v_a_2872_;
v_isShared_2876_ = v_isSharedCheck_3238_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_fst_2873_);
lean_dec(v_a_2872_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_3238_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
size_t v_sz_2877_; lean_object* v___x_2878_; 
v_sz_2877_ = lean_array_size(v___x_2847_);
lean_inc_ref(v_fs_2861_);
lean_inc_ref(v___x_2848_);
lean_inc_ref(v___x_2844_);
v___x_2878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2839_, v___x_2844_, v___x_2848_, v_fs_2861_, v___x_2847_, v_sz_2877_, v___x_2846_, v_fst_2873_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_a_2879_);
lean_dec_ref(v___x_2878_);
v___x_2880_ = l_Lean_mkAppN(v_a_2879_, v___x_2849_);
lean_inc_ref_n(v___x_2850_, 3);
v___x_2881_ = l_Lean_Expr_app___override(v___x_2880_, v___x_2850_);
v___x_2882_ = l_Array_append___redArg(v___x_2842_, v___x_2844_);
v___x_2883_ = l_Array_append___redArg(v___x_2882_, v___x_2849_);
v___x_2884_ = lean_mk_empty_array_with_capacity(v___x_2851_);
v___x_2885_ = lean_array_push(v___x_2884_, v___x_2850_);
v___x_2886_ = lean_array_get(v___x_2852_, v___x_2844_, v_val_2853_);
lean_dec_ref(v___x_2844_);
v___x_2887_ = lean_array_push(v___x_2849_, v___x_2850_);
v___x_2888_ = l_Lean_mkAppN(v___x_2886_, v___x_2887_);
v___x_2889_ = lean_array_get(v___x_2852_, v___x_2848_, v_val_2853_);
lean_dec_ref(v___x_2848_);
v___x_2890_ = l_Lean_mkAppN(v___x_2889_, v___x_2887_);
lean_inc_ref(v___x_2888_);
v___x_2891_ = l_Lean_Meta_mkPProd(v___x_2888_, v___x_2890_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; uint8_t v___x_2896_; lean_object* v___x_2897_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
v___x_2893_ = l_Array_append___redArg(v___x_2883_, v___x_2885_);
lean_dec_ref(v___x_2885_);
v___x_2894_ = l_Array_append___redArg(v___x_2893_, v_fs_2861_);
v___x_2895_ = 0;
v___x_2896_ = 1;
v___x_2897_ = l_Lean_Meta_mkForallFVars(v___x_2894_, v_a_2892_, v___x_2895_, v___x_2854_, v___x_2854_, v___x_2896_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2899_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2899_ = l_Lean_Meta_mkLambdaFVars(v___x_2894_, v___x_2881_, v___x_2895_, v___x_2854_, v___x_2895_, v___x_2854_, v___x_2896_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_3205_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2899_);
v___x_2901_ = lean_box(1);
lean_inc(v_levelParams_2856_);
lean_inc(v_brecOnGoName_2855_);
v___x_2902_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2855_, v_levelParams_2856_, v_a_2898_, v_a_2900_, v___x_2901_, v___y_2865_);
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_3205_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_3205_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
lean_inc(v_a_2903_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 1);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_3204_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Lean_addDecl(v___x_2908_, v___x_2895_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_toConstantVal_2910_; lean_object* v_name_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3201_; 
lean_dec_ref(v___x_2909_);
v_toConstantVal_2910_ = lean_ctor_get(v_a_2903_, 0);
lean_inc_ref(v_toConstantVal_2910_);
lean_dec(v_a_2903_);
v_name_2911_ = lean_ctor_get(v_toConstantVal_2910_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_toConstantVal_2910_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; lean_object* v_unused_3203_; 
v_unused_3202_ = lean_ctor_get(v_toConstantVal_2910_, 2);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_toConstantVal_2910_, 1);
lean_dec(v_unused_3203_);
v___x_2913_ = v_toConstantVal_2910_;
v_isShared_2914_ = v_isSharedCheck_3201_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_name_2911_);
lean_dec(v_toConstantVal_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3201_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v_env_2917_; lean_object* v_nextMacroScope_2918_; lean_object* v_ngen_2919_; lean_object* v_auxDeclNGen_2920_; lean_object* v_traceState_2921_; lean_object* v_messages_2922_; lean_object* v_infoState_2923_; lean_object* v_snapshotTasks_2924_; lean_object* v_newDecls_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_3199_; 
lean_inc(v_name_2911_);
v___x_2915_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2911_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec_ref(v___x_2915_);
v___x_2916_ = lean_st_ref_take(v___y_2865_);
v_env_2917_ = lean_ctor_get(v___x_2916_, 0);
v_nextMacroScope_2918_ = lean_ctor_get(v___x_2916_, 1);
v_ngen_2919_ = lean_ctor_get(v___x_2916_, 2);
v_auxDeclNGen_2920_ = lean_ctor_get(v___x_2916_, 3);
v_traceState_2921_ = lean_ctor_get(v___x_2916_, 4);
v_messages_2922_ = lean_ctor_get(v___x_2916_, 6);
v_infoState_2923_ = lean_ctor_get(v___x_2916_, 7);
v_snapshotTasks_2924_ = lean_ctor_get(v___x_2916_, 8);
v_newDecls_2925_ = lean_ctor_get(v___x_2916_, 9);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_3199_ == 0)
{
lean_object* v_unused_3200_; 
v_unused_3200_ = lean_ctor_get(v___x_2916_, 5);
lean_dec(v_unused_3200_);
v___x_2927_ = v___x_2916_;
v_isShared_2928_ = v_isSharedCheck_3199_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_newDecls_2925_);
lean_inc(v_snapshotTasks_2924_);
lean_inc(v_infoState_2923_);
lean_inc(v_messages_2922_);
lean_inc(v_traceState_2921_);
lean_inc(v_auxDeclNGen_2920_);
lean_inc(v_ngen_2919_);
lean_inc(v_nextMacroScope_2918_);
lean_inc(v_env_2917_);
lean_dec(v___x_2916_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_3199_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2929_ = l_Lean_addProtected(v_env_2917_, v_name_2911_);
v___x_2930_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 5, v___x_2930_);
lean_ctor_set(v___x_2927_, 0, v___x_2929_);
v___x_2932_ = v___x_2927_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v___x_2929_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_nextMacroScope_2918_);
lean_ctor_set(v_reuseFailAlloc_3198_, 2, v_ngen_2919_);
lean_ctor_set(v_reuseFailAlloc_3198_, 3, v_auxDeclNGen_2920_);
lean_ctor_set(v_reuseFailAlloc_3198_, 4, v_traceState_2921_);
lean_ctor_set(v_reuseFailAlloc_3198_, 5, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3198_, 6, v_messages_2922_);
lean_ctor_set(v_reuseFailAlloc_3198_, 7, v_infoState_2923_);
lean_ctor_set(v_reuseFailAlloc_3198_, 8, v_snapshotTasks_2924_);
lean_ctor_set(v_reuseFailAlloc_3198_, 9, v_newDecls_2925_);
v___x_2932_ = v_reuseFailAlloc_3198_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v_mctx_2935_; lean_object* v_zetaDeltaFVarIds_2936_; lean_object* v_postponed_2937_; lean_object* v_diag_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_3196_; 
v___x_2933_ = lean_st_ref_set(v___y_2865_, v___x_2932_);
v___x_2934_ = lean_st_ref_take(v___y_2863_);
v_mctx_2935_ = lean_ctor_get(v___x_2934_, 0);
v_zetaDeltaFVarIds_2936_ = lean_ctor_get(v___x_2934_, 2);
v_postponed_2937_ = lean_ctor_get(v___x_2934_, 3);
v_diag_2938_ = lean_ctor_get(v___x_2934_, 4);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_3196_ == 0)
{
lean_object* v_unused_3197_; 
v_unused_3197_ = lean_ctor_get(v___x_2934_, 1);
lean_dec(v_unused_3197_);
v___x_2940_ = v___x_2934_;
v_isShared_2941_ = v_isSharedCheck_3196_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_diag_2938_);
lean_inc(v_postponed_2937_);
lean_inc(v_zetaDeltaFVarIds_2936_);
lean_inc(v_mctx_2935_);
lean_dec(v___x_2934_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_3196_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2942_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 1, v___x_2942_);
v___x_2944_ = v___x_2940_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_mctx_2935_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_3195_, 2, v_zetaDeltaFVarIds_2936_);
lean_ctor_set(v_reuseFailAlloc_3195_, 3, v_postponed_2937_);
lean_ctor_set(v_reuseFailAlloc_3195_, 4, v_diag_2938_);
v___x_2944_ = v_reuseFailAlloc_3195_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2945_ = lean_st_ref_set(v___y_2863_, v___x_2944_);
lean_inc(v___x_2857_);
v___x_2946_ = l_Lean_Expr_const___override(v_brecOnGoName_2855_, v___x_2857_);
v___x_2947_ = l_Lean_mkAppN(v___x_2946_, v___x_2894_);
lean_inc_ref(v___x_2947_);
v___x_2948_ = l_Lean_Meta_mkPProdFstM(v___x_2947_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2950_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref(v___x_2948_);
v___x_2950_ = l_Lean_Meta_mkLambdaFVars(v___x_2894_, v_a_2949_, v___x_2895_, v___x_2854_, v___x_2895_, v___x_2854_, v___x_2896_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref(v___x_2950_);
v___x_2952_ = l_Lean_Meta_mkForallFVars(v___x_2894_, v___x_2888_, v___x_2895_, v___x_2854_, v___x_2854_, v___x_2896_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3170_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref(v___x_2952_);
lean_inc(v_levelParams_2856_);
v___x_2954_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2858_, v_levelParams_2856_, v_a_2953_, v_a_2951_, v___x_2901_, v___y_2865_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_3170_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3170_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
lean_inc(v_a_2955_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set_tag(v___x_2957_, 1);
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_3169_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_addDecl(v___x_2960_, v___x_2895_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_toConstantVal_2962_; lean_object* v_name_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_3166_; 
lean_dec_ref(v___x_2961_);
v_toConstantVal_2962_ = lean_ctor_get(v_a_2955_, 0);
lean_inc_ref(v_toConstantVal_2962_);
lean_dec(v_a_2955_);
v_name_2963_ = lean_ctor_get(v_toConstantVal_2962_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_toConstantVal_2962_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3167_ = lean_ctor_get(v_toConstantVal_2962_, 2);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_toConstantVal_2962_, 1);
lean_dec(v_unused_3168_);
v___x_2965_ = v_toConstantVal_2962_;
v_isShared_2966_ = v_isSharedCheck_3166_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_name_2963_);
lean_dec(v_toConstantVal_2962_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_3166_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_env_2969_; lean_object* v_nextMacroScope_2970_; lean_object* v_ngen_2971_; lean_object* v_auxDeclNGen_2972_; lean_object* v_traceState_2973_; lean_object* v_messages_2974_; lean_object* v_infoState_2975_; lean_object* v_snapshotTasks_2976_; lean_object* v_newDecls_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3164_; 
lean_inc(v_name_2963_);
v___x_2967_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2963_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec_ref(v___x_2967_);
v___x_2968_ = lean_st_ref_take(v___y_2865_);
v_env_2969_ = lean_ctor_get(v___x_2968_, 0);
v_nextMacroScope_2970_ = lean_ctor_get(v___x_2968_, 1);
v_ngen_2971_ = lean_ctor_get(v___x_2968_, 2);
v_auxDeclNGen_2972_ = lean_ctor_get(v___x_2968_, 3);
v_traceState_2973_ = lean_ctor_get(v___x_2968_, 4);
v_messages_2974_ = lean_ctor_get(v___x_2968_, 6);
v_infoState_2975_ = lean_ctor_get(v___x_2968_, 7);
v_snapshotTasks_2976_ = lean_ctor_get(v___x_2968_, 8);
v_newDecls_2977_ = lean_ctor_get(v___x_2968_, 9);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; 
v_unused_3165_ = lean_ctor_get(v___x_2968_, 5);
lean_dec(v_unused_3165_);
v___x_2979_ = v___x_2968_;
v_isShared_2980_ = v_isSharedCheck_3164_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_newDecls_2977_);
lean_inc(v_snapshotTasks_2976_);
lean_inc(v_infoState_2975_);
lean_inc(v_messages_2974_);
lean_inc(v_traceState_2973_);
lean_inc(v_auxDeclNGen_2972_);
lean_inc(v_ngen_2971_);
lean_inc(v_nextMacroScope_2970_);
lean_inc(v_env_2969_);
lean_dec(v___x_2968_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3164_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v___x_2983_; 
lean_inc(v_name_2963_);
v___x_2981_ = l_Lean_markAuxRecursor(v_env_2969_, v_name_2963_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 5, v___x_2930_);
lean_ctor_set(v___x_2979_, 0, v___x_2981_);
v___x_2983_ = v___x_2979_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_2981_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_nextMacroScope_2970_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v_ngen_2971_);
lean_ctor_set(v_reuseFailAlloc_3163_, 3, v_auxDeclNGen_2972_);
lean_ctor_set(v_reuseFailAlloc_3163_, 4, v_traceState_2973_);
lean_ctor_set(v_reuseFailAlloc_3163_, 5, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3163_, 6, v_messages_2974_);
lean_ctor_set(v_reuseFailAlloc_3163_, 7, v_infoState_2975_);
lean_ctor_set(v_reuseFailAlloc_3163_, 8, v_snapshotTasks_2976_);
lean_ctor_set(v_reuseFailAlloc_3163_, 9, v_newDecls_2977_);
v___x_2983_ = v_reuseFailAlloc_3163_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_mctx_2986_; lean_object* v_zetaDeltaFVarIds_2987_; lean_object* v_postponed_2988_; lean_object* v_diag_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3161_; 
v___x_2984_ = lean_st_ref_set(v___y_2865_, v___x_2983_);
v___x_2985_ = lean_st_ref_take(v___y_2863_);
v_mctx_2986_ = lean_ctor_get(v___x_2985_, 0);
v_zetaDeltaFVarIds_2987_ = lean_ctor_get(v___x_2985_, 2);
v_postponed_2988_ = lean_ctor_get(v___x_2985_, 3);
v_diag_2989_ = lean_ctor_get(v___x_2985_, 4);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v___x_2985_, 1);
lean_dec(v_unused_3162_);
v___x_2991_ = v___x_2985_;
v_isShared_2992_ = v_isSharedCheck_3161_;
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
v_isShared_2992_ = v_isSharedCheck_3161_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 1, v___x_2942_);
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_mctx_2986_);
lean_ctor_set(v_reuseFailAlloc_3160_, 1, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_3160_, 2, v_zetaDeltaFVarIds_2987_);
lean_ctor_set(v_reuseFailAlloc_3160_, 3, v_postponed_2988_);
lean_ctor_set(v_reuseFailAlloc_3160_, 4, v_diag_2989_);
v___x_2994_ = v_reuseFailAlloc_3160_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_env_2997_; lean_object* v_nextMacroScope_2998_; lean_object* v_ngen_2999_; lean_object* v_auxDeclNGen_3000_; lean_object* v_traceState_3001_; lean_object* v_messages_3002_; lean_object* v_infoState_3003_; lean_object* v_snapshotTasks_3004_; lean_object* v_newDecls_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3158_; 
v___x_2995_ = lean_st_ref_set(v___y_2863_, v___x_2994_);
v___x_2996_ = lean_st_ref_take(v___y_2865_);
v_env_2997_ = lean_ctor_get(v___x_2996_, 0);
v_nextMacroScope_2998_ = lean_ctor_get(v___x_2996_, 1);
v_ngen_2999_ = lean_ctor_get(v___x_2996_, 2);
v_auxDeclNGen_3000_ = lean_ctor_get(v___x_2996_, 3);
v_traceState_3001_ = lean_ctor_get(v___x_2996_, 4);
v_messages_3002_ = lean_ctor_get(v___x_2996_, 6);
v_infoState_3003_ = lean_ctor_get(v___x_2996_, 7);
v_snapshotTasks_3004_ = lean_ctor_get(v___x_2996_, 8);
v_newDecls_3005_ = lean_ctor_get(v___x_2996_, 9);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3158_ == 0)
{
lean_object* v_unused_3159_; 
v_unused_3159_ = lean_ctor_get(v___x_2996_, 5);
lean_dec(v_unused_3159_);
v___x_3007_ = v___x_2996_;
v_isShared_3008_ = v_isSharedCheck_3158_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_newDecls_3005_);
lean_inc(v_snapshotTasks_3004_);
lean_inc(v_infoState_3003_);
lean_inc(v_messages_3002_);
lean_inc(v_traceState_3001_);
lean_inc(v_auxDeclNGen_3000_);
lean_inc(v_ngen_2999_);
lean_inc(v_nextMacroScope_2998_);
lean_inc(v_env_2997_);
lean_dec(v___x_2996_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3158_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_inc(v_name_2963_);
v___x_3009_ = l_Lean_addProtected(v_env_2997_, v_name_2963_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 5, v___x_2930_);
lean_ctor_set(v___x_3007_, 0, v___x_3009_);
v___x_3011_ = v___x_3007_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3157_, 1, v_nextMacroScope_2998_);
lean_ctor_set(v_reuseFailAlloc_3157_, 2, v_ngen_2999_);
lean_ctor_set(v_reuseFailAlloc_3157_, 3, v_auxDeclNGen_3000_);
lean_ctor_set(v_reuseFailAlloc_3157_, 4, v_traceState_3001_);
lean_ctor_set(v_reuseFailAlloc_3157_, 5, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3157_, 6, v_messages_3002_);
lean_ctor_set(v_reuseFailAlloc_3157_, 7, v_infoState_3003_);
lean_ctor_set(v_reuseFailAlloc_3157_, 8, v_snapshotTasks_3004_);
lean_ctor_set(v_reuseFailAlloc_3157_, 9, v_newDecls_3005_);
v___x_3011_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v_mctx_3014_; lean_object* v_zetaDeltaFVarIds_3015_; lean_object* v_postponed_3016_; lean_object* v_diag_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3155_; 
v___x_3012_ = lean_st_ref_set(v___y_2865_, v___x_3011_);
v___x_3013_ = lean_st_ref_take(v___y_2863_);
v_mctx_3014_ = lean_ctor_get(v___x_3013_, 0);
v_zetaDeltaFVarIds_3015_ = lean_ctor_get(v___x_3013_, 2);
v_postponed_3016_ = lean_ctor_get(v___x_3013_, 3);
v_diag_3017_ = lean_ctor_get(v___x_3013_, 4);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3155_ == 0)
{
lean_object* v_unused_3156_; 
v_unused_3156_ = lean_ctor_get(v___x_3013_, 1);
lean_dec(v_unused_3156_);
v___x_3019_ = v___x_3013_;
v_isShared_3020_ = v_isSharedCheck_3155_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_diag_3017_);
lean_inc(v_postponed_3016_);
lean_inc(v_zetaDeltaFVarIds_3015_);
lean_inc(v_mctx_3014_);
lean_dec(v___x_3013_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3155_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 1, v___x_2942_);
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_mctx_3014_);
lean_ctor_set(v_reuseFailAlloc_3154_, 1, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_3154_, 2, v_zetaDeltaFVarIds_3015_);
lean_ctor_set(v_reuseFailAlloc_3154_, 3, v_postponed_3016_);
lean_ctor_set(v_reuseFailAlloc_3154_, 4, v_diag_3017_);
v___x_3022_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = lean_st_ref_set(v___y_2863_, v___x_3022_);
v___x_3024_ = l_Lean_Meta_mkPProdSndM(v___x_2947_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = l_Lean_Expr_const___override(v_name_2963_, v___x_2857_);
v___x_3027_ = l_Lean_mkAppN(v___x_3026_, v___x_2894_);
v___x_3028_ = lean_array_get(v___x_2852_, v_fs_2861_, v_val_2853_);
lean_dec_ref(v_fs_2861_);
v___x_3029_ = l_Lean_mkAppN(v___x_3028_, v___x_2887_);
lean_dec_ref(v___x_2887_);
v___x_3030_ = l_Lean_Expr_app___override(v___x_3029_, v_a_3025_);
v___x_3031_ = l_Lean_Meta_mkEq(v___x_3027_, v___x_3030_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc_n(v_a_3032_, 2);
lean_dec_ref(v___x_3031_);
v___x_3033_ = lean_box(0);
v___x_3034_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3032_, v___x_3033_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref(v___x_3034_);
v___x_3036_ = l_Lean_Expr_mvarId_x21(v_a_3035_);
v___x_3037_ = l_Lean_Expr_fvarId_x21(v___x_2850_);
lean_dec_ref(v___x_2850_);
v___x_3038_ = lean_mk_empty_array_with_capacity(v___x_2859_);
v___x_3039_ = lean_box(0);
v___x_3040_ = l_Lean_MVarId_cases(v___x_3036_, v___x_3037_, v___x_3038_, v___x_2895_, v___x_3039_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; size_t v_sz_3043_; lean_object* v___x_3044_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref(v___x_3040_);
v___x_3042_ = lean_box(0);
v_sz_3043_ = lean_array_size(v_a_3041_);
v___x_3044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3041_, v_sz_3043_, v___x_2846_, v___x_3042_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec(v_a_3041_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v___x_3045_; lean_object* v_a_3046_; lean_object* v___x_3047_; 
lean_dec_ref(v___x_3044_);
v___x_3045_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_3035_, v___y_2863_);
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref(v___x_3045_);
v___x_3047_ = l_Lean_Meta_mkForallFVars(v___x_2894_, v_a_3032_, v___x_2895_, v___x_2854_, v___x_2854_, v___x_2896_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = l_Lean_Meta_mkLambdaFVars(v___x_2894_, v_a_3046_, v___x_2895_, v___x_2854_, v___x_2895_, v___x_2854_, v___x_2896_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec_ref(v___x_2894_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v_a_3050_; lean_object* v___x_3052_; 
v_a_3050_ = lean_ctor_get(v___x_3049_, 0);
lean_inc(v_a_3050_);
lean_dec_ref(v___x_3049_);
lean_inc(v_brecOnEqName_2860_);
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 2, v_a_3048_);
lean_ctor_set(v___x_2965_, 1, v_levelParams_2856_);
lean_ctor_set(v___x_2965_, 0, v_brecOnEqName_2860_);
v___x_3052_ = v___x_2965_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_brecOnEqName_2860_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_levelParams_2856_);
lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_a_3048_);
v___x_3052_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(0);
lean_inc(v_brecOnEqName_2860_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set_tag(v___x_2875_, 1);
lean_ctor_set(v___x_2875_, 1, v___x_3053_);
lean_ctor_set(v___x_2875_, 0, v_brecOnEqName_2860_);
v___x_3055_ = v___x_2875_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_brecOnEqName_2860_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3057_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 2, v___x_3055_);
lean_ctor_set(v___x_2913_, 1, v_a_3050_);
lean_ctor_set(v___x_2913_, 0, v___x_3052_);
v___x_3057_ = v___x_2913_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_a_3050_);
lean_ctor_set(v_reuseFailAlloc_3103_, 2, v___x_3055_);
v___x_3057_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
lean_object* v___x_3058_; lean_object* v_a_3059_; lean_object* v___x_3060_; 
v___x_3058_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3057_, v___y_2865_);
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = l_Lean_addDecl(v_a_3059_, v___x_2895_, v___y_2864_, v___y_2865_);
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
lean_object* v___x_3064_; lean_object* v_env_3065_; lean_object* v_nextMacroScope_3066_; lean_object* v_ngen_3067_; lean_object* v_auxDeclNGen_3068_; lean_object* v_traceState_3069_; lean_object* v_messages_3070_; lean_object* v_infoState_3071_; lean_object* v_snapshotTasks_3072_; lean_object* v_newDecls_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3099_; 
v___x_3064_ = lean_st_ref_take(v___y_2865_);
v_env_3065_ = lean_ctor_get(v___x_3064_, 0);
v_nextMacroScope_3066_ = lean_ctor_get(v___x_3064_, 1);
v_ngen_3067_ = lean_ctor_get(v___x_3064_, 2);
v_auxDeclNGen_3068_ = lean_ctor_get(v___x_3064_, 3);
v_traceState_3069_ = lean_ctor_get(v___x_3064_, 4);
v_messages_3070_ = lean_ctor_get(v___x_3064_, 6);
v_infoState_3071_ = lean_ctor_get(v___x_3064_, 7);
v_snapshotTasks_3072_ = lean_ctor_get(v___x_3064_, 8);
v_newDecls_3073_ = lean_ctor_get(v___x_3064_, 9);
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
lean_inc(v_newDecls_3073_);
lean_inc(v_snapshotTasks_3072_);
lean_inc(v_infoState_3071_);
lean_inc(v_messages_3070_);
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
v___x_3077_ = l_Lean_addProtected(v_env_3065_, v_brecOnEqName_2860_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 5, v___x_2930_);
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
lean_ctor_set(v_reuseFailAlloc_3098_, 5, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_3098_, 6, v_messages_3070_);
lean_ctor_set(v_reuseFailAlloc_3098_, 7, v_infoState_3071_);
lean_ctor_set(v_reuseFailAlloc_3098_, 8, v_snapshotTasks_3072_);
lean_ctor_set(v_reuseFailAlloc_3098_, 9, v_newDecls_3073_);
v___x_3079_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v_mctx_3082_; lean_object* v_zetaDeltaFVarIds_3083_; lean_object* v_postponed_3084_; lean_object* v_diag_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3096_; 
v___x_3080_ = lean_st_ref_set(v___y_2865_, v___x_3079_);
v___x_3081_ = lean_st_ref_take(v___y_2863_);
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
lean_ctor_set(v___x_3087_, 1, v___x_2942_);
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_mctx_3082_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_2942_);
lean_ctor_set(v_reuseFailAlloc_3095_, 2, v_zetaDeltaFVarIds_3083_);
lean_ctor_set(v_reuseFailAlloc_3095_, 3, v_postponed_3084_);
lean_ctor_set(v_reuseFailAlloc_3095_, 4, v_diag_3085_);
v___x_3090_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3093_; 
v___x_3091_ = lean_st_ref_set(v___y_2863_, v___x_3090_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3042_);
v___x_3093_ = v___x_3062_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3042_);
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
lean_dec(v_brecOnEqName_2860_);
return v___x_3060_;
}
}
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_3048_);
lean_del_object(v___x_2965_);
lean_del_object(v___x_2913_);
lean_del_object(v___x_2875_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_levelParams_2856_);
v_a_3106_ = lean_ctor_get(v___x_3049_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3049_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3049_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v_a_3046_);
lean_del_object(v___x_2965_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_del_object(v___x_2875_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_levelParams_2856_);
v_a_3114_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3047_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3047_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_dec(v_a_3035_);
lean_dec(v_a_3032_);
lean_del_object(v___x_2965_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_del_object(v___x_2875_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_levelParams_2856_);
return v___x_3044_;
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_a_3035_);
lean_dec(v_a_3032_);
lean_del_object(v___x_2965_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_del_object(v___x_2875_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_levelParams_2856_);
v_a_3122_ = lean_ctor_get(v___x_3040_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3040_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3040_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec(v_a_3032_);
lean_del_object(v___x_2965_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_del_object(v___x_2875_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_levelParams_2856_);
lean_dec_ref(v___x_2850_);
v_a_3130_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3034_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3034_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_del_object(v___x_2965_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_del_object(v___x_2875_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_levelParams_2856_);
lean_dec_ref(v___x_2850_);
v_a_3138_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3031_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3031_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_del_object(v___x_2965_);
lean_dec(v_name_2963_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec_ref(v___x_2850_);
v_a_3146_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3024_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3024_);
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
lean_dec(v_a_2955_);
lean_dec_ref(v___x_2947_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec_ref(v___x_2850_);
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec(v_a_2951_);
lean_dec_ref(v___x_2947_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec_ref(v___x_2850_);
v_a_3171_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_2952_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_2952_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref(v___x_2947_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec_ref(v___x_2850_);
v_a_3179_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_2950_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_2950_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v___x_2947_);
lean_del_object(v___x_2913_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec_ref(v___x_2850_);
v_a_3187_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_2948_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_2948_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
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
lean_dec(v_a_2903_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec(v_brecOnGoName_2855_);
lean_dec_ref(v___x_2850_);
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_2898_);
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec(v_brecOnGoName_2855_);
lean_dec_ref(v___x_2850_);
v_a_3206_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_2899_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_2899_);
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
lean_dec_ref(v___x_2894_);
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2881_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec(v_brecOnGoName_2855_);
lean_dec_ref(v___x_2850_);
v_a_3214_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_2897_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_2897_);
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
lean_dec_ref(v___x_2888_);
lean_dec_ref(v___x_2887_);
lean_dec_ref(v___x_2885_);
lean_dec_ref(v___x_2883_);
lean_dec_ref(v___x_2881_);
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec(v_brecOnGoName_2855_);
lean_dec_ref(v___x_2850_);
v_a_3222_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_3229_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_3229_ == 0)
{
v___x_3224_ = v___x_2891_;
v_isShared_3225_ = v_isSharedCheck_3229_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_a_3222_);
lean_dec(v___x_2891_);
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
lean_del_object(v___x_2875_);
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec(v_brecOnGoName_2855_);
lean_dec_ref(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2844_);
lean_dec_ref(v___x_2842_);
v_a_3230_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_2878_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_2878_);
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
lean_dec_ref(v_fs_2861_);
lean_dec(v_brecOnEqName_2860_);
lean_dec(v_brecOnName_2858_);
lean_dec(v___x_2857_);
lean_dec(v_levelParams_2856_);
lean_dec(v_brecOnGoName_2855_);
lean_dec_ref(v___x_2850_);
lean_dec_ref(v___x_2849_);
lean_dec_ref(v___x_2848_);
lean_dec_ref(v___x_2844_);
lean_dec_ref(v___x_2842_);
lean_dec(v___x_2839_);
v_a_3240_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_2871_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_2871_);
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
lean_object* v_sz_3254_ = _args[6];
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
lean_object* v_brecOnName_3267_ = _args[19];
lean_object* v___x_3268_ = _args[20];
lean_object* v_brecOnEqName_3269_ = _args[21];
lean_object* v_fs_3270_ = _args[22];
lean_object* v___y_3271_ = _args[23];
lean_object* v___y_3272_ = _args[24];
lean_object* v___y_3273_ = _args[25];
lean_object* v___y_3274_ = _args[26];
lean_object* v___y_3275_ = _args[27];
_start:
{
size_t v_sz_boxed_3276_; size_t v___x_30970__boxed_3277_; uint8_t v___x_30978__boxed_3278_; lean_object* v_res_3279_; 
v_sz_boxed_3276_ = lean_unbox_usize(v_sz_3254_);
lean_dec(v_sz_3254_);
v___x_30970__boxed_3277_ = lean_unbox_usize(v___x_3255_);
lean_dec(v___x_3255_);
v___x_30978__boxed_3278_ = lean_unbox(v___x_3263_);
v_res_3279_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3248_, v_tail_3249_, v_recName_3250_, v___x_3251_, v___x_3252_, v___x_3253_, v_sz_boxed_3276_, v___x_30970__boxed_3277_, v___x_3256_, v___x_3257_, v___x_3258_, v___x_3259_, v___x_3260_, v___x_3261_, v_val_3262_, v___x_30978__boxed_3278_, v_brecOnGoName_3264_, v_levelParams_3265_, v___x_3266_, v_brecOnName_3267_, v___x_3268_, v_brecOnEqName_3269_, v_fs_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___x_3268_);
lean_dec(v_val_3262_);
lean_dec_ref(v___x_3261_);
lean_dec(v___x_3260_);
lean_dec_ref(v___x_3256_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3280_, lean_object* v_a_3281_, uint8_t v___x_3282_, lean_object* v_f_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; uint8_t v___x_3292_; lean_object* v___x_3293_; 
lean_inc_ref(v_targs_3280_);
v___x_3289_ = lean_array_push(v_targs_3280_, v_f_3283_);
v___x_3290_ = l_Lean_mkAppN(v_a_3281_, v_targs_3280_);
lean_dec_ref(v_targs_3280_);
v___x_3291_ = 0;
v___x_3292_ = 1;
v___x_3293_ = l_Lean_Meta_mkForallFVars(v___x_3289_, v___x_3290_, v___x_3291_, v___x_3282_, v___x_3282_, v___x_3292_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec_ref(v___x_3289_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3294_, lean_object* v_a_3295_, lean_object* v___x_3296_, lean_object* v_f_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
uint8_t v___x_31688__boxed_3303_; lean_object* v_res_3304_; 
v___x_31688__boxed_3303_ = lean_unbox(v___x_3296_);
v_res_3304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3294_, v_a_3295_, v___x_31688__boxed_3303_, v_f_3297_, v___y_3298_, v___y_3299_, v___y_3300_, v___y_3301_);
lean_dec(v___y_3301_);
lean_dec_ref(v___y_3300_);
lean_dec(v___y_3299_);
lean_dec_ref(v___y_3298_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3308_, uint8_t v___x_3309_, lean_object* v___x_3310_, lean_object* v_targs_3311_, lean_object* v_x_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v___x_3318_; lean_object* v___f_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3318_ = lean_box(v___x_3309_);
lean_inc_ref(v_targs_3311_);
v___f_3319_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3319_, 0, v_targs_3311_);
lean_closure_set(v___f_3319_, 1, v_a_3308_);
lean_closure_set(v___f_3319_, 2, v___x_3318_);
v___x_3320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3321_ = l_Lean_mkAppN(v___x_3310_, v_targs_3311_);
lean_dec_ref(v_targs_3311_);
v___x_3322_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3320_, v___x_3321_, v___f_3319_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3323_, lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v_targs_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
uint8_t v___x_31722__boxed_3333_; lean_object* v_res_3334_; 
v___x_31722__boxed_3333_ = lean_unbox(v___x_3324_);
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3323_, v___x_31722__boxed_3333_, v___x_3325_, v_targs_3326_, v_x_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec_ref(v_x_3327_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3335_, lean_object* v_x_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3342_, 0, v_a_3335_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3343_, lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3343_, v_x_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v_x_3344_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v_as_3352_, size_t v_sz_3353_, size_t v_i_3354_, lean_object* v_b_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
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
lean_object* v_snd_3363_; lean_object* v_fst_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3460_; 
v_snd_3363_ = lean_ctor_get(v_b_3355_, 1);
v_fst_3364_ = lean_ctor_get(v_b_3355_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_b_3355_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3366_ = v_b_3355_;
v_isShared_3367_ = v_isSharedCheck_3460_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_snd_3363_);
lean_inc(v_fst_3364_);
lean_dec(v_b_3355_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3460_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v_fst_3368_; lean_object* v_snd_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3459_; 
v_fst_3368_ = lean_ctor_get(v_snd_3363_, 0);
v_snd_3369_ = lean_ctor_get(v_snd_3363_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_snd_3363_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3371_ = v_snd_3363_;
v_isShared_3372_ = v_isSharedCheck_3459_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_snd_3369_);
lean_inc(v_fst_3368_);
lean_dec(v_snd_3363_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3459_;
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
lean_object* v_upperBound_3382_; lean_object* v_val_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3458_; 
v_upperBound_3382_ = lean_ctor_get(v_snd_3369_, 1);
v_val_3383_ = lean_ctor_get(v_next_3381_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v_next_3381_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3385_ = v_next_3381_;
v_isShared_3386_ = v_isSharedCheck_3458_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_val_3383_);
lean_dec(v_next_3381_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3458_;
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
lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3455_; 
lean_inc(v_upperBound_3382_);
lean_del_object(v___x_3371_);
lean_del_object(v___x_3366_);
v_isSharedCheck_3455_ = !lean_is_exclusive(v_snd_3369_);
if (v_isSharedCheck_3455_ == 0)
{
lean_object* v_unused_3456_; lean_object* v_unused_3457_; 
v_unused_3456_ = lean_ctor_get(v_snd_3369_, 1);
lean_dec(v_unused_3456_);
v_unused_3457_ = lean_ctor_get(v_snd_3369_, 0);
lean_dec(v_unused_3457_);
v___x_3389_ = v_snd_3369_;
v_isShared_3390_ = v_isSharedCheck_3455_;
goto v_resetjp_3388_;
}
else
{
lean_dec(v_snd_3369_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3455_;
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
lean_object* v_reuseFailAlloc_3454_; 
v_reuseFailAlloc_3454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3454_;
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
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3397_);
lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_upperBound_3382_);
v___x_3399_ = v_reuseFailAlloc_3453_;
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
lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3449_; 
lean_inc(v_stop_3393_);
lean_inc(v_start_3392_);
lean_inc_ref(v_array_3391_);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_fst_3368_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; lean_object* v_unused_3451_; lean_object* v_unused_3452_; 
v_unused_3450_ = lean_ctor_get(v_fst_3368_, 2);
lean_dec(v_unused_3450_);
v_unused_3451_ = lean_ctor_get(v_fst_3368_, 1);
lean_dec(v_unused_3451_);
v_unused_3452_ = lean_ctor_get(v_fst_3368_, 0);
lean_dec(v_unused_3452_);
v___x_3405_ = v_fst_3368_;
v_isShared_3406_ = v_isSharedCheck_3449_;
goto v_resetjp_3404_;
}
else
{
lean_dec(v_fst_3368_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3449_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v_a_3407_; lean_object* v___x_3408_; 
v_a_3407_ = lean_array_uget_borrowed(v_as_3352_, v_i_3354_);
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
lean_inc(v_a_3407_);
v___x_3408_ = lean_infer_type(v_a_3407_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___f_3412_; uint8_t v___x_3413_; lean_object* v___x_3414_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = lean_array_fget_borrowed(v_array_3391_, v_start_3392_);
v___x_3411_ = lean_box(v___x_3400_);
lean_inc(v___x_3410_);
lean_inc(v_a_3407_);
v___f_3412_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3412_, 0, v_a_3407_);
lean_closure_set(v___f_3412_, 1, v___x_3411_);
lean_closure_set(v___f_3412_, 2, v___x_3410_);
v___x_3413_ = 0;
v___x_3414_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3409_, v___f_3412_, v___x_3413_, v___y_3356_, v___y_3357_, v___y_3358_, v___y_3359_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; lean_object* v___x_3419_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref(v___x_3414_);
v___f_3416_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3416_, 0, v_a_3415_);
v___x_3417_ = lean_nat_add(v_start_3392_, v___x_3394_);
lean_dec(v_start_3392_);
if (v_isShared_3406_ == 0)
{
lean_ctor_set(v___x_3405_, 1, v___x_3417_);
v___x_3419_ = v___x_3405_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_array_3391_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v___x_3417_);
lean_ctor_set(v_reuseFailAlloc_3432_, 2, v_stop_3393_);
v___x_3419_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; size_t v___x_3429_; size_t v___x_3430_; 
v___x_3420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3421_ = l_Nat_reprFast(v___x_3395_);
v___x_3422_ = lean_string_append(v___x_3420_, v___x_3421_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = lean_box(0);
v___x_3424_ = l_Lean_Name_str___override(v___x_3423_, v___x_3422_);
v___x_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
lean_ctor_set(v___x_3425_, 1, v___f_3416_);
v___x_3426_ = lean_array_push(v_fst_3364_, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3419_);
lean_ctor_set(v___x_3427_, 1, v___x_3399_);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = ((size_t)1ULL);
v___x_3430_ = lean_usize_add(v_i_3354_, v___x_3429_);
v_i_3354_ = v___x_3430_;
v_b_3355_ = v___x_3428_;
goto _start;
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
lean_del_object(v___x_3405_);
lean_dec_ref(v___x_3399_);
lean_dec(v___x_3395_);
lean_dec(v_stop_3393_);
lean_dec(v_start_3392_);
lean_dec_ref(v_array_3391_);
lean_dec(v_fst_3364_);
v_a_3433_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3435_ = v___x_3414_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3414_);
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
lean_del_object(v___x_3405_);
lean_dec_ref(v___x_3399_);
lean_dec(v___x_3395_);
lean_dec(v_stop_3393_);
lean_dec(v_start_3392_);
lean_dec_ref(v_array_3391_);
lean_dec(v_fst_3364_);
v_a_3441_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3443_ = v___x_3408_;
v_isShared_3444_ = v_isSharedCheck_3448_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v___x_3408_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v_as_3461_, lean_object* v_sz_3462_, lean_object* v_i_3463_, lean_object* v_b_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
size_t v_sz_boxed_3470_; size_t v_i_boxed_3471_; lean_object* v_res_3472_; 
v_sz_boxed_3470_ = lean_unbox_usize(v_sz_3462_);
lean_dec(v_sz_3462_);
v_i_boxed_3471_ = lean_unbox_usize(v_i_3463_);
lean_dec(v_i_3463_);
v_res_3472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v_as_3461_, v_sz_boxed_3470_, v_i_boxed_3471_, v_b_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec_ref(v_as_3461_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3473_, size_t v_i_3474_, lean_object* v_bs_3475_){
_start:
{
uint8_t v___x_3476_; 
v___x_3476_ = lean_usize_dec_lt(v_i_3474_, v_sz_3473_);
if (v___x_3476_ == 0)
{
return v_bs_3475_;
}
else
{
lean_object* v_v_3477_; lean_object* v_fst_3478_; lean_object* v_snd_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3495_; 
v_v_3477_ = lean_array_uget(v_bs_3475_, v_i_3474_);
v_fst_3478_ = lean_ctor_get(v_v_3477_, 0);
v_snd_3479_ = lean_ctor_get(v_v_3477_, 1);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_v_3477_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3481_ = v_v_3477_;
v_isShared_3482_ = v_isSharedCheck_3495_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_snd_3479_);
lean_inc(v_fst_3478_);
lean_dec(v_v_3477_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3495_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v_bs_x27_3484_; uint8_t v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v___x_3483_ = lean_unsigned_to_nat(0u);
v_bs_x27_3484_ = lean_array_uset(v_bs_3475_, v_i_3474_, v___x_3483_);
v___x_3485_ = 0;
v___x_3486_ = lean_box(v___x_3485_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3486_);
v___x_3488_ = v___x_3481_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_snd_3479_);
v___x_3488_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; size_t v___x_3490_; size_t v___x_3491_; lean_object* v___x_3492_; 
v___x_3489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3489_, 0, v_fst_3478_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = ((size_t)1ULL);
v___x_3491_ = lean_usize_add(v_i_3474_, v___x_3490_);
v___x_3492_ = lean_array_uset(v_bs_x27_3484_, v_i_3474_, v___x_3489_);
v_i_3474_ = v___x_3491_;
v_bs_3475_ = v___x_3492_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3496_, lean_object* v_i_3497_, lean_object* v_bs_3498_){
_start:
{
size_t v_sz_boxed_3499_; size_t v_i_boxed_3500_; lean_object* v_res_3501_; 
v_sz_boxed_3499_ = lean_unbox_usize(v_sz_3496_);
lean_dec(v_sz_3496_);
v_i_boxed_3500_ = lean_unbox_usize(v_i_3497_);
lean_dec(v_i_3497_);
v_res_3501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3499_, v_i_boxed_3500_, v_bs_3498_);
return v_res_3501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(lean_object* v___x_3502_, lean_object* v_a_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_30531__overap_3510_; lean_object* v___x_3511_; 
v___x_3509_ = l_Lean_instInhabitedExpr;
v___x_30531__overap_3510_ = l_instInhabitedOfMonad___redArg(v___x_3502_, v___x_3509_);
lean_inc(v___y_3507_);
lean_inc_ref(v___y_3506_);
lean_inc(v___y_3505_);
lean_inc_ref(v___y_3504_);
v___x_3511_ = lean_apply_5(v___x_30531__overap_3510_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_, lean_box(0));
return v___x_3511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed(lean_object* v___x_3512_, lean_object* v_a_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0(v___x_3512_, v_a_3513_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec_ref(v___y_3516_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec_ref(v_a_3513_);
return v_res_3519_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_instMonadEIO(lean_box(0));
return v___x_3520_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__0);
v___x_3522_ = l_StateRefT_x27_instMonad___redArg(v___x_3521_);
return v___x_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed(lean_object* v_acc_3527_, lean_object* v_declInfos_3528_, lean_object* v_k_3529_, lean_object* v_kind_3530_, lean_object* v_b_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
uint8_t v_kind_boxed_3537_; lean_object* v_res_3538_; 
v_kind_boxed_3537_ = lean_unbox(v_kind_3530_);
v_res_3538_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(v_acc_3527_, v_declInfos_3528_, v_k_3529_, v_kind_boxed_3537_, v_b_3531_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_acc_3539_, lean_object* v_declInfos_3540_, lean_object* v_k_3541_, uint8_t v_kind_3542_, lean_object* v_name_3543_, uint8_t v_bi_3544_, lean_object* v_type_3545_, uint8_t v_kind_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_box(v_kind_3542_);
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3553_, 0, v_acc_3539_);
lean_closure_set(v___f_3553_, 1, v_declInfos_3540_);
lean_closure_set(v___f_3553_, 2, v_k_3541_);
lean_closure_set(v___f_3553_, 3, v___x_3552_);
v___x_3554_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3543_, v_bi_3544_, v_type_3545_, v___f_3553_, v_kind_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3554_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3554_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
else
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
v_a_3563_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3554_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3554_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_declInfos_3571_, lean_object* v_k_3572_, uint8_t v_kind_3573_, lean_object* v_acc_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; lean_object* v_toApplicative_3581_; lean_object* v_toFunctor_3582_; lean_object* v_toSeq_3583_; lean_object* v_toSeqLeft_3584_; lean_object* v_toSeqRight_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___x_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v_toApplicative_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3652_; 
v___x_3580_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__1);
v_toApplicative_3581_ = lean_ctor_get(v___x_3580_, 0);
v_toFunctor_3582_ = lean_ctor_get(v_toApplicative_3581_, 0);
v_toSeq_3583_ = lean_ctor_get(v_toApplicative_3581_, 2);
v_toSeqLeft_3584_ = lean_ctor_get(v_toApplicative_3581_, 3);
v_toSeqRight_3585_ = lean_ctor_get(v_toApplicative_3581_, 4);
v___f_3586_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__2));
v___f_3587_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__3));
lean_inc_ref_n(v_toFunctor_3582_, 2);
v___f_3588_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3588_, 0, v_toFunctor_3582_);
v___f_3589_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3589_, 0, v_toFunctor_3582_);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___f_3588_);
lean_ctor_set(v___x_3590_, 1, v___f_3589_);
lean_inc(v_toSeqRight_3585_);
v___f_3591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3591_, 0, v_toSeqRight_3585_);
lean_inc(v_toSeqLeft_3584_);
v___f_3592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3592_, 0, v_toSeqLeft_3584_);
lean_inc(v_toSeq_3583_);
v___f_3593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3593_, 0, v_toSeq_3583_);
v___x_3594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3590_);
lean_ctor_set(v___x_3594_, 1, v___f_3586_);
lean_ctor_set(v___x_3594_, 2, v___f_3593_);
lean_ctor_set(v___x_3594_, 3, v___f_3592_);
lean_ctor_set(v___x_3594_, 4, v___f_3591_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v___f_3587_);
v___x_3596_ = l_StateRefT_x27_instMonad___redArg(v___x_3595_);
v_toApplicative_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; 
v_unused_3653_ = lean_ctor_get(v___x_3596_, 1);
lean_dec(v_unused_3653_);
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3652_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_toApplicative_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3652_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v_toFunctor_3601_; lean_object* v_toSeq_3602_; lean_object* v_toSeqLeft_3603_; lean_object* v_toSeqRight_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3650_; 
v_toFunctor_3601_ = lean_ctor_get(v_toApplicative_3597_, 0);
v_toSeq_3602_ = lean_ctor_get(v_toApplicative_3597_, 2);
v_toSeqLeft_3603_ = lean_ctor_get(v_toApplicative_3597_, 3);
v_toSeqRight_3604_ = lean_ctor_get(v_toApplicative_3597_, 4);
v_isSharedCheck_3650_ = !lean_is_exclusive(v_toApplicative_3597_);
if (v_isSharedCheck_3650_ == 0)
{
lean_object* v_unused_3651_; 
v_unused_3651_ = lean_ctor_get(v_toApplicative_3597_, 1);
lean_dec(v_unused_3651_);
v___x_3606_ = v_toApplicative_3597_;
v_isShared_3607_ = v_isSharedCheck_3650_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_toSeqRight_3604_);
lean_inc(v_toSeqLeft_3603_);
lean_inc(v_toSeq_3602_);
lean_inc(v_toFunctor_3601_);
lean_dec(v_toApplicative_3597_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3650_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___f_3608_; lean_object* v___f_3609_; lean_object* v___f_3610_; lean_object* v___f_3611_; lean_object* v___x_3612_; lean_object* v___f_3613_; lean_object* v___f_3614_; lean_object* v___f_3615_; lean_object* v___x_3617_; 
v___f_3608_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__4));
v___f_3609_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___closed__5));
lean_inc_ref(v_toFunctor_3601_);
v___f_3610_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3610_, 0, v_toFunctor_3601_);
v___f_3611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3611_, 0, v_toFunctor_3601_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___f_3610_);
lean_ctor_set(v___x_3612_, 1, v___f_3611_);
v___f_3613_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3613_, 0, v_toSeqRight_3604_);
v___f_3614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3614_, 0, v_toSeqLeft_3603_);
v___f_3615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3615_, 0, v_toSeq_3602_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set(v___x_3606_, 4, v___f_3613_);
lean_ctor_set(v___x_3606_, 3, v___f_3614_);
lean_ctor_set(v___x_3606_, 2, v___f_3615_);
lean_ctor_set(v___x_3606_, 1, v___f_3608_);
lean_ctor_set(v___x_3606_, 0, v___x_3612_);
v___x_3617_ = v___x_3606_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3649_, 1, v___f_3608_);
lean_ctor_set(v_reuseFailAlloc_3649_, 2, v___f_3615_);
lean_ctor_set(v_reuseFailAlloc_3649_, 3, v___f_3614_);
lean_ctor_set(v_reuseFailAlloc_3649_, 4, v___f_3613_);
v___x_3617_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3619_; 
if (v_isShared_3600_ == 0)
{
lean_ctor_set(v___x_3599_, 1, v___f_3609_);
lean_ctor_set(v___x_3599_, 0, v___x_3617_);
v___x_3619_ = v___x_3599_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v___f_3609_);
v___x_3619_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3620_ = lean_array_get_size(v_acc_3574_);
v___x_3621_ = lean_array_get_size(v_declInfos_3571_);
v___x_3622_ = lean_nat_dec_lt(v___x_3620_, v___x_3621_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; 
lean_dec_ref(v___x_3619_);
lean_dec_ref(v_declInfos_3571_);
lean_inc(v___y_3578_);
lean_inc_ref(v___y_3577_);
lean_inc(v___y_3576_);
lean_inc_ref(v___y_3575_);
v___x_3623_ = lean_apply_6(v_k_3572_, v_acc_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, lean_box(0));
return v___x_3623_;
}
else
{
lean_object* v___f_3624_; lean_object* v___x_3625_; uint8_t v___x_3626_; lean_object* v___f_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_snd_3632_; lean_object* v_fst_3633_; lean_object* v_fst_3634_; lean_object* v_snd_3635_; lean_object* v___x_3636_; 
v___f_3624_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3624_, 0, v___x_3619_);
v___x_3625_ = lean_box(0);
v___x_3626_ = 0;
v___f_3627_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3627_, 0, v___f_3624_);
v___x_3628_ = lean_box(v___x_3626_);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3628_);
lean_ctor_set(v___x_3629_, 1, v___f_3627_);
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3625_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_array_get(v___x_3630_, v_declInfos_3571_, v___x_3620_);
lean_dec_ref(v___x_3630_);
v_snd_3632_ = lean_ctor_get(v___x_3631_, 1);
lean_inc(v_snd_3632_);
v_fst_3633_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_fst_3633_);
lean_dec(v___x_3631_);
v_fst_3634_ = lean_ctor_get(v_snd_3632_, 0);
lean_inc(v_fst_3634_);
v_snd_3635_ = lean_ctor_get(v_snd_3632_, 1);
lean_inc(v_snd_3635_);
lean_dec(v_snd_3632_);
lean_inc(v___y_3578_);
lean_inc_ref(v___y_3577_);
lean_inc(v___y_3576_);
lean_inc_ref(v___y_3575_);
lean_inc_ref(v_acc_3574_);
v___x_3636_ = lean_apply_6(v_snd_3635_, v_acc_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_, lean_box(0));
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_object* v_a_3637_; uint8_t v___x_3638_; lean_object* v___x_3639_; 
v_a_3637_ = lean_ctor_get(v___x_3636_, 0);
lean_inc(v_a_3637_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = lean_unbox(v_fst_3634_);
lean_dec(v_fst_3634_);
v___x_3639_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3574_, v_declInfos_3571_, v_k_3572_, v_kind_3573_, v_fst_3633_, v___x_3638_, v_a_3637_, v_kind_3573_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
return v___x_3639_;
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec(v_fst_3634_);
lean_dec(v_fst_3633_);
lean_dec_ref(v_acc_3574_);
lean_dec_ref(v_k_3572_);
lean_dec_ref(v_declInfos_3571_);
v_a_3640_ = lean_ctor_get(v___x_3636_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3636_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3636_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3636_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___lam__0(lean_object* v_acc_3654_, lean_object* v_declInfos_3655_, lean_object* v_k_3656_, uint8_t v_kind_3657_, lean_object* v_b_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3664_ = lean_array_push(v_acc_3654_, v_b_3658_);
v___x_3665_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3655_, v_k_3656_, v_kind_3657_, v___x_3664_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_acc_3666_, lean_object* v_declInfos_3667_, lean_object* v_k_3668_, lean_object* v_kind_3669_, lean_object* v_name_3670_, lean_object* v_bi_3671_, lean_object* v_type_3672_, lean_object* v_kind_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
uint8_t v_kind_boxed_3679_; uint8_t v_bi_boxed_3680_; uint8_t v_kind_boxed_3681_; lean_object* v_res_3682_; 
v_kind_boxed_3679_ = lean_unbox(v_kind_3669_);
v_bi_boxed_3680_ = lean_unbox(v_bi_3671_);
v_kind_boxed_3681_ = lean_unbox(v_kind_3673_);
v_res_3682_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_acc_3666_, v_declInfos_3667_, v_k_3668_, v_kind_boxed_3679_, v_name_3670_, v_bi_boxed_3680_, v_type_3672_, v_kind_boxed_3681_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_declInfos_3683_, lean_object* v_k_3684_, lean_object* v_kind_3685_, lean_object* v_acc_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
uint8_t v_kind_boxed_3692_; lean_object* v_res_3693_; 
v_kind_boxed_3692_ = lean_unbox(v_kind_3685_);
v_res_3693_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3683_, v_k_3684_, v_kind_boxed_3692_, v_acc_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
return v_res_3693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_declInfos_3694_, lean_object* v_k_3695_, uint8_t v_kind_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3703_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_declInfos_3694_, v_k_3695_, v_kind_3696_, v___x_3702_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_declInfos_3704_, lean_object* v_k_3705_, lean_object* v_kind_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
uint8_t v_kind_boxed_3712_; lean_object* v_res_3713_; 
v_kind_boxed_3712_ = lean_unbox(v_kind_3706_);
v_res_3713_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_declInfos_3704_, v_k_3705_, v_kind_boxed_3712_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec(v___y_3708_);
lean_dec_ref(v___y_3707_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_declInfos_3714_, lean_object* v_k_3715_, uint8_t v_kind_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
size_t v_sz_3722_; size_t v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_sz_3722_ = lean_array_size(v_declInfos_3714_);
v___x_3723_ = ((size_t)0ULL);
v___x_3724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3722_, v___x_3723_, v_declInfos_3714_);
v___x_3725_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v___x_3724_, v_k_3715_, v_kind_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_declInfos_3726_, lean_object* v_k_3727_, lean_object* v_kind_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v_kind_boxed_3734_; lean_object* v_res_3735_; 
v_kind_boxed_3734_ = lean_unbox(v_kind_3728_);
v_res_3735_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_declInfos_3726_, v_k_3727_, v_kind_boxed_3734_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
return v_res_3735_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3737_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3738_ = lean_unsigned_to_nat(4u);
v___x_3739_ = lean_unsigned_to_nat(202u);
v___x_3740_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3741_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3742_ = l_mkPanicMessageWithDecl(v___x_3741_, v___x_3740_, v___x_3739_, v___x_3738_, v___x_3737_);
return v___x_3742_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3748_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3749_ = l_Lean_stringToMessageData(v___x_3748_);
return v___x_3749_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3752_ = l_Lean_stringToMessageData(v___x_3751_);
return v___x_3752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3755_, lean_object* v_numMotives_3756_, lean_object* v_numMinors_3757_, lean_object* v___x_3758_, lean_object* v_all_3759_, lean_object* v_head_3760_, lean_object* v_tail_3761_, lean_object* v_recName_3762_, lean_object* v_brecOnGoName_3763_, lean_object* v_levelParams_3764_, lean_object* v_brecOnName_3765_, lean_object* v_brecOnEqName_3766_, lean_object* v_type_3767_, lean_object* v_refArgs_3768_, lean_object* v_refBody_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; 
v___x_3775_ = lean_nat_add(v_nParams_3755_, v_numMotives_3756_);
v___x_3776_ = lean_nat_add(v___x_3775_, v_numMinors_3757_);
v___x_3777_ = lean_array_get_size(v_refArgs_3768_);
v___x_3778_ = lean_nat_dec_lt(v___x_3776_, v___x_3777_);
if (v___x_3778_ == 0)
{
lean_object* v___x_3779_; lean_object* v___x_3780_; 
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec_ref(v_refArgs_3768_);
lean_dec_ref(v_type_3767_);
lean_dec(v_brecOnEqName_3766_);
lean_dec(v_brecOnName_3765_);
lean_dec(v_levelParams_3764_);
lean_dec(v_brecOnGoName_3763_);
lean_dec(v_recName_3762_);
lean_dec(v_tail_3761_);
lean_dec(v_head_3760_);
lean_dec_ref(v_all_3759_);
lean_dec(v___x_3758_);
lean_dec(v_nParams_3755_);
v___x_3779_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3780_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3779_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3780_;
}
else
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3781_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3755_);
lean_inc_ref_n(v_refArgs_3768_, 2);
v___x_3782_ = l_Array_toSubarray___redArg(v_refArgs_3768_, v___x_3781_, v_nParams_3755_);
lean_inc(v___x_3775_);
v___x_3783_ = l_Array_toSubarray___redArg(v_refArgs_3768_, v_nParams_3755_, v___x_3775_);
v___x_3784_ = l_Subarray_copy___redArg(v___x_3783_);
v___x_3785_ = l_Lean_Expr_getAppFn(v_refBody_3769_);
v___x_3786_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3784_, v___x_3785_);
lean_dec_ref(v___x_3785_);
if (lean_obj_tag(v___x_3786_) == 1)
{
lean_object* v_val_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
lean_dec_ref(v_type_3767_);
v_val_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc(v_val_3787_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = l_Lean_instInhabitedExpr;
v___x_3789_ = lean_unsigned_to_nat(1u);
v___x_3790_ = lean_nat_sub(v___x_3777_, v___x_3789_);
v___x_3791_ = lean_array_get(v___x_3788_, v_refArgs_3768_, v___x_3790_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
lean_inc(v___y_3771_);
lean_inc_ref(v___y_3770_);
lean_inc(v___x_3791_);
v___x_3792_ = lean_infer_type(v___x_3791_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref(v___x_3792_);
lean_inc(v___y_3773_);
lean_inc_ref(v___y_3772_);
lean_inc(v___y_3771_);
lean_inc_ref(v___y_3770_);
v___x_3794_ = lean_infer_type(v_a_3793_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref(v___x_3794_);
v___x_3796_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3795_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref(v___x_3796_);
if (lean_obj_tag(v_a_3797_) == 1)
{
lean_object* v_val_3798_; lean_object* v___x_3799_; lean_object* v___f_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; size_t v_sz_3810_; size_t v___x_3811_; lean_object* v___x_3812_; 
v_val_3798_ = lean_ctor_get(v_a_3797_, 0);
lean_inc(v_val_3798_);
lean_dec_ref(v_a_3797_);
v___x_3799_ = l_Subarray_copy___redArg(v___x_3782_);
lean_inc_ref(v___x_3784_);
lean_inc_ref(v___x_3799_);
lean_inc(v___x_3758_);
v___f_3800_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3800_, 0, v___x_3758_);
lean_closure_set(v___f_3800_, 1, v___x_3799_);
lean_closure_set(v___f_3800_, 2, v___x_3784_);
lean_closure_set(v___f_3800_, 3, v_all_3759_);
lean_closure_set(v___f_3800_, 4, v___x_3781_);
lean_closure_set(v___f_3800_, 5, v___x_3789_);
v___x_3801_ = lean_array_get_size(v___x_3784_);
v___x_3802_ = l_Array_ofFn___redArg(v___x_3801_, v___f_3800_);
v___x_3803_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3804_ = lean_array_get_size(v___x_3802_);
lean_inc_ref(v___x_3802_);
v___x_3805_ = l_Array_toSubarray___redArg(v___x_3802_, v___x_3781_, v___x_3804_);
v___x_3806_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v___x_3801_);
lean_inc_ref(v___x_3805_);
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3805_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3803_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v_sz_3810_ = lean_array_size(v___x_3784_);
v___x_3811_ = ((size_t)0ULL);
v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3784_, v_sz_3810_, v___x_3811_, v___x_3809_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v_fst_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___f_3823_; uint8_t v___x_3824_; lean_object* v___x_3825_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3812_);
v_fst_3814_ = lean_ctor_get(v_a_3813_, 0);
lean_inc(v_fst_3814_);
lean_dec(v_a_3813_);
lean_inc(v___x_3776_);
lean_inc_ref(v_refArgs_3768_);
v___x_3815_ = l_Array_toSubarray___redArg(v_refArgs_3768_, v___x_3775_, v___x_3776_);
v___x_3816_ = l_Subarray_copy___redArg(v___x_3815_);
v___x_3817_ = l_Array_toSubarray___redArg(v_refArgs_3768_, v___x_3776_, v___x_3790_);
v___x_3818_ = l_Subarray_copy___redArg(v___x_3817_);
v___x_3819_ = l_Lean_mkLevelMax(v_val_3798_, v_head_3760_);
v___x_3820_ = lean_box_usize(v_sz_3810_);
v___x_3821_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3822_ = lean_box(v___x_3778_);
v___f_3823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3823_, 0, v___x_3819_);
lean_closure_set(v___f_3823_, 1, v_tail_3761_);
lean_closure_set(v___f_3823_, 2, v_recName_3762_);
lean_closure_set(v___f_3823_, 3, v___x_3799_);
lean_closure_set(v___f_3823_, 4, v___x_3805_);
lean_closure_set(v___f_3823_, 5, v___x_3784_);
lean_closure_set(v___f_3823_, 6, v___x_3820_);
lean_closure_set(v___f_3823_, 7, v___x_3821_);
lean_closure_set(v___f_3823_, 8, v___x_3816_);
lean_closure_set(v___f_3823_, 9, v___x_3802_);
lean_closure_set(v___f_3823_, 10, v___x_3818_);
lean_closure_set(v___f_3823_, 11, v___x_3791_);
lean_closure_set(v___f_3823_, 12, v___x_3789_);
lean_closure_set(v___f_3823_, 13, v___x_3788_);
lean_closure_set(v___f_3823_, 14, v_val_3787_);
lean_closure_set(v___f_3823_, 15, v___x_3822_);
lean_closure_set(v___f_3823_, 16, v_brecOnGoName_3763_);
lean_closure_set(v___f_3823_, 17, v_levelParams_3764_);
lean_closure_set(v___f_3823_, 18, v___x_3758_);
lean_closure_set(v___f_3823_, 19, v_brecOnName_3765_);
lean_closure_set(v___f_3823_, 20, v___x_3781_);
lean_closure_set(v___f_3823_, 21, v_brecOnEqName_3766_);
v___x_3824_ = 0;
v___x_3825_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_fst_3814_, v___f_3823_, v___x_3824_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3825_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v___x_3805_);
lean_dec_ref(v___x_3802_);
lean_dec_ref(v___x_3799_);
lean_dec(v_val_3798_);
lean_dec(v___x_3791_);
lean_dec(v___x_3790_);
lean_dec(v_val_3787_);
lean_dec_ref(v___x_3784_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec_ref(v_refArgs_3768_);
lean_dec(v_brecOnEqName_3766_);
lean_dec(v_brecOnName_3765_);
lean_dec(v_levelParams_3764_);
lean_dec(v_brecOnGoName_3763_);
lean_dec(v_recName_3762_);
lean_dec(v_tail_3761_);
lean_dec(v_head_3760_);
lean_dec(v___x_3758_);
v_a_3826_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3812_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3812_);
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
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
lean_dec(v_a_3797_);
lean_dec(v___x_3790_);
lean_dec(v_val_3787_);
lean_dec_ref(v___x_3784_);
lean_dec_ref(v___x_3782_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec_ref(v_refArgs_3768_);
lean_dec(v_brecOnEqName_3766_);
lean_dec(v_brecOnName_3765_);
lean_dec(v_levelParams_3764_);
lean_dec(v_brecOnGoName_3763_);
lean_dec(v_recName_3762_);
lean_dec(v_tail_3761_);
lean_dec(v_head_3760_);
lean_dec_ref(v_all_3759_);
lean_dec(v___x_3758_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3835_ = l_Lean_MessageData_ofExpr(v___x_3791_);
v___x_3836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3834_);
lean_ctor_set(v___x_3836_, 1, v___x_3835_);
v___x_3837_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3836_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3838_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3839_;
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec(v___x_3791_);
lean_dec(v___x_3790_);
lean_dec(v_val_3787_);
lean_dec_ref(v___x_3784_);
lean_dec_ref(v___x_3782_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec_ref(v_refArgs_3768_);
lean_dec(v_brecOnEqName_3766_);
lean_dec(v_brecOnName_3765_);
lean_dec(v_levelParams_3764_);
lean_dec(v_brecOnGoName_3763_);
lean_dec(v_recName_3762_);
lean_dec(v_tail_3761_);
lean_dec(v_head_3760_);
lean_dec_ref(v_all_3759_);
lean_dec(v___x_3758_);
v_a_3840_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3796_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3796_);
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
lean_dec(v___x_3791_);
lean_dec(v___x_3790_);
lean_dec(v_val_3787_);
lean_dec_ref(v___x_3784_);
lean_dec_ref(v___x_3782_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec_ref(v_refArgs_3768_);
lean_dec(v_brecOnEqName_3766_);
lean_dec(v_brecOnName_3765_);
lean_dec(v_levelParams_3764_);
lean_dec(v_brecOnGoName_3763_);
lean_dec(v_recName_3762_);
lean_dec(v_tail_3761_);
lean_dec(v_head_3760_);
lean_dec_ref(v_all_3759_);
lean_dec(v___x_3758_);
v_a_3848_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3794_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3794_);
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
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec(v___x_3791_);
lean_dec(v___x_3790_);
lean_dec(v_val_3787_);
lean_dec_ref(v___x_3784_);
lean_dec_ref(v___x_3782_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec_ref(v_refArgs_3768_);
lean_dec(v_brecOnEqName_3766_);
lean_dec(v_brecOnName_3765_);
lean_dec(v_levelParams_3764_);
lean_dec(v_brecOnGoName_3763_);
lean_dec(v_recName_3762_);
lean_dec(v_tail_3761_);
lean_dec(v_head_3760_);
lean_dec_ref(v_all_3759_);
lean_dec(v___x_3758_);
v_a_3856_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3792_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3792_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec(v___x_3786_);
lean_dec_ref(v___x_3782_);
lean_dec(v___x_3776_);
lean_dec(v___x_3775_);
lean_dec_ref(v_refArgs_3768_);
lean_dec(v_brecOnEqName_3766_);
lean_dec(v_brecOnName_3765_);
lean_dec(v_levelParams_3764_);
lean_dec(v_brecOnGoName_3763_);
lean_dec(v_recName_3762_);
lean_dec(v_tail_3761_);
lean_dec(v_head_3760_);
lean_dec_ref(v_all_3759_);
lean_dec(v___x_3758_);
v___x_3864_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3865_ = l_Lean_MessageData_ofExpr(v_type_3767_);
v___x_3866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___x_3864_);
lean_ctor_set(v___x_3866_, 1, v___x_3865_);
v___x_3867_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3866_);
lean_ctor_set(v___x_3868_, 1, v___x_3867_);
v___x_3869_ = lean_array_to_list(v___x_3784_);
v___x_3870_ = lean_box(0);
v___x_3871_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3869_, v___x_3870_);
v___x_3872_ = l_Lean_MessageData_ofList(v___x_3871_);
v___x_3873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3868_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3873_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3874_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3875_ = _args[0];
lean_object* v_numMotives_3876_ = _args[1];
lean_object* v_numMinors_3877_ = _args[2];
lean_object* v___x_3878_ = _args[3];
lean_object* v_all_3879_ = _args[4];
lean_object* v_head_3880_ = _args[5];
lean_object* v_tail_3881_ = _args[6];
lean_object* v_recName_3882_ = _args[7];
lean_object* v_brecOnGoName_3883_ = _args[8];
lean_object* v_levelParams_3884_ = _args[9];
lean_object* v_brecOnName_3885_ = _args[10];
lean_object* v_brecOnEqName_3886_ = _args[11];
lean_object* v_type_3887_ = _args[12];
lean_object* v_refArgs_3888_ = _args[13];
lean_object* v_refBody_3889_ = _args[14];
lean_object* v___y_3890_ = _args[15];
lean_object* v___y_3891_ = _args[16];
lean_object* v___y_3892_ = _args[17];
lean_object* v___y_3893_ = _args[18];
lean_object* v___y_3894_ = _args[19];
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3875_, v_numMotives_3876_, v_numMinors_3877_, v___x_3878_, v_all_3879_, v_head_3880_, v_tail_3881_, v_recName_3882_, v_brecOnGoName_3883_, v_levelParams_3884_, v_brecOnName_3885_, v_brecOnEqName_3886_, v_type_3887_, v_refArgs_3888_, v_refBody_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v_refBody_3889_);
lean_dec(v_numMinors_3877_);
lean_dec(v_numMotives_3876_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3898_, lean_object* v_nParams_3899_, lean_object* v_all_3900_, lean_object* v_brecOnName_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v___x_3907_; 
lean_inc(v_recName_3898_);
v___x_3907_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3898_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3939_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3910_ = v___x_3907_;
v_isShared_3911_ = v_isSharedCheck_3939_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3939_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
if (lean_obj_tag(v_a_3908_) == 7)
{
lean_object* v_val_3912_; lean_object* v_toConstantVal_3913_; lean_object* v_numMotives_3914_; lean_object* v_numMinors_3915_; lean_object* v_levelParams_3916_; lean_object* v_type_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_del_object(v___x_3910_);
v_val_3912_ = lean_ctor_get(v_a_3908_, 0);
lean_inc_ref(v_val_3912_);
lean_dec_ref(v_a_3908_);
v_toConstantVal_3913_ = lean_ctor_get(v_val_3912_, 0);
lean_inc_ref(v_toConstantVal_3913_);
v_numMotives_3914_ = lean_ctor_get(v_val_3912_, 4);
lean_inc(v_numMotives_3914_);
v_numMinors_3915_ = lean_ctor_get(v_val_3912_, 5);
lean_inc(v_numMinors_3915_);
lean_dec_ref(v_val_3912_);
v_levelParams_3916_ = lean_ctor_get(v_toConstantVal_3913_, 1);
lean_inc_n(v_levelParams_3916_, 2);
v_type_3917_ = lean_ctor_get(v_toConstantVal_3913_, 2);
lean_inc_ref(v_type_3917_);
lean_dec_ref(v_toConstantVal_3913_);
v___x_3918_ = lean_box(0);
v___x_3919_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3916_, v___x_3918_);
if (lean_obj_tag(v___x_3919_) == 1)
{
lean_object* v_head_3920_; lean_object* v_tail_3921_; lean_object* v___x_3922_; lean_object* v_brecOnGoName_3923_; lean_object* v___x_3924_; lean_object* v_brecOnEqName_3925_; lean_object* v___f_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; 
v_head_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_head_3920_);
v_tail_3921_ = lean_ctor_get(v___x_3919_, 1);
lean_inc(v_tail_3921_);
v___x_3922_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc_n(v_brecOnName_3901_, 2);
v_brecOnGoName_3923_ = l_Lean_Name_str___override(v_brecOnName_3901_, v___x_3922_);
v___x_3924_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
v_brecOnEqName_3925_ = l_Lean_Name_str___override(v_brecOnName_3901_, v___x_3924_);
lean_inc_ref(v_type_3917_);
v___f_3926_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 20, 13);
lean_closure_set(v___f_3926_, 0, v_nParams_3899_);
lean_closure_set(v___f_3926_, 1, v_numMotives_3914_);
lean_closure_set(v___f_3926_, 2, v_numMinors_3915_);
lean_closure_set(v___f_3926_, 3, v___x_3919_);
lean_closure_set(v___f_3926_, 4, v_all_3900_);
lean_closure_set(v___f_3926_, 5, v_head_3920_);
lean_closure_set(v___f_3926_, 6, v_tail_3921_);
lean_closure_set(v___f_3926_, 7, v_recName_3898_);
lean_closure_set(v___f_3926_, 8, v_brecOnGoName_3923_);
lean_closure_set(v___f_3926_, 9, v_levelParams_3916_);
lean_closure_set(v___f_3926_, 10, v_brecOnName_3901_);
lean_closure_set(v___f_3926_, 11, v_brecOnEqName_3925_);
lean_closure_set(v___f_3926_, 12, v_type_3917_);
v___x_3927_ = 0;
v___x_3928_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3917_, v___f_3926_, v___x_3927_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
return v___x_3928_;
}
else
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_dec(v___x_3919_);
lean_dec_ref(v_type_3917_);
lean_dec(v_levelParams_3916_);
lean_dec(v_numMinors_3915_);
lean_dec(v_numMotives_3914_);
lean_dec(v_brecOnName_3901_);
lean_dec_ref(v_all_3900_);
lean_dec(v_nParams_3899_);
v___x_3929_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3930_ = l_Lean_MessageData_ofName(v_recName_3898_);
v___x_3931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3929_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
v___x_3932_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3931_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3933_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
return v___x_3934_;
}
}
else
{
lean_object* v___x_3935_; lean_object* v___x_3937_; 
lean_dec(v_a_3908_);
lean_dec(v_brecOnName_3901_);
lean_dec_ref(v_all_3900_);
lean_dec(v_nParams_3899_);
lean_dec(v_recName_3898_);
v___x_3935_ = lean_box(0);
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v___x_3935_);
v___x_3937_ = v___x_3910_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v___x_3935_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec(v_brecOnName_3901_);
lean_dec_ref(v_all_3900_);
lean_dec(v_nParams_3899_);
lean_dec(v_recName_3898_);
v_a_3940_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3907_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3907_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3948_, lean_object* v_nParams_3949_, lean_object* v_all_3950_, lean_object* v_brecOnName_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3948_, v_nParams_3949_, v_all_3950_, v_brecOnName_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_3958_, lean_object* v___x_3959_, lean_object* v___x_3960_, lean_object* v___x_3961_, lean_object* v___x_3962_, lean_object* v_a_3963_, lean_object* v_b_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_){
_start:
{
uint8_t v___x_3970_; 
v___x_3970_ = lean_nat_dec_lt(v_a_3963_, v_upperBound_3958_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; 
lean_dec(v_a_3963_);
lean_dec_ref(v___x_3962_);
lean_dec(v___x_3961_);
lean_dec(v___x_3960_);
lean_dec(v___x_3959_);
v___x_3971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3971_, 0, v_b_3964_);
return v___x_3971_;
}
else
{
lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3972_ = lean_unsigned_to_nat(1u);
v___x_3973_ = lean_nat_add(v_a_3963_, v___x_3972_);
lean_dec(v_a_3963_);
lean_inc_n(v___x_3973_, 2);
lean_inc(v___x_3959_);
v___x_3974_ = lean_name_append_index_after(v___x_3959_, v___x_3973_);
lean_inc(v___x_3960_);
v___x_3975_ = lean_name_append_index_after(v___x_3960_, v___x_3973_);
lean_inc_ref(v___x_3962_);
lean_inc(v___x_3961_);
v___x_3976_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_3974_, v___x_3961_, v___x_3962_, v___x_3975_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v___x_3977_; 
lean_dec_ref(v___x_3976_);
v___x_3977_ = lean_box(0);
v_a_3963_ = v___x_3973_;
v_b_3964_ = v___x_3977_;
goto _start;
}
else
{
lean_dec(v___x_3973_);
lean_dec_ref(v___x_3962_);
lean_dec(v___x_3961_);
lean_dec(v___x_3960_);
lean_dec(v___x_3959_);
return v___x_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_3979_, lean_object* v___x_3980_, lean_object* v___x_3981_, lean_object* v___x_3982_, lean_object* v___x_3983_, lean_object* v_a_3984_, lean_object* v_b_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_3979_, v___x_3980_, v___x_3981_, v___x_3982_, v___x_3983_, v_a_3984_, v_b_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v_upperBound_3979_);
return v_res_3991_;
}
}
static lean_object* _init_l_Lean_mkBRecOn___closed__2(void){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_3997_ = ((lean_object*)(l_Lean_mkBelow___closed__5));
v___x_3998_ = l_Lean_Name_append(v___x_3997_, v___x_3996_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_){
_start:
{
lean_object* v_options_4005_; uint8_t v_hasTrace_4006_; 
v_options_4005_ = lean_ctor_get(v_a_4002_, 2);
v_hasTrace_4006_ = lean_ctor_get_uint8(v_options_4005_, sizeof(void*)*1);
if (v_hasTrace_4006_ == 0)
{
lean_object* v___x_4007_; 
lean_inc(v_indName_3999_);
v___x_4007_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4073_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4010_ = v___x_4007_;
v_isShared_4011_ = v_isSharedCheck_4073_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4007_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4073_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
if (lean_obj_tag(v_a_4008_) == 5)
{
lean_object* v_val_4012_; uint8_t v_isRec_4013_; 
v_val_4012_ = lean_ctor_get(v_a_4008_, 0);
lean_inc_ref(v_val_4012_);
lean_dec_ref(v_a_4008_);
v_isRec_4013_ = lean_ctor_get_uint8(v_val_4012_, sizeof(void*)*6);
if (v_isRec_4013_ == 0)
{
lean_object* v___x_4014_; lean_object* v___x_4016_; 
lean_dec_ref(v_val_4012_);
lean_dec(v_indName_3999_);
v___x_4014_ = lean_box(0);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v___x_4014_);
v___x_4016_ = v___x_4010_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v___x_4014_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
else
{
lean_object* v_toConstantVal_4018_; lean_object* v_numParams_4019_; lean_object* v_all_4020_; lean_object* v_numNested_4021_; lean_object* v_type_4022_; lean_object* v___x_4023_; 
lean_del_object(v___x_4010_);
v_toConstantVal_4018_ = lean_ctor_get(v_val_4012_, 0);
lean_inc_ref(v_toConstantVal_4018_);
v_numParams_4019_ = lean_ctor_get(v_val_4012_, 1);
lean_inc(v_numParams_4019_);
v_all_4020_ = lean_ctor_get(v_val_4012_, 3);
lean_inc(v_all_4020_);
v_numNested_4021_ = lean_ctor_get(v_val_4012_, 5);
lean_inc(v_numNested_4021_);
lean_dec_ref(v_val_4012_);
v_type_4022_ = lean_ctor_get(v_toConstantVal_4018_, 2);
lean_inc_ref(v_type_4022_);
lean_dec_ref(v_toConstantVal_4018_);
v___x_4023_ = l_Lean_Meta_isPropFormerType(v_type_4022_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4060_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4026_ = v___x_4023_;
v_isShared_4027_ = v_isSharedCheck_4060_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4023_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4060_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
uint8_t v___x_4028_; 
v___x_4028_ = lean_unbox(v_a_4024_);
lean_dec(v_a_4024_);
if (v___x_4028_ == 0)
{
lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
lean_del_object(v___x_4026_);
lean_inc_n(v_indName_3999_, 2);
v___x_4029_ = l_Lean_mkRecName(v_indName_3999_);
v___x_4030_ = l_Lean_mkBRecOnName(v_indName_3999_);
lean_inc(v_all_4020_);
v___x_4031_ = lean_array_mk(v_all_4020_);
lean_inc(v___x_4030_);
lean_inc_ref(v___x_4031_);
lean_inc(v_numParams_4019_);
lean_inc(v___x_4029_);
v___x_4032_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4029_, v_numParams_4019_, v___x_4031_, v___x_4030_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4054_; 
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4054_ == 0)
{
lean_object* v_unused_4055_; 
v_unused_4055_ = lean_ctor_get(v___x_4032_, 0);
lean_dec(v_unused_4055_);
v___x_4034_ = v___x_4032_;
v_isShared_4035_ = v_isSharedCheck_4054_;
goto v_resetjp_4033_;
}
else
{
lean_dec(v___x_4032_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4054_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; uint8_t v___x_4039_; 
v___x_4036_ = lean_box(0);
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = l_List_get_x21Internal___redArg(v___x_4036_, v_all_4020_, v___x_4037_);
lean_dec(v_all_4020_);
v___x_4039_ = lean_name_eq(v___x_4038_, v_indName_3999_);
lean_dec(v_indName_3999_);
lean_dec(v___x_4038_);
if (v___x_4039_ == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4042_; 
lean_dec_ref(v___x_4031_);
lean_dec(v___x_4030_);
lean_dec(v___x_4029_);
lean_dec(v_numNested_4021_);
lean_dec(v_numParams_4019_);
v___x_4040_ = lean_box(0);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v___x_4040_);
v___x_4042_ = v___x_4034_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
else
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
lean_del_object(v___x_4034_);
v___x_4044_ = lean_box(0);
v___x_4045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4021_, v___x_4029_, v___x_4030_, v_numParams_4019_, v___x_4031_, v___x_4037_, v___x_4044_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_numNested_4021_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4052_ == 0)
{
lean_object* v_unused_4053_; 
v_unused_4053_ = lean_ctor_get(v___x_4045_, 0);
lean_dec(v_unused_4053_);
v___x_4047_ = v___x_4045_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_dec(v___x_4045_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 0, v___x_4044_);
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4044_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
else
{
return v___x_4045_;
}
}
}
}
else
{
lean_dec_ref(v___x_4031_);
lean_dec(v___x_4030_);
lean_dec(v___x_4029_);
lean_dec(v_numNested_4021_);
lean_dec(v_all_4020_);
lean_dec(v_numParams_4019_);
lean_dec(v_indName_3999_);
return v___x_4032_;
}
}
else
{
lean_object* v___x_4056_; lean_object* v___x_4058_; 
lean_dec(v_numNested_4021_);
lean_dec(v_all_4020_);
lean_dec(v_numParams_4019_);
lean_dec(v_indName_3999_);
v___x_4056_ = lean_box(0);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 0, v___x_4056_);
v___x_4058_ = v___x_4026_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_dec(v_numNested_4021_);
lean_dec(v_all_4020_);
lean_dec(v_numParams_4019_);
lean_dec(v_indName_3999_);
v_a_4061_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4023_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4023_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
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
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4071_; 
lean_dec(v_a_4008_);
lean_dec(v_indName_3999_);
v___x_4069_ = lean_box(0);
if (v_isShared_4011_ == 0)
{
lean_ctor_set(v___x_4010_, 0, v___x_4069_);
v___x_4071_ = v___x_4010_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v___x_4069_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v_indName_3999_);
v_a_4074_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4007_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4007_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
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
lean_object* v_inheritedTraceOptions_4082_; lean_object* v___f_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v_a_4091_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v_a_4106_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v_a_4111_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v_a_4116_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v_a_4128_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v_a_4133_; 
v_inheritedTraceOptions_4082_ = lean_ctor_get(v_a_4002_, 13);
lean_inc(v_indName_3999_);
v___f_4083_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4083_, 0, v_indName_3999_);
v___x_4084_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4085_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4086_ = lean_obj_once(&l_Lean_mkBRecOn___closed__2, &l_Lean_mkBRecOn___closed__2_once, _init_l_Lean_mkBRecOn___closed__2);
v___x_4087_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4082_, v_options_4005_, v___x_4086_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4204_; uint8_t v___x_4205_; 
v___x_4204_ = l_Lean_trace_profiler;
v___x_4205_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4005_, v___x_4204_);
if (v___x_4205_ == 0)
{
lean_object* v___x_4206_; 
lean_dec_ref(v___f_4083_);
lean_inc(v_indName_3999_);
v___x_4206_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4272_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4272_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4272_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
if (lean_obj_tag(v_a_4207_) == 5)
{
lean_object* v_val_4211_; uint8_t v_isRec_4212_; 
v_val_4211_ = lean_ctor_get(v_a_4207_, 0);
lean_inc_ref(v_val_4211_);
lean_dec_ref(v_a_4207_);
v_isRec_4212_ = lean_ctor_get_uint8(v_val_4211_, sizeof(void*)*6);
if (v_isRec_4212_ == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
lean_dec_ref(v_val_4211_);
lean_dec(v_indName_3999_);
v___x_4213_ = lean_box(0);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4213_);
v___x_4215_ = v___x_4209_;
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
lean_object* v_toConstantVal_4217_; lean_object* v_numParams_4218_; lean_object* v_all_4219_; lean_object* v_numNested_4220_; lean_object* v_type_4221_; lean_object* v___x_4222_; 
lean_del_object(v___x_4209_);
v_toConstantVal_4217_ = lean_ctor_get(v_val_4211_, 0);
lean_inc_ref(v_toConstantVal_4217_);
v_numParams_4218_ = lean_ctor_get(v_val_4211_, 1);
lean_inc(v_numParams_4218_);
v_all_4219_ = lean_ctor_get(v_val_4211_, 3);
lean_inc(v_all_4219_);
v_numNested_4220_ = lean_ctor_get(v_val_4211_, 5);
lean_inc(v_numNested_4220_);
lean_dec_ref(v_val_4211_);
v_type_4221_ = lean_ctor_get(v_toConstantVal_4217_, 2);
lean_inc_ref(v_type_4221_);
lean_dec_ref(v_toConstantVal_4217_);
v___x_4222_ = l_Lean_Meta_isPropFormerType(v_type_4221_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4259_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4259_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4259_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
uint8_t v___x_4227_; 
v___x_4227_ = lean_unbox(v_a_4223_);
lean_dec(v_a_4223_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_del_object(v___x_4225_);
lean_inc_n(v_indName_3999_, 2);
v___x_4228_ = l_Lean_mkRecName(v_indName_3999_);
v___x_4229_ = l_Lean_mkBRecOnName(v_indName_3999_);
lean_inc(v_all_4219_);
v___x_4230_ = lean_array_mk(v_all_4219_);
lean_inc(v___x_4229_);
lean_inc_ref(v___x_4230_);
lean_inc(v_numParams_4218_);
lean_inc(v___x_4228_);
v___x_4231_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4228_, v_numParams_4218_, v___x_4230_, v___x_4229_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4253_; 
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4253_ == 0)
{
lean_object* v_unused_4254_; 
v_unused_4254_ = lean_ctor_get(v___x_4231_, 0);
lean_dec(v_unused_4254_);
v___x_4233_ = v___x_4231_;
v_isShared_4234_ = v_isSharedCheck_4253_;
goto v_resetjp_4232_;
}
else
{
lean_dec(v___x_4231_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4253_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; 
v___x_4235_ = lean_box(0);
v___x_4236_ = lean_unsigned_to_nat(0u);
v___x_4237_ = l_List_get_x21Internal___redArg(v___x_4235_, v_all_4219_, v___x_4236_);
lean_dec(v_all_4219_);
v___x_4238_ = lean_name_eq(v___x_4237_, v_indName_3999_);
lean_dec(v_indName_3999_);
lean_dec(v___x_4237_);
if (v___x_4238_ == 0)
{
lean_object* v___x_4239_; lean_object* v___x_4241_; 
lean_dec_ref(v___x_4230_);
lean_dec(v___x_4229_);
lean_dec(v___x_4228_);
lean_dec(v_numNested_4220_);
lean_dec(v_numParams_4218_);
v___x_4239_ = lean_box(0);
if (v_isShared_4234_ == 0)
{
lean_ctor_set(v___x_4233_, 0, v___x_4239_);
v___x_4241_ = v___x_4233_;
goto v_reusejp_4240_;
}
else
{
lean_object* v_reuseFailAlloc_4242_; 
v_reuseFailAlloc_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4242_, 0, v___x_4239_);
v___x_4241_ = v_reuseFailAlloc_4242_;
goto v_reusejp_4240_;
}
v_reusejp_4240_:
{
return v___x_4241_;
}
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
lean_del_object(v___x_4233_);
v___x_4243_ = lean_box(0);
v___x_4244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4220_, v___x_4228_, v___x_4229_, v_numParams_4218_, v___x_4230_, v___x_4236_, v___x_4243_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_numNested_4220_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4251_ == 0)
{
lean_object* v_unused_4252_; 
v_unused_4252_ = lean_ctor_get(v___x_4244_, 0);
lean_dec(v_unused_4252_);
v___x_4246_ = v___x_4244_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_dec(v___x_4244_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
lean_ctor_set(v___x_4246_, 0, v___x_4243_);
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4243_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
else
{
return v___x_4244_;
}
}
}
}
else
{
lean_dec_ref(v___x_4230_);
lean_dec(v___x_4229_);
lean_dec(v___x_4228_);
lean_dec(v_numNested_4220_);
lean_dec(v_all_4219_);
lean_dec(v_numParams_4218_);
lean_dec(v_indName_3999_);
return v___x_4231_;
}
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
lean_dec(v_numNested_4220_);
lean_dec(v_all_4219_);
lean_dec(v_numParams_4218_);
lean_dec(v_indName_3999_);
v___x_4255_ = lean_box(0);
if (v_isShared_4226_ == 0)
{
lean_ctor_set(v___x_4225_, 0, v___x_4255_);
v___x_4257_ = v___x_4225_;
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
lean_dec(v_numNested_4220_);
lean_dec(v_all_4219_);
lean_dec(v_numParams_4218_);
lean_dec(v_indName_3999_);
v_a_4260_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4222_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4222_);
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
}
else
{
lean_object* v___x_4268_; lean_object* v___x_4270_; 
lean_dec(v_a_4207_);
lean_dec(v_indName_3999_);
v___x_4268_ = lean_box(0);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4268_);
v___x_4270_ = v___x_4209_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
return v___x_4270_;
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec(v_indName_3999_);
v_a_4273_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4206_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4206_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
else
{
goto v___jp_4135_;
}
}
else
{
goto v___jp_4135_;
}
v___jp_4088_:
{
lean_object* v___x_4092_; double v___x_4093_; double v___x_4094_; double v___x_4095_; double v___x_4096_; double v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4092_ = lean_io_mono_nanos_now();
v___x_4093_ = lean_float_of_nat(v___y_4090_);
v___x_4094_ = lean_float_once(&l_Lean_mkBelow___closed__7, &l_Lean_mkBelow___closed__7_once, _init_l_Lean_mkBelow___closed__7);
v___x_4095_ = lean_float_div(v___x_4093_, v___x_4094_);
v___x_4096_ = lean_float_of_nat(v___x_4092_);
v___x_4097_ = lean_float_div(v___x_4096_, v___x_4094_);
v___x_4098_ = lean_box_float(v___x_4095_);
v___x_4099_ = lean_box_float(v___x_4097_);
v___x_4100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4101_, 0, v_a_4091_);
lean_ctor_set(v___x_4101_, 1, v___x_4100_);
v___x_4102_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4084_, v_hasTrace_4006_, v___x_4085_, v_options_4005_, v___x_4087_, v___y_4089_, v___f_4083_, v___x_4101_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
return v___x_4102_;
}
v___jp_4103_:
{
lean_object* v___x_4107_; 
v___x_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4107_, 0, v_a_4106_);
v___y_4089_ = v___y_4104_;
v___y_4090_ = v___y_4105_;
v_a_4091_ = v___x_4107_;
goto v___jp_4088_;
}
v___jp_4108_:
{
lean_object* v___x_4112_; 
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v_a_4111_);
v___y_4089_ = v___y_4109_;
v___y_4090_ = v___y_4110_;
v_a_4091_ = v___x_4112_;
goto v___jp_4088_;
}
v___jp_4113_:
{
lean_object* v___x_4117_; double v___x_4118_; double v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4117_ = lean_io_get_num_heartbeats();
v___x_4118_ = lean_float_of_nat(v___y_4115_);
v___x_4119_ = lean_float_of_nat(v___x_4117_);
v___x_4120_ = lean_box_float(v___x_4118_);
v___x_4121_ = lean_box_float(v___x_4119_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4120_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v_a_4116_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__3(v___x_4084_, v_hasTrace_4006_, v___x_4085_, v_options_4005_, v___x_4087_, v___y_4114_, v___f_4083_, v___x_4123_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
return v___x_4124_;
}
v___jp_4125_:
{
lean_object* v___x_4129_; 
v___x_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4129_, 0, v_a_4128_);
v___y_4114_ = v___y_4126_;
v___y_4115_ = v___y_4127_;
v_a_4116_ = v___x_4129_;
goto v___jp_4113_;
}
v___jp_4130_:
{
lean_object* v___x_4134_; 
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_a_4133_);
v___y_4114_ = v___y_4131_;
v___y_4115_ = v___y_4132_;
v_a_4116_ = v___x_4134_;
goto v___jp_4113_;
}
v___jp_4135_:
{
lean_object* v___x_4136_; lean_object* v_a_4137_; lean_object* v___x_4138_; uint8_t v___x_4139_; 
v___x_4136_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__1___redArg(v_a_4003_);
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref(v___x_4136_);
v___x_4138_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4139_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__2(v_options_4005_, v___x_4138_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = lean_io_mono_nanos_now();
lean_inc(v_indName_3999_);
v___x_4141_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v___x_4141_);
if (lean_obj_tag(v_a_4142_) == 5)
{
lean_object* v_val_4143_; uint8_t v_isRec_4144_; 
v_val_4143_ = lean_ctor_get(v_a_4142_, 0);
lean_inc_ref(v_val_4143_);
lean_dec_ref(v_a_4142_);
v_isRec_4144_ = lean_ctor_get_uint8(v_val_4143_, sizeof(void*)*6);
if (v_isRec_4144_ == 0)
{
lean_object* v___x_4145_; 
lean_dec_ref(v_val_4143_);
lean_dec(v_indName_3999_);
v___x_4145_ = lean_box(0);
v___y_4104_ = v_a_4137_;
v___y_4105_ = v___x_4140_;
v_a_4106_ = v___x_4145_;
goto v___jp_4103_;
}
else
{
lean_object* v_toConstantVal_4146_; lean_object* v_numParams_4147_; lean_object* v_all_4148_; lean_object* v_numNested_4149_; lean_object* v_type_4150_; lean_object* v___x_4151_; 
v_toConstantVal_4146_ = lean_ctor_get(v_val_4143_, 0);
lean_inc_ref(v_toConstantVal_4146_);
v_numParams_4147_ = lean_ctor_get(v_val_4143_, 1);
lean_inc(v_numParams_4147_);
v_all_4148_ = lean_ctor_get(v_val_4143_, 3);
lean_inc(v_all_4148_);
v_numNested_4149_ = lean_ctor_get(v_val_4143_, 5);
lean_inc(v_numNested_4149_);
lean_dec_ref(v_val_4143_);
v_type_4150_ = lean_ctor_get(v_toConstantVal_4146_, 2);
lean_inc_ref(v_type_4150_);
lean_dec_ref(v_toConstantVal_4146_);
v___x_4151_ = l_Lean_Meta_isPropFormerType(v_type_4150_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; uint8_t v___x_4153_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref(v___x_4151_);
v___x_4153_ = lean_unbox(v_a_4152_);
lean_dec(v_a_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_inc_n(v_indName_3999_, 2);
v___x_4154_ = l_Lean_mkRecName(v_indName_3999_);
v___x_4155_ = l_Lean_mkBRecOnName(v_indName_3999_);
lean_inc(v_all_4148_);
v___x_4156_ = lean_array_mk(v_all_4148_);
lean_inc(v___x_4155_);
lean_inc_ref(v___x_4156_);
lean_inc(v_numParams_4147_);
lean_inc(v___x_4154_);
v___x_4157_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4154_, v_numParams_4147_, v___x_4156_, v___x_4155_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
lean_dec_ref(v___x_4157_);
v___x_4158_ = lean_box(0);
v___x_4159_ = lean_unsigned_to_nat(0u);
v___x_4160_ = l_List_get_x21Internal___redArg(v___x_4158_, v_all_4148_, v___x_4159_);
lean_dec(v_all_4148_);
v___x_4161_ = lean_name_eq(v___x_4160_, v_indName_3999_);
lean_dec(v_indName_3999_);
lean_dec(v___x_4160_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; 
lean_dec_ref(v___x_4156_);
lean_dec(v___x_4155_);
lean_dec(v___x_4154_);
lean_dec(v_numNested_4149_);
lean_dec(v_numParams_4147_);
v___x_4162_ = lean_box(0);
v___y_4104_ = v_a_4137_;
v___y_4105_ = v___x_4140_;
v_a_4106_ = v___x_4162_;
goto v___jp_4103_;
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4163_ = lean_box(0);
v___x_4164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4149_, v___x_4154_, v___x_4155_, v_numParams_4147_, v___x_4156_, v___x_4159_, v___x_4163_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_numNested_4149_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_dec_ref(v___x_4164_);
v___y_4104_ = v_a_4137_;
v___y_4105_ = v___x_4140_;
v_a_4106_ = v___x_4163_;
goto v___jp_4103_;
}
else
{
lean_object* v_a_4165_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref(v___x_4164_);
v___y_4109_ = v_a_4137_;
v___y_4110_ = v___x_4140_;
v_a_4111_ = v_a_4165_;
goto v___jp_4108_;
}
}
}
else
{
lean_dec_ref(v___x_4156_);
lean_dec(v___x_4155_);
lean_dec(v___x_4154_);
lean_dec(v_numNested_4149_);
lean_dec(v_all_4148_);
lean_dec(v_numParams_4147_);
lean_dec(v_indName_3999_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4166_; 
v_a_4166_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4166_);
lean_dec_ref(v___x_4157_);
v___y_4104_ = v_a_4137_;
v___y_4105_ = v___x_4140_;
v_a_4106_ = v_a_4166_;
goto v___jp_4103_;
}
else
{
lean_object* v_a_4167_; 
v_a_4167_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4167_);
lean_dec_ref(v___x_4157_);
v___y_4109_ = v_a_4137_;
v___y_4110_ = v___x_4140_;
v_a_4111_ = v_a_4167_;
goto v___jp_4108_;
}
}
}
else
{
lean_object* v___x_4168_; 
lean_dec(v_numNested_4149_);
lean_dec(v_all_4148_);
lean_dec(v_numParams_4147_);
lean_dec(v_indName_3999_);
v___x_4168_ = lean_box(0);
v___y_4104_ = v_a_4137_;
v___y_4105_ = v___x_4140_;
v_a_4106_ = v___x_4168_;
goto v___jp_4103_;
}
}
else
{
lean_object* v_a_4169_; 
lean_dec(v_numNested_4149_);
lean_dec(v_all_4148_);
lean_dec(v_numParams_4147_);
lean_dec(v_indName_3999_);
v_a_4169_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4169_);
lean_dec_ref(v___x_4151_);
v___y_4109_ = v_a_4137_;
v___y_4110_ = v___x_4140_;
v_a_4111_ = v_a_4169_;
goto v___jp_4108_;
}
}
}
else
{
lean_object* v___x_4170_; 
lean_dec(v_a_4142_);
lean_dec(v_indName_3999_);
v___x_4170_ = lean_box(0);
v___y_4104_ = v_a_4137_;
v___y_4105_ = v___x_4140_;
v_a_4106_ = v___x_4170_;
goto v___jp_4103_;
}
}
else
{
lean_object* v_a_4171_; 
lean_dec(v_indName_3999_);
v_a_4171_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4171_);
lean_dec_ref(v___x_4141_);
v___y_4109_ = v_a_4137_;
v___y_4110_ = v___x_4140_;
v_a_4111_ = v_a_4171_;
goto v___jp_4108_;
}
}
else
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
v___x_4172_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_3999_);
v___x_4173_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v___x_4173_);
if (lean_obj_tag(v_a_4174_) == 5)
{
lean_object* v_val_4175_; uint8_t v_isRec_4176_; 
v_val_4175_ = lean_ctor_get(v_a_4174_, 0);
lean_inc_ref(v_val_4175_);
lean_dec_ref(v_a_4174_);
v_isRec_4176_ = lean_ctor_get_uint8(v_val_4175_, sizeof(void*)*6);
if (v_isRec_4176_ == 0)
{
lean_object* v___x_4177_; 
lean_dec_ref(v_val_4175_);
lean_dec(v_indName_3999_);
v___x_4177_ = lean_box(0);
v___y_4126_ = v_a_4137_;
v___y_4127_ = v___x_4172_;
v_a_4128_ = v___x_4177_;
goto v___jp_4125_;
}
else
{
lean_object* v_toConstantVal_4178_; lean_object* v_numParams_4179_; lean_object* v_all_4180_; lean_object* v_numNested_4181_; lean_object* v_type_4182_; lean_object* v___x_4183_; 
v_toConstantVal_4178_ = lean_ctor_get(v_val_4175_, 0);
lean_inc_ref(v_toConstantVal_4178_);
v_numParams_4179_ = lean_ctor_get(v_val_4175_, 1);
lean_inc(v_numParams_4179_);
v_all_4180_ = lean_ctor_get(v_val_4175_, 3);
lean_inc(v_all_4180_);
v_numNested_4181_ = lean_ctor_get(v_val_4175_, 5);
lean_inc(v_numNested_4181_);
lean_dec_ref(v_val_4175_);
v_type_4182_ = lean_ctor_get(v_toConstantVal_4178_, 2);
lean_inc_ref(v_type_4182_);
lean_dec_ref(v_toConstantVal_4178_);
v___x_4183_ = l_Lean_Meta_isPropFormerType(v_type_4182_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_object* v_a_4184_; uint8_t v___x_4185_; 
v_a_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4184_);
lean_dec_ref(v___x_4183_);
v___x_4185_ = lean_unbox(v_a_4184_);
lean_dec(v_a_4184_);
if (v___x_4185_ == 0)
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
lean_inc_n(v_indName_3999_, 2);
v___x_4186_ = l_Lean_mkRecName(v_indName_3999_);
v___x_4187_ = l_Lean_mkBRecOnName(v_indName_3999_);
lean_inc(v_all_4180_);
v___x_4188_ = lean_array_mk(v_all_4180_);
lean_inc(v___x_4187_);
lean_inc_ref(v___x_4188_);
lean_inc(v_numParams_4179_);
lean_inc(v___x_4186_);
v___x_4189_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4186_, v_numParams_4179_, v___x_4188_, v___x_4187_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
lean_dec_ref(v___x_4189_);
v___x_4190_ = lean_box(0);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = l_List_get_x21Internal___redArg(v___x_4190_, v_all_4180_, v___x_4191_);
lean_dec(v_all_4180_);
v___x_4193_ = lean_name_eq(v___x_4192_, v_indName_3999_);
lean_dec(v_indName_3999_);
lean_dec(v___x_4192_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; 
lean_dec_ref(v___x_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v_numNested_4181_);
lean_dec(v_numParams_4179_);
v___x_4194_ = lean_box(0);
v___y_4126_ = v_a_4137_;
v___y_4127_ = v___x_4172_;
v_a_4128_ = v___x_4194_;
goto v___jp_4125_;
}
else
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_box(0);
v___x_4196_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4181_, v___x_4186_, v___x_4187_, v_numParams_4179_, v___x_4188_, v___x_4191_, v___x_4195_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_);
lean_dec(v_numNested_4181_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_dec_ref(v___x_4196_);
v___y_4126_ = v_a_4137_;
v___y_4127_ = v___x_4172_;
v_a_4128_ = v___x_4195_;
goto v___jp_4125_;
}
else
{
lean_object* v_a_4197_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref(v___x_4196_);
v___y_4131_ = v_a_4137_;
v___y_4132_ = v___x_4172_;
v_a_4133_ = v_a_4197_;
goto v___jp_4130_;
}
}
}
else
{
lean_dec_ref(v___x_4188_);
lean_dec(v___x_4187_);
lean_dec(v___x_4186_);
lean_dec(v_numNested_4181_);
lean_dec(v_all_4180_);
lean_dec(v_numParams_4179_);
lean_dec(v_indName_3999_);
if (lean_obj_tag(v___x_4189_) == 0)
{
lean_object* v_a_4198_; 
v_a_4198_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4198_);
lean_dec_ref(v___x_4189_);
v___y_4126_ = v_a_4137_;
v___y_4127_ = v___x_4172_;
v_a_4128_ = v_a_4198_;
goto v___jp_4125_;
}
else
{
lean_object* v_a_4199_; 
v_a_4199_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4189_);
v___y_4131_ = v_a_4137_;
v___y_4132_ = v___x_4172_;
v_a_4133_ = v_a_4199_;
goto v___jp_4130_;
}
}
}
else
{
lean_object* v___x_4200_; 
lean_dec(v_numNested_4181_);
lean_dec(v_all_4180_);
lean_dec(v_numParams_4179_);
lean_dec(v_indName_3999_);
v___x_4200_ = lean_box(0);
v___y_4126_ = v_a_4137_;
v___y_4127_ = v___x_4172_;
v_a_4128_ = v___x_4200_;
goto v___jp_4125_;
}
}
else
{
lean_object* v_a_4201_; 
lean_dec(v_numNested_4181_);
lean_dec(v_all_4180_);
lean_dec(v_numParams_4179_);
lean_dec(v_indName_3999_);
v_a_4201_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_a_4201_);
lean_dec_ref(v___x_4183_);
v___y_4131_ = v_a_4137_;
v___y_4132_ = v___x_4172_;
v_a_4133_ = v_a_4201_;
goto v___jp_4130_;
}
}
}
else
{
lean_object* v___x_4202_; 
lean_dec(v_a_4174_);
lean_dec(v_indName_3999_);
v___x_4202_ = lean_box(0);
v___y_4126_ = v_a_4137_;
v___y_4127_ = v___x_4172_;
v_a_4128_ = v___x_4202_;
goto v___jp_4125_;
}
}
else
{
lean_object* v_a_4203_; 
lean_dec(v_indName_3999_);
v_a_4203_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4203_);
lean_dec_ref(v___x_4173_);
v___y_4131_ = v_a_4137_;
v___y_4132_ = v___x_4172_;
v_a_4133_ = v_a_4203_;
goto v___jp_4130_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v_res_4287_; 
v_res_4287_ = l_Lean_mkBRecOn(v_indName_4281_, v_a_4282_, v_a_4283_, v_a_4284_, v_a_4285_);
lean_dec(v_a_4285_);
lean_dec_ref(v_a_4284_);
lean_dec(v_a_4283_);
lean_dec_ref(v_a_4282_);
return v_res_4287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4288_, lean_object* v___x_4289_, lean_object* v___x_4290_, lean_object* v___x_4291_, lean_object* v___x_4292_, lean_object* v_inst_4293_, lean_object* v_R_4294_, lean_object* v_a_4295_, lean_object* v_b_4296_, lean_object* v_c_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; 
v___x_4303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4288_, v___x_4289_, v___x_4290_, v___x_4291_, v___x_4292_, v_a_4295_, v_b_4296_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
return v___x_4303_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4304_, lean_object* v___x_4305_, lean_object* v___x_4306_, lean_object* v___x_4307_, lean_object* v___x_4308_, lean_object* v_inst_4309_, lean_object* v_R_4310_, lean_object* v_a_4311_, lean_object* v_b_4312_, lean_object* v_c_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4304_, v___x_4305_, v___x_4306_, v___x_4307_, v___x_4308_, v_inst_4309_, v_R_4310_, v_a_4311_, v_b_4312_, v_c_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v_upperBound_4304_);
return v_res_4319_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4365_ = lean_unsigned_to_nat(2304625798u);
v___x_4366_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4367_ = l_Lean_Name_num___override(v___x_4366_, v___x_4365_);
return v___x_4367_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4370_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4371_ = l_Lean_Name_str___override(v___x_4370_, v___x_4369_);
return v___x_4371_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4373_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4374_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4375_ = l_Lean_Name_str___override(v___x_4374_, v___x_4373_);
return v___x_4375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4376_ = lean_unsigned_to_nat(2u);
v___x_4377_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4378_ = l_Lean_Name_num___override(v___x_4377_, v___x_4376_);
return v___x_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4380_; uint8_t v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v___x_4380_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4381_ = 0;
v___x_4382_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4383_ = l_Lean_registerTraceClass(v___x_4380_, v___x_4381_, v___x_4382_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4384_){
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4385_;
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
