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
v___x_4964__overap_436_ = lean_panic_fn(v___f_435_, v_msg_429_);
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
lean_inc(v___x_692_);
v___x_693_ = l_Lean_Level_succ___override(v___x_692_);
v___x_694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v_tail_659_);
v___x_695_ = l_Lean_Expr_const___override(v_recName_660_, v___x_694_);
v___x_696_ = l_Lean_mkAppN(v___x_695_, v___x_690_);
v_sz_697_ = lean_array_size(v___x_691_);
v___x_698_ = ((size_t)0ULL);
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
lean_dec_ref(v___x_913_);
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
v___x_928_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
lean_ctor_set(v___x_928_, 2, v___x_927_);
lean_ctor_set(v___x_928_, 3, v___x_926_);
lean_ctor_set(v___x_928_, 4, v___x_926_);
lean_ctor_set(v___x_928_, 5, v___x_926_);
lean_ctor_set(v___x_928_, 6, v___x_926_);
lean_ctor_set(v___x_928_, 7, v___x_926_);
lean_ctor_set(v___x_928_, 8, v___x_926_);
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
lean_dec_ref(v___x_1163_);
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
lean_inc(v_levelParams_1172_);
v_type_1173_ = lean_ctor_get(v_toConstantVal_1169_, 2);
lean_inc_ref(v_type_1173_);
lean_dec_ref(v_toConstantVal_1169_);
v___x_1174_ = lean_box(0);
lean_inc(v_levelParams_1172_);
v___x_1175_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_1172_, v___x_1174_);
if (lean_obj_tag(v___x_1175_) == 1)
{
lean_object* v_head_1176_; lean_object* v_tail_1177_; lean_object* v___f_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; 
v_head_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_head_1176_);
v_tail_1177_ = lean_ctor_get(v___x_1175_, 1);
lean_inc(v_tail_1177_);
lean_dec_ref(v___x_1175_);
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
lean_inc(v_a_1181_);
lean_dec_ref(v___x_1180_);
lean_inc(v_a_1181_);
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
lean_dec_ref(v___x_1184_);
v_toConstantVal_1185_ = lean_ctor_get(v_a_1181_, 0);
lean_inc_ref(v_toConstantVal_1185_);
lean_dec(v_a_1181_);
v_name_1186_ = lean_ctor_get(v_toConstantVal_1185_, 0);
lean_inc(v_name_1186_);
lean_dec_ref(v_toConstantVal_1185_);
lean_inc(v_name_1186_);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(lean_object* v_cls_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v_options_1429_; uint8_t v_hasTrace_1430_; 
v_options_1429_ = lean_ctor_get(v___y_1427_, 2);
v_hasTrace_1430_ = lean_ctor_get_uint8(v_options_1429_, sizeof(void*)*1);
if (v_hasTrace_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec(v_cls_1426_);
v___x_1431_ = lean_box(v_hasTrace_1430_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
else
{
lean_object* v_inheritedTraceOptions_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v_inheritedTraceOptions_1433_ = lean_ctor_get(v___y_1427_, 13);
v___x_1434_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___closed__1));
v___x_1435_ = l_Lean_Name_append(v___x_1434_, v_cls_1426_);
v___x_1436_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1433_, v_options_1429_, v___x_1435_);
lean_dec(v___x_1435_);
v___x_1437_ = lean_box(v___x_1436_);
v___x_1438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
return v___x_1438_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg___boxed(lean_object* v_cls_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v_cls_1439_, v___y_1440_);
lean_dec_ref(v___y_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1(lean_object* v_cls_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v_cls_1443_, v___y_1446_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___boxed(lean_object* v_cls_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1(v_cls_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
lean_dec_ref(v___y_1451_);
return v_res_1456_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = lean_unsigned_to_nat(32u);
v___x_1458_ = lean_mk_empty_array_with_capacity(v___x_1457_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1460_ = ((size_t)5ULL);
v___x_1461_ = lean_unsigned_to_nat(0u);
v___x_1462_ = lean_unsigned_to_nat(32u);
v___x_1463_ = lean_mk_empty_array_with_capacity(v___x_1462_);
v___x_1464_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__0);
v___x_1465_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
lean_ctor_set(v___x_1465_, 1, v___x_1463_);
lean_ctor_set(v___x_1465_, 2, v___x_1461_);
lean_ctor_set(v___x_1465_, 3, v___x_1461_);
lean_ctor_set_usize(v___x_1465_, 4, v___x_1460_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v_traceState_1469_; lean_object* v_traces_1470_; lean_object* v___x_1471_; lean_object* v_traceState_1472_; lean_object* v_env_1473_; lean_object* v_nextMacroScope_1474_; lean_object* v_ngen_1475_; lean_object* v_auxDeclNGen_1476_; lean_object* v_cache_1477_; lean_object* v_messages_1478_; lean_object* v_infoState_1479_; lean_object* v_snapshotTasks_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1499_; 
v___x_1468_ = lean_st_ref_get(v___y_1466_);
v_traceState_1469_ = lean_ctor_get(v___x_1468_, 4);
lean_inc_ref(v_traceState_1469_);
lean_dec(v___x_1468_);
v_traces_1470_ = lean_ctor_get(v_traceState_1469_, 0);
lean_inc_ref(v_traces_1470_);
lean_dec_ref(v_traceState_1469_);
v___x_1471_ = lean_st_ref_take(v___y_1466_);
v_traceState_1472_ = lean_ctor_get(v___x_1471_, 4);
v_env_1473_ = lean_ctor_get(v___x_1471_, 0);
v_nextMacroScope_1474_ = lean_ctor_get(v___x_1471_, 1);
v_ngen_1475_ = lean_ctor_get(v___x_1471_, 2);
v_auxDeclNGen_1476_ = lean_ctor_get(v___x_1471_, 3);
v_cache_1477_ = lean_ctor_get(v___x_1471_, 5);
v_messages_1478_ = lean_ctor_get(v___x_1471_, 6);
v_infoState_1479_ = lean_ctor_get(v___x_1471_, 7);
v_snapshotTasks_1480_ = lean_ctor_get(v___x_1471_, 8);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1482_ = v___x_1471_;
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_snapshotTasks_1480_);
lean_inc(v_infoState_1479_);
lean_inc(v_messages_1478_);
lean_inc(v_cache_1477_);
lean_inc(v_traceState_1472_);
lean_inc(v_auxDeclNGen_1476_);
lean_inc(v_ngen_1475_);
lean_inc(v_nextMacroScope_1474_);
lean_inc(v_env_1473_);
lean_dec(v___x_1471_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1499_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
uint64_t v_tid_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1497_; 
v_tid_1484_ = lean_ctor_get_uint64(v_traceState_1472_, sizeof(void*)*1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_traceState_1472_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v_traceState_1472_, 0);
lean_dec(v_unused_1498_);
v___x_1486_ = v_traceState_1472_;
v_isShared_1487_ = v_isSharedCheck_1497_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_traceState_1472_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1497_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___closed__1);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v___x_1488_);
v___x_1490_ = v___x_1486_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1488_);
lean_ctor_set_uint64(v_reuseFailAlloc_1496_, sizeof(void*)*1, v_tid_1484_);
v___x_1490_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1492_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 4, v___x_1490_);
v___x_1492_ = v___x_1482_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_env_1473_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_nextMacroScope_1474_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_ngen_1475_);
lean_ctor_set(v_reuseFailAlloc_1495_, 3, v_auxDeclNGen_1476_);
lean_ctor_set(v_reuseFailAlloc_1495_, 4, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1495_, 5, v_cache_1477_);
lean_ctor_set(v_reuseFailAlloc_1495_, 6, v_messages_1478_);
lean_ctor_set(v_reuseFailAlloc_1495_, 7, v_infoState_1479_);
lean_ctor_set(v_reuseFailAlloc_1495_, 8, v_snapshotTasks_1480_);
v___x_1492_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_st_ref_set(v___y_1466_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v_traces_1470_);
return v___x_1494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg___boxed(lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v___y_1500_);
lean_dec(v___y_1500_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2(lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v___y_1506_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___boxed(lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2(v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
return v_res_1514_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkBelow_spec__3(lean_object* v_opts_1515_, lean_object* v_opt_1516_){
_start:
{
lean_object* v_name_1517_; lean_object* v_defValue_1518_; lean_object* v_map_1519_; lean_object* v___x_1520_; 
v_name_1517_ = lean_ctor_get(v_opt_1516_, 0);
v_defValue_1518_ = lean_ctor_get(v_opt_1516_, 1);
v_map_1519_ = lean_ctor_get(v_opts_1515_, 0);
v___x_1520_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1519_, v_name_1517_);
if (lean_obj_tag(v___x_1520_) == 0)
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_unbox(v_defValue_1518_);
return v___x_1521_;
}
else
{
lean_object* v_val_1522_; 
v_val_1522_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_val_1522_);
lean_dec_ref(v___x_1520_);
if (lean_obj_tag(v_val_1522_) == 1)
{
uint8_t v_v_1523_; 
v_v_1523_ = lean_ctor_get_uint8(v_val_1522_, 0);
lean_dec_ref(v_val_1522_);
return v_v_1523_;
}
else
{
uint8_t v___x_1524_; 
lean_dec(v_val_1522_);
v___x_1524_ = lean_unbox(v_defValue_1518_);
return v___x_1524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkBelow_spec__3___boxed(lean_object* v_opts_1525_, lean_object* v_opt_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_opts_1525_, v_opt_1526_);
lean_dec_ref(v_opt_1526_);
lean_dec_ref(v_opts_1525_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0(lean_object* v_indName_1529_, lean_object* v_x_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = l_Lean_MessageData_ofName(v_indName_1529_);
v___x_1537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1537_, 0, v___x_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___lam__0___boxed(lean_object* v_indName_1538_, lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_mkBelow___lam__0(v_indName_1538_, v_x_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec_ref(v_x_1539_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(lean_object* v_upperBound_1546_, lean_object* v___x_1547_, lean_object* v___x_1548_, lean_object* v___x_1549_, lean_object* v_a_1550_, lean_object* v_b_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v___x_1557_; 
v___x_1557_ = lean_nat_dec_lt(v_a_1550_, v_upperBound_1546_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; 
lean_dec(v_a_1550_);
lean_dec(v___x_1549_);
lean_dec(v___x_1548_);
lean_dec(v___x_1547_);
v___x_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_b_1551_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1559_ = lean_unsigned_to_nat(1u);
v___x_1560_ = lean_nat_add(v_a_1550_, v___x_1559_);
lean_dec(v_a_1550_);
lean_inc(v___x_1560_);
lean_inc(v___x_1547_);
v___x_1561_ = lean_name_append_index_after(v___x_1547_, v___x_1560_);
lean_inc(v___x_1560_);
lean_inc(v___x_1548_);
v___x_1562_ = lean_name_append_index_after(v___x_1548_, v___x_1560_);
lean_inc(v___x_1549_);
v___x_1563_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1561_, v___x_1549_, v___x_1562_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1564_; 
lean_dec_ref(v___x_1563_);
v___x_1564_ = lean_box(0);
v_a_1550_ = v___x_1560_;
v_b_1551_ = v___x_1564_;
goto _start;
}
else
{
lean_dec(v___x_1560_);
lean_dec(v___x_1549_);
lean_dec(v___x_1548_);
lean_dec(v___x_1547_);
return v___x_1563_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg___boxed(lean_object* v_upperBound_1566_, lean_object* v___x_1567_, lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v_a_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_1566_, v___x_1567_, v___x_1568_, v___x_1569_, v_a_1570_, v_b_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v_upperBound_1566_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(lean_object* v_x_1578_){
_start:
{
if (lean_obj_tag(v_x_1578_) == 0)
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
v_a_1580_ = lean_ctor_get(v_x_1578_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1578_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v_x_1578_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v_x_1578_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
lean_ctor_set_tag(v___x_1582_, 1);
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1588_ = lean_ctor_get(v_x_1578_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1578_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v_x_1578_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v_x_1578_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set_tag(v___x_1590_, 0);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg___boxed(lean_object* v_x_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_x_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(lean_object* v_opts_1599_, lean_object* v_opt_1600_){
_start:
{
lean_object* v_name_1601_; lean_object* v_defValue_1602_; lean_object* v_map_1603_; lean_object* v___x_1604_; 
v_name_1601_ = lean_ctor_get(v_opt_1600_, 0);
v_defValue_1602_ = lean_ctor_get(v_opt_1600_, 1);
v_map_1603_ = lean_ctor_get(v_opts_1599_, 0);
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1603_, v_name_1601_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_inc(v_defValue_1602_);
return v_defValue_1602_;
}
else
{
lean_object* v_val_1605_; 
v_val_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_val_1605_);
lean_dec_ref(v___x_1604_);
if (lean_obj_tag(v_val_1605_) == 3)
{
lean_object* v_v_1606_; 
v_v_1606_ = lean_ctor_get(v_val_1605_, 0);
lean_inc(v_v_1606_);
lean_dec_ref(v_val_1605_);
return v_v_1606_;
}
else
{
lean_dec(v_val_1605_);
lean_inc(v_defValue_1602_);
return v_defValue_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7___boxed(lean_object* v_opts_1607_, lean_object* v_opt_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(v_opts_1607_, v_opt_1608_);
lean_dec_ref(v_opt_1608_);
lean_dec_ref(v_opts_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4(lean_object* v_e_1610_){
_start:
{
if (lean_obj_tag(v_e_1610_) == 0)
{
uint8_t v___x_1611_; 
v___x_1611_ = 2;
return v___x_1611_;
}
else
{
uint8_t v___x_1612_; 
v___x_1612_ = 0;
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4___boxed(lean_object* v_e_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4(v_e_1613_);
lean_dec_ref(v_e_1613_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6(size_t v_sz_1616_, size_t v_i_1617_, lean_object* v_bs_1618_){
_start:
{
uint8_t v___x_1619_; 
v___x_1619_ = lean_usize_dec_lt(v_i_1617_, v_sz_1616_);
if (v___x_1619_ == 0)
{
return v_bs_1618_;
}
else
{
lean_object* v_v_1620_; lean_object* v_msg_1621_; lean_object* v___x_1622_; lean_object* v_bs_x27_1623_; size_t v___x_1624_; size_t v___x_1625_; lean_object* v___x_1626_; 
v_v_1620_ = lean_array_uget_borrowed(v_bs_1618_, v_i_1617_);
v_msg_1621_ = lean_ctor_get(v_v_1620_, 1);
lean_inc_ref(v_msg_1621_);
v___x_1622_ = lean_unsigned_to_nat(0u);
v_bs_x27_1623_ = lean_array_uset(v_bs_1618_, v_i_1617_, v___x_1622_);
v___x_1624_ = ((size_t)1ULL);
v___x_1625_ = lean_usize_add(v_i_1617_, v___x_1624_);
v___x_1626_ = lean_array_uset(v_bs_x27_1623_, v_i_1617_, v_msg_1621_);
v_i_1617_ = v___x_1625_;
v_bs_1618_ = v___x_1626_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6___boxed(lean_object* v_sz_1628_, lean_object* v_i_1629_, lean_object* v_bs_1630_){
_start:
{
size_t v_sz_boxed_1631_; size_t v_i_boxed_1632_; lean_object* v_res_1633_; 
v_sz_boxed_1631_ = lean_unbox_usize(v_sz_1628_);
lean_dec(v_sz_1628_);
v_i_boxed_1632_ = lean_unbox_usize(v_i_1629_);
lean_dec(v_i_1629_);
v_res_1633_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6(v_sz_boxed_1631_, v_i_boxed_1632_, v_bs_1630_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5(lean_object* v_oldTraces_1634_, lean_object* v_data_1635_, lean_object* v_ref_1636_, lean_object* v_msg_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_fileName_1643_; lean_object* v_fileMap_1644_; lean_object* v_options_1645_; lean_object* v_currRecDepth_1646_; lean_object* v_maxRecDepth_1647_; lean_object* v_ref_1648_; lean_object* v_currNamespace_1649_; lean_object* v_openDecls_1650_; lean_object* v_initHeartbeats_1651_; lean_object* v_maxHeartbeats_1652_; lean_object* v_quotContext_1653_; lean_object* v_currMacroScope_1654_; uint8_t v_diag_1655_; lean_object* v_cancelTk_x3f_1656_; uint8_t v_suppressElabErrors_1657_; lean_object* v_inheritedTraceOptions_1658_; lean_object* v___x_1659_; lean_object* v_traceState_1660_; lean_object* v_traces_1661_; lean_object* v_ref_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; size_t v_sz_1665_; size_t v___x_1666_; lean_object* v___x_1667_; lean_object* v_msg_1668_; lean_object* v___x_1669_; lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1707_; 
v_fileName_1643_ = lean_ctor_get(v___y_1640_, 0);
v_fileMap_1644_ = lean_ctor_get(v___y_1640_, 1);
v_options_1645_ = lean_ctor_get(v___y_1640_, 2);
v_currRecDepth_1646_ = lean_ctor_get(v___y_1640_, 3);
v_maxRecDepth_1647_ = lean_ctor_get(v___y_1640_, 4);
v_ref_1648_ = lean_ctor_get(v___y_1640_, 5);
v_currNamespace_1649_ = lean_ctor_get(v___y_1640_, 6);
v_openDecls_1650_ = lean_ctor_get(v___y_1640_, 7);
v_initHeartbeats_1651_ = lean_ctor_get(v___y_1640_, 8);
v_maxHeartbeats_1652_ = lean_ctor_get(v___y_1640_, 9);
v_quotContext_1653_ = lean_ctor_get(v___y_1640_, 10);
v_currMacroScope_1654_ = lean_ctor_get(v___y_1640_, 11);
v_diag_1655_ = lean_ctor_get_uint8(v___y_1640_, sizeof(void*)*14);
v_cancelTk_x3f_1656_ = lean_ctor_get(v___y_1640_, 12);
v_suppressElabErrors_1657_ = lean_ctor_get_uint8(v___y_1640_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1658_ = lean_ctor_get(v___y_1640_, 13);
v___x_1659_ = lean_st_ref_get(v___y_1641_);
v_traceState_1660_ = lean_ctor_get(v___x_1659_, 4);
lean_inc_ref(v_traceState_1660_);
lean_dec(v___x_1659_);
v_traces_1661_ = lean_ctor_get(v_traceState_1660_, 0);
lean_inc_ref(v_traces_1661_);
lean_dec_ref(v_traceState_1660_);
v_ref_1662_ = l_Lean_replaceRef(v_ref_1636_, v_ref_1648_);
lean_inc_ref(v_inheritedTraceOptions_1658_);
lean_inc(v_cancelTk_x3f_1656_);
lean_inc(v_currMacroScope_1654_);
lean_inc(v_quotContext_1653_);
lean_inc(v_maxHeartbeats_1652_);
lean_inc(v_initHeartbeats_1651_);
lean_inc(v_openDecls_1650_);
lean_inc(v_currNamespace_1649_);
lean_inc(v_maxRecDepth_1647_);
lean_inc(v_currRecDepth_1646_);
lean_inc_ref(v_options_1645_);
lean_inc_ref(v_fileMap_1644_);
lean_inc_ref(v_fileName_1643_);
v___x_1663_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1663_, 0, v_fileName_1643_);
lean_ctor_set(v___x_1663_, 1, v_fileMap_1644_);
lean_ctor_set(v___x_1663_, 2, v_options_1645_);
lean_ctor_set(v___x_1663_, 3, v_currRecDepth_1646_);
lean_ctor_set(v___x_1663_, 4, v_maxRecDepth_1647_);
lean_ctor_set(v___x_1663_, 5, v_ref_1662_);
lean_ctor_set(v___x_1663_, 6, v_currNamespace_1649_);
lean_ctor_set(v___x_1663_, 7, v_openDecls_1650_);
lean_ctor_set(v___x_1663_, 8, v_initHeartbeats_1651_);
lean_ctor_set(v___x_1663_, 9, v_maxHeartbeats_1652_);
lean_ctor_set(v___x_1663_, 10, v_quotContext_1653_);
lean_ctor_set(v___x_1663_, 11, v_currMacroScope_1654_);
lean_ctor_set(v___x_1663_, 12, v_cancelTk_x3f_1656_);
lean_ctor_set(v___x_1663_, 13, v_inheritedTraceOptions_1658_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*14, v_diag_1655_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*14 + 1, v_suppressElabErrors_1657_);
v___x_1664_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1661_);
lean_dec_ref(v_traces_1661_);
v_sz_1665_ = lean_array_size(v___x_1664_);
v___x_1666_ = ((size_t)0ULL);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5_spec__6(v_sz_1665_, v___x_1666_, v___x_1664_);
v_msg_1668_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1668_, 0, v_data_1635_);
lean_ctor_set(v_msg_1668_, 1, v_msg_1637_);
lean_ctor_set(v_msg_1668_, 2, v___x_1667_);
v___x_1669_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6_spec__7(v_msg_1668_, v___y_1638_, v___y_1639_, v___x_1663_, v___y_1641_);
lean_dec_ref(v___x_1663_);
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1669_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1672_ = v___x_1669_;
v_isShared_1673_ = v_isSharedCheck_1707_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1669_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1707_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v_traceState_1675_; lean_object* v_env_1676_; lean_object* v_nextMacroScope_1677_; lean_object* v_ngen_1678_; lean_object* v_auxDeclNGen_1679_; lean_object* v_cache_1680_; lean_object* v_messages_1681_; lean_object* v_infoState_1682_; lean_object* v_snapshotTasks_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1706_; 
v___x_1674_ = lean_st_ref_take(v___y_1641_);
v_traceState_1675_ = lean_ctor_get(v___x_1674_, 4);
v_env_1676_ = lean_ctor_get(v___x_1674_, 0);
v_nextMacroScope_1677_ = lean_ctor_get(v___x_1674_, 1);
v_ngen_1678_ = lean_ctor_get(v___x_1674_, 2);
v_auxDeclNGen_1679_ = lean_ctor_get(v___x_1674_, 3);
v_cache_1680_ = lean_ctor_get(v___x_1674_, 5);
v_messages_1681_ = lean_ctor_get(v___x_1674_, 6);
v_infoState_1682_ = lean_ctor_get(v___x_1674_, 7);
v_snapshotTasks_1683_ = lean_ctor_get(v___x_1674_, 8);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1685_ = v___x_1674_;
v_isShared_1686_ = v_isSharedCheck_1706_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_snapshotTasks_1683_);
lean_inc(v_infoState_1682_);
lean_inc(v_messages_1681_);
lean_inc(v_cache_1680_);
lean_inc(v_traceState_1675_);
lean_inc(v_auxDeclNGen_1679_);
lean_inc(v_ngen_1678_);
lean_inc(v_nextMacroScope_1677_);
lean_inc(v_env_1676_);
lean_dec(v___x_1674_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1706_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
uint64_t v_tid_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1704_; 
v_tid_1687_ = lean_ctor_get_uint64(v_traceState_1675_, sizeof(void*)*1);
v_isSharedCheck_1704_ = !lean_is_exclusive(v_traceState_1675_);
if (v_isSharedCheck_1704_ == 0)
{
lean_object* v_unused_1705_; 
v_unused_1705_ = lean_ctor_get(v_traceState_1675_, 0);
lean_dec(v_unused_1705_);
v___x_1689_ = v_traceState_1675_;
v_isShared_1690_ = v_isSharedCheck_1704_;
goto v_resetjp_1688_;
}
else
{
lean_dec(v_traceState_1675_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1704_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1694_; 
v___x_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1691_, 0, v_ref_1636_);
lean_ctor_set(v___x_1691_, 1, v_a_1670_);
v___x_1692_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1634_, v___x_1691_);
if (v_isShared_1690_ == 0)
{
lean_ctor_set(v___x_1689_, 0, v___x_1692_);
v___x_1694_ = v___x_1689_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1692_);
lean_ctor_set_uint64(v_reuseFailAlloc_1703_, sizeof(void*)*1, v_tid_1687_);
v___x_1694_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1696_; 
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 4, v___x_1694_);
v___x_1696_ = v___x_1685_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_env_1676_);
lean_ctor_set(v_reuseFailAlloc_1702_, 1, v_nextMacroScope_1677_);
lean_ctor_set(v_reuseFailAlloc_1702_, 2, v_ngen_1678_);
lean_ctor_set(v_reuseFailAlloc_1702_, 3, v_auxDeclNGen_1679_);
lean_ctor_set(v_reuseFailAlloc_1702_, 4, v___x_1694_);
lean_ctor_set(v_reuseFailAlloc_1702_, 5, v_cache_1680_);
lean_ctor_set(v_reuseFailAlloc_1702_, 6, v_messages_1681_);
lean_ctor_set(v_reuseFailAlloc_1702_, 7, v_infoState_1682_);
lean_ctor_set(v_reuseFailAlloc_1702_, 8, v_snapshotTasks_1683_);
v___x_1696_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1697_ = lean_st_ref_set(v___y_1641_, v___x_1696_);
v___x_1698_ = lean_box(0);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 0, v___x_1698_);
v___x_1700_ = v___x_1672_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5___boxed(lean_object* v_oldTraces_1708_, lean_object* v_data_1709_, lean_object* v_ref_1710_, lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5(v_oldTraces_1708_, v_data_1709_, v_ref_1710_, v_msg_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1717_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__0));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1721_; double v___x_1722_; 
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_float_of_nat(v___x_1721_);
return v___x_1722_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__3));
v___x_1725_ = l_Lean_stringToMessageData(v___x_1724_);
return v___x_1725_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5(void){
_start:
{
lean_object* v___x_1726_; double v___x_1727_; 
v___x_1726_ = lean_unsigned_to_nat(1000u);
v___x_1727_ = lean_float_of_nat(v___x_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(lean_object* v_cls_1728_, uint8_t v_collapsed_1729_, lean_object* v_tag_1730_, lean_object* v_opts_1731_, uint8_t v_clsEnabled_1732_, lean_object* v_oldTraces_1733_, lean_object* v_msg_1734_, lean_object* v_resStartStop_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_fst_1741_; lean_object* v_snd_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1832_; 
v_fst_1741_ = lean_ctor_get(v_resStartStop_1735_, 0);
v_snd_1742_ = lean_ctor_get(v_resStartStop_1735_, 1);
v_isSharedCheck_1832_ = !lean_is_exclusive(v_resStartStop_1735_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1744_ = v_resStartStop_1735_;
v_isShared_1745_ = v_isSharedCheck_1832_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_snd_1742_);
lean_inc(v_fst_1741_);
lean_dec(v_resStartStop_1735_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1832_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___y_1747_; lean_object* v___y_1748_; lean_object* v_data_1749_; lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1831_; 
v_fst_1752_ = lean_ctor_get(v_snd_1742_, 0);
v_snd_1753_ = lean_ctor_get(v_snd_1742_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_snd_1742_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1755_ = v_snd_1742_;
v_isShared_1756_ = v_isSharedCheck_1831_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_inc(v_fst_1752_);
lean_dec(v_snd_1742_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1831_;
goto v_resetjp_1754_;
}
v___jp_1746_:
{
lean_object* v___x_1750_; 
lean_inc(v___y_1748_);
v___x_1750_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__5(v_oldTraces_1733_, v_data_1749_, v___y_1748_, v___y_1747_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref(v___x_1750_);
v___x_1751_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_fst_1741_);
return v___x_1751_;
}
else
{
lean_dec(v_fst_1741_);
return v___x_1750_;
}
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; uint8_t v___x_1758_; lean_object* v___y_1760_; lean_object* v_a_1761_; uint8_t v___y_1785_; double v___y_1816_; 
v___x_1757_ = l_Lean_trace_profiler;
v___x_1758_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_opts_1731_, v___x_1757_);
if (v___x_1758_ == 0)
{
v___y_1785_ = v___x_1758_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1822_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_opts_1731_, v___x_1821_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; double v___x_1825_; double v___x_1826_; double v___x_1827_; 
v___x_1823_ = l_Lean_trace_profiler_threshold;
v___x_1824_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(v_opts_1731_, v___x_1823_);
v___x_1825_ = lean_float_of_nat(v___x_1824_);
v___x_1826_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__5);
v___x_1827_ = lean_float_div(v___x_1825_, v___x_1826_);
v___y_1816_ = v___x_1827_;
goto v___jp_1815_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; double v___x_1830_; 
v___x_1828_ = l_Lean_trace_profiler_threshold;
v___x_1829_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__7(v_opts_1731_, v___x_1828_);
v___x_1830_ = lean_float_of_nat(v___x_1829_);
v___y_1816_ = v___x_1830_;
goto v___jp_1815_;
}
}
v___jp_1759_:
{
uint8_t v_result_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v_result_1762_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__4(v_fst_1741_);
v___x_1763_ = l_Lean_TraceResult_toEmoji(v_result_1762_);
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
v___x_1765_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__1);
if (v_isShared_1756_ == 0)
{
lean_ctor_set_tag(v___x_1755_, 7);
lean_ctor_set(v___x_1755_, 1, v___x_1765_);
lean_ctor_set(v___x_1755_, 0, v___x_1764_);
v___x_1767_ = v___x_1755_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v_m_1769_; 
if (v_isShared_1745_ == 0)
{
lean_ctor_set_tag(v___x_1744_, 7);
lean_ctor_set(v___x_1744_, 1, v_a_1761_);
lean_ctor_set(v___x_1744_, 0, v___x_1767_);
v_m_1769_ = v___x_1744_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1777_, 1, v_a_1761_);
v_m_1769_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; double v___x_1772_; lean_object* v_data_1773_; 
v___x_1770_ = lean_box(v_result_1762_);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
v___x_1772_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__2);
lean_inc_ref(v_tag_1730_);
lean_inc_ref(v___x_1771_);
lean_inc(v_cls_1728_);
v_data_1773_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1773_, 0, v_cls_1728_);
lean_ctor_set(v_data_1773_, 1, v___x_1771_);
lean_ctor_set(v_data_1773_, 2, v_tag_1730_);
lean_ctor_set_float(v_data_1773_, sizeof(void*)*3, v___x_1772_);
lean_ctor_set_float(v_data_1773_, sizeof(void*)*3 + 8, v___x_1772_);
lean_ctor_set_uint8(v_data_1773_, sizeof(void*)*3 + 16, v_collapsed_1729_);
if (v___x_1758_ == 0)
{
lean_dec_ref(v___x_1771_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_dec_ref(v_tag_1730_);
lean_dec(v_cls_1728_);
v___y_1747_ = v_m_1769_;
v___y_1748_ = v___y_1760_;
v_data_1749_ = v_data_1773_;
goto v___jp_1746_;
}
else
{
lean_object* v_data_1774_; double v___x_1775_; double v___x_1776_; 
lean_dec_ref(v_data_1773_);
v_data_1774_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1774_, 0, v_cls_1728_);
lean_ctor_set(v_data_1774_, 1, v___x_1771_);
lean_ctor_set(v_data_1774_, 2, v_tag_1730_);
v___x_1775_ = lean_unbox_float(v_fst_1752_);
lean_dec(v_fst_1752_);
lean_ctor_set_float(v_data_1774_, sizeof(void*)*3, v___x_1775_);
v___x_1776_ = lean_unbox_float(v_snd_1753_);
lean_dec(v_snd_1753_);
lean_ctor_set_float(v_data_1774_, sizeof(void*)*3 + 8, v___x_1776_);
lean_ctor_set_uint8(v_data_1774_, sizeof(void*)*3 + 16, v_collapsed_1729_);
v___y_1747_ = v_m_1769_;
v___y_1748_ = v___y_1760_;
v_data_1749_ = v_data_1774_;
goto v___jp_1746_;
}
}
}
}
v___jp_1779_:
{
lean_object* v_ref_1780_; lean_object* v___x_1781_; 
v_ref_1780_ = lean_ctor_get(v___y_1738_, 5);
lean_inc(v___y_1739_);
lean_inc_ref(v___y_1738_);
lean_inc(v___y_1737_);
lean_inc_ref(v___y_1736_);
lean_inc(v_fst_1741_);
v___x_1781_ = lean_apply_6(v_msg_1734_, v_fst_1741_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, lean_box(0));
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v___x_1781_);
v___y_1760_ = v_ref_1780_;
v_a_1761_ = v_a_1782_;
goto v___jp_1759_;
}
else
{
lean_object* v___x_1783_; 
lean_dec_ref(v___x_1781_);
v___x_1783_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___closed__4);
v___y_1760_ = v_ref_1780_;
v_a_1761_ = v___x_1783_;
goto v___jp_1759_;
}
}
v___jp_1784_:
{
if (v_clsEnabled_1732_ == 0)
{
if (v___y_1785_ == 0)
{
lean_object* v___x_1786_; lean_object* v_traceState_1787_; lean_object* v_env_1788_; lean_object* v_nextMacroScope_1789_; lean_object* v_ngen_1790_; lean_object* v_auxDeclNGen_1791_; lean_object* v_cache_1792_; lean_object* v_messages_1793_; lean_object* v_infoState_1794_; lean_object* v_snapshotTasks_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1814_; 
lean_del_object(v___x_1755_);
lean_dec(v_snd_1753_);
lean_dec(v_fst_1752_);
lean_del_object(v___x_1744_);
lean_dec_ref(v_msg_1734_);
lean_dec_ref(v_tag_1730_);
lean_dec(v_cls_1728_);
v___x_1786_ = lean_st_ref_take(v___y_1739_);
v_traceState_1787_ = lean_ctor_get(v___x_1786_, 4);
v_env_1788_ = lean_ctor_get(v___x_1786_, 0);
v_nextMacroScope_1789_ = lean_ctor_get(v___x_1786_, 1);
v_ngen_1790_ = lean_ctor_get(v___x_1786_, 2);
v_auxDeclNGen_1791_ = lean_ctor_get(v___x_1786_, 3);
v_cache_1792_ = lean_ctor_get(v___x_1786_, 5);
v_messages_1793_ = lean_ctor_get(v___x_1786_, 6);
v_infoState_1794_ = lean_ctor_get(v___x_1786_, 7);
v_snapshotTasks_1795_ = lean_ctor_get(v___x_1786_, 8);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1797_ = v___x_1786_;
v_isShared_1798_ = v_isSharedCheck_1814_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_snapshotTasks_1795_);
lean_inc(v_infoState_1794_);
lean_inc(v_messages_1793_);
lean_inc(v_cache_1792_);
lean_inc(v_traceState_1787_);
lean_inc(v_auxDeclNGen_1791_);
lean_inc(v_ngen_1790_);
lean_inc(v_nextMacroScope_1789_);
lean_inc(v_env_1788_);
lean_dec(v___x_1786_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1814_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
uint64_t v_tid_1799_; lean_object* v_traces_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1813_; 
v_tid_1799_ = lean_ctor_get_uint64(v_traceState_1787_, sizeof(void*)*1);
v_traces_1800_ = lean_ctor_get(v_traceState_1787_, 0);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_traceState_1787_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1802_ = v_traceState_1787_;
v_isShared_1803_ = v_isSharedCheck_1813_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_traces_1800_);
lean_dec(v_traceState_1787_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1813_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1733_, v_traces_1800_);
lean_dec_ref(v_traces_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1804_);
lean_ctor_set_uint64(v_reuseFailAlloc_1812_, sizeof(void*)*1, v_tid_1799_);
v___x_1806_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 4, v___x_1806_);
v___x_1808_ = v___x_1797_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_env_1788_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_nextMacroScope_1789_);
lean_ctor_set(v_reuseFailAlloc_1811_, 2, v_ngen_1790_);
lean_ctor_set(v_reuseFailAlloc_1811_, 3, v_auxDeclNGen_1791_);
lean_ctor_set(v_reuseFailAlloc_1811_, 4, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1811_, 5, v_cache_1792_);
lean_ctor_set(v_reuseFailAlloc_1811_, 6, v_messages_1793_);
lean_ctor_set(v_reuseFailAlloc_1811_, 7, v_infoState_1794_);
lean_ctor_set(v_reuseFailAlloc_1811_, 8, v_snapshotTasks_1795_);
v___x_1808_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = lean_st_ref_set(v___y_1739_, v___x_1808_);
v___x_1810_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_fst_1741_);
return v___x_1810_;
}
}
}
}
}
else
{
goto v___jp_1779_;
}
}
else
{
goto v___jp_1779_;
}
}
v___jp_1815_:
{
double v___x_1817_; double v___x_1818_; double v___x_1819_; uint8_t v___x_1820_; 
v___x_1817_ = lean_unbox_float(v_snd_1753_);
v___x_1818_ = lean_unbox_float(v_fst_1752_);
v___x_1819_ = lean_float_sub(v___x_1817_, v___x_1818_);
v___x_1820_ = lean_float_decLt(v___y_1816_, v___x_1819_);
v___y_1785_ = v___x_1820_;
goto v___jp_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4___boxed(lean_object* v_cls_1833_, lean_object* v_collapsed_1834_, lean_object* v_tag_1835_, lean_object* v_opts_1836_, lean_object* v_clsEnabled_1837_, lean_object* v_oldTraces_1838_, lean_object* v_msg_1839_, lean_object* v_resStartStop_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
uint8_t v_collapsed_boxed_1846_; uint8_t v_clsEnabled_boxed_1847_; lean_object* v_res_1848_; 
v_collapsed_boxed_1846_ = lean_unbox(v_collapsed_1834_);
v_clsEnabled_boxed_1847_ = lean_unbox(v_clsEnabled_1837_);
v_res_1848_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v_cls_1833_, v_collapsed_boxed_1846_, v_tag_1835_, v_opts_1836_, v_clsEnabled_boxed_1847_, v_oldTraces_1838_, v_msg_1839_, v_resStartStop_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v_opts_1836_);
return v_res_1848_;
}
}
static double _init_l_Lean_mkBelow___closed__4(void){
_start:
{
lean_object* v___x_1855_; double v___x_1856_; 
v___x_1855_ = lean_unsigned_to_nat(1000000000u);
v___x_1856_ = lean_float_of_nat(v___x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow(lean_object* v_indName_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_){
_start:
{
lean_object* v_options_1863_; uint8_t v_hasTrace_1864_; 
v_options_1863_ = lean_ctor_get(v_a_1860_, 2);
v_hasTrace_1864_ = lean_ctor_get_uint8(v_options_1863_, sizeof(void*)*1);
if (v_hasTrace_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_inc(v_indName_1857_);
v___x_1865_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1865_) == 0)
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1930_; 
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1930_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1930_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
if (lean_obj_tag(v_a_1866_) == 5)
{
lean_object* v_val_1870_; uint8_t v_isRec_1871_; 
v_val_1870_ = lean_ctor_get(v_a_1866_, 0);
lean_inc_ref(v_val_1870_);
lean_dec_ref(v_a_1866_);
v_isRec_1871_ = lean_ctor_get_uint8(v_val_1870_, sizeof(void*)*6);
if (v_isRec_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
lean_dec_ref(v_val_1870_);
lean_dec(v_indName_1857_);
v___x_1872_ = lean_box(0);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1872_);
v___x_1874_ = v___x_1868_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
else
{
lean_object* v_toConstantVal_1876_; lean_object* v_numParams_1877_; lean_object* v_all_1878_; lean_object* v_numNested_1879_; lean_object* v_type_1880_; lean_object* v___x_1881_; 
lean_del_object(v___x_1868_);
v_toConstantVal_1876_ = lean_ctor_get(v_val_1870_, 0);
lean_inc_ref(v_toConstantVal_1876_);
v_numParams_1877_ = lean_ctor_get(v_val_1870_, 1);
lean_inc(v_numParams_1877_);
v_all_1878_ = lean_ctor_get(v_val_1870_, 3);
lean_inc(v_all_1878_);
v_numNested_1879_ = lean_ctor_get(v_val_1870_, 5);
lean_inc(v_numNested_1879_);
lean_dec_ref(v_val_1870_);
v_type_1880_ = lean_ctor_get(v_toConstantVal_1876_, 2);
lean_inc_ref(v_type_1880_);
lean_dec_ref(v_toConstantVal_1876_);
v___x_1881_ = l_Lean_Meta_isPropFormerType(v_type_1880_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1917_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1884_ = v___x_1881_;
v_isShared_1885_ = v_isSharedCheck_1917_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_a_1882_);
lean_dec(v___x_1881_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1917_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
uint8_t v___x_1886_; 
v___x_1886_ = lean_unbox(v_a_1882_);
lean_dec(v_a_1882_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
lean_del_object(v___x_1884_);
lean_inc(v_indName_1857_);
v___x_1887_ = l_Lean_mkRecName(v_indName_1857_);
lean_inc(v_indName_1857_);
v___x_1888_ = l_Lean_mkBelowName(v_indName_1857_);
lean_inc(v___x_1888_);
lean_inc(v_numParams_1877_);
lean_inc(v___x_1887_);
v___x_1889_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_1887_, v_numParams_1877_, v___x_1888_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1911_; 
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v___x_1889_, 0);
lean_dec(v_unused_1912_);
v___x_1891_ = v___x_1889_;
v_isShared_1892_ = v_isSharedCheck_1911_;
goto v_resetjp_1890_;
}
else
{
lean_dec(v___x_1889_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1911_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_unsigned_to_nat(0u);
v___x_1895_ = l_List_get_x21Internal___redArg(v___x_1893_, v_all_1878_, v___x_1894_);
lean_dec(v_all_1878_);
v___x_1896_ = lean_name_eq(v___x_1895_, v_indName_1857_);
lean_dec(v_indName_1857_);
lean_dec(v___x_1895_);
if (v___x_1896_ == 0)
{
lean_object* v___x_1897_; lean_object* v___x_1899_; 
lean_dec(v___x_1888_);
lean_dec(v___x_1887_);
lean_dec(v_numNested_1879_);
lean_dec(v_numParams_1877_);
v___x_1897_ = lean_box(0);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 0, v___x_1897_);
v___x_1899_ = v___x_1891_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
else
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_del_object(v___x_1891_);
v___x_1901_ = lean_box(0);
v___x_1902_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_1879_, v___x_1887_, v___x_1888_, v_numParams_1877_, v___x_1894_, v___x_1901_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_numNested_1879_);
if (lean_obj_tag(v___x_1902_) == 0)
{
lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1902_);
if (v_isSharedCheck_1909_ == 0)
{
lean_object* v_unused_1910_; 
v_unused_1910_ = lean_ctor_get(v___x_1902_, 0);
lean_dec(v_unused_1910_);
v___x_1904_ = v___x_1902_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_dec(v___x_1902_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 0, v___x_1901_);
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1901_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
else
{
return v___x_1902_;
}
}
}
}
else
{
lean_dec(v___x_1888_);
lean_dec(v___x_1887_);
lean_dec(v_numNested_1879_);
lean_dec(v_all_1878_);
lean_dec(v_numParams_1877_);
lean_dec(v_indName_1857_);
return v___x_1889_;
}
}
else
{
lean_object* v___x_1913_; lean_object* v___x_1915_; 
lean_dec(v_numNested_1879_);
lean_dec(v_all_1878_);
lean_dec(v_numParams_1877_);
lean_dec(v_indName_1857_);
v___x_1913_ = lean_box(0);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 0, v___x_1913_);
v___x_1915_ = v___x_1884_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_numNested_1879_);
lean_dec(v_all_1878_);
lean_dec(v_numParams_1877_);
lean_dec(v_indName_1857_);
v_a_1918_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1881_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1881_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1928_; 
lean_dec(v_a_1866_);
lean_dec(v_indName_1857_);
v___x_1926_ = lean_box(0);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1926_);
v___x_1928_ = v___x_1868_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec(v_indName_1857_);
v_a_1931_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1865_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1865_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_2142_; 
v___x_1939_ = ((lean_object*)(l_Lean_mkBelow___closed__2));
v___x_1940_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v___x_1939_, v_a_1860_);
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_1943_ = v___x_1940_;
v_isShared_1944_ = v_isSharedCheck_2142_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_2142_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___f_1945_; lean_object* v___x_1946_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v_a_1950_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v_a_1966_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v_a_1973_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v_a_1978_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v_a_1991_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v_a_1996_; uint8_t v___x_2065_; 
lean_inc(v_indName_1857_);
v___f_1945_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1945_, 0, v_indName_1857_);
v___x_1946_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_2065_ = lean_unbox(v_a_1941_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = l_Lean_trace_profiler;
v___x_2067_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_1863_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
lean_dec_ref(v___f_1945_);
lean_del_object(v___x_1943_);
lean_dec(v_a_1941_);
lean_inc(v_indName_1857_);
v___x_2068_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2133_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2071_ = v___x_2068_;
v_isShared_2072_ = v_isSharedCheck_2133_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2068_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2133_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
if (lean_obj_tag(v_a_2069_) == 5)
{
lean_object* v_val_2073_; uint8_t v_isRec_2074_; 
v_val_2073_ = lean_ctor_get(v_a_2069_, 0);
lean_inc_ref(v_val_2073_);
lean_dec_ref(v_a_2069_);
v_isRec_2074_ = lean_ctor_get_uint8(v_val_2073_, sizeof(void*)*6);
if (v_isRec_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
lean_dec_ref(v_val_2073_);
lean_dec(v_indName_1857_);
v___x_2075_ = lean_box(0);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2075_);
v___x_2077_ = v___x_2071_;
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
else
{
lean_object* v_toConstantVal_2079_; lean_object* v_numParams_2080_; lean_object* v_all_2081_; lean_object* v_numNested_2082_; lean_object* v_type_2083_; lean_object* v___x_2084_; 
lean_del_object(v___x_2071_);
v_toConstantVal_2079_ = lean_ctor_get(v_val_2073_, 0);
lean_inc_ref(v_toConstantVal_2079_);
v_numParams_2080_ = lean_ctor_get(v_val_2073_, 1);
lean_inc(v_numParams_2080_);
v_all_2081_ = lean_ctor_get(v_val_2073_, 3);
lean_inc(v_all_2081_);
v_numNested_2082_ = lean_ctor_get(v_val_2073_, 5);
lean_inc(v_numNested_2082_);
lean_dec_ref(v_val_2073_);
v_type_2083_ = lean_ctor_get(v_toConstantVal_2079_, 2);
lean_inc_ref(v_type_2083_);
lean_dec_ref(v_toConstantVal_2079_);
v___x_2084_ = l_Lean_Meta_isPropFormerType(v_type_2083_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2084_) == 0)
{
lean_object* v_a_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2120_; 
v_a_2085_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2087_ = v___x_2084_;
v_isShared_2088_ = v_isSharedCheck_2120_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_a_2085_);
lean_dec(v___x_2084_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2120_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_unbox(v_a_2085_);
lean_dec(v_a_2085_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
lean_del_object(v___x_2087_);
lean_inc(v_indName_1857_);
v___x_2090_ = l_Lean_mkRecName(v_indName_1857_);
lean_inc(v_indName_1857_);
v___x_2091_ = l_Lean_mkBelowName(v_indName_1857_);
lean_inc(v___x_2091_);
lean_inc(v_numParams_2080_);
lean_inc(v___x_2090_);
v___x_2092_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2090_, v_numParams_2080_, v___x_2091_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2092_) == 0)
{
lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2114_; 
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2092_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v___x_2092_, 0);
lean_dec(v_unused_2115_);
v___x_2094_ = v___x_2092_;
v_isShared_2095_ = v_isSharedCheck_2114_;
goto v_resetjp_2093_;
}
else
{
lean_dec(v___x_2092_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2114_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2096_ = lean_box(0);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = l_List_get_x21Internal___redArg(v___x_2096_, v_all_2081_, v___x_2097_);
lean_dec(v_all_2081_);
v___x_2099_ = lean_name_eq(v___x_2098_, v_indName_1857_);
lean_dec(v_indName_1857_);
lean_dec(v___x_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2100_; lean_object* v___x_2102_; 
lean_dec(v___x_2091_);
lean_dec(v___x_2090_);
lean_dec(v_numNested_2082_);
lean_dec(v_numParams_2080_);
v___x_2100_ = lean_box(0);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2100_);
v___x_2102_ = v___x_2094_;
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
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_del_object(v___x_2094_);
v___x_2104_ = lean_box(0);
v___x_2105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2082_, v___x_2090_, v___x_2091_, v_numParams_2080_, v___x_2097_, v___x_2104_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_numNested_2082_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v___x_2105_, 0);
lean_dec(v_unused_2113_);
v___x_2107_ = v___x_2105_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_dec(v___x_2105_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2104_);
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2104_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
else
{
return v___x_2105_;
}
}
}
}
else
{
lean_dec(v___x_2091_);
lean_dec(v___x_2090_);
lean_dec(v_numNested_2082_);
lean_dec(v_all_2081_);
lean_dec(v_numParams_2080_);
lean_dec(v_indName_1857_);
return v___x_2092_;
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2118_; 
lean_dec(v_numNested_2082_);
lean_dec(v_all_2081_);
lean_dec(v_numParams_2080_);
lean_dec(v_indName_1857_);
v___x_2116_ = lean_box(0);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2116_);
v___x_2118_ = v___x_2087_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_numNested_2082_);
lean_dec(v_all_2081_);
lean_dec(v_numParams_2080_);
lean_dec(v_indName_1857_);
v_a_2121_ = lean_ctor_get(v___x_2084_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2084_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2084_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2084_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2131_; 
lean_dec(v_a_2069_);
lean_dec(v_indName_1857_);
v___x_2129_ = lean_box(0);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2129_);
v___x_2131_ = v___x_2071_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_indName_1857_);
v_a_2134_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2068_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2068_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
else
{
goto v___jp_1998_;
}
}
else
{
goto v___jp_1998_;
}
v___jp_1947_:
{
lean_object* v___x_1951_; double v___x_1952_; double v___x_1953_; double v___x_1954_; double v___x_1955_; double v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; 
v___x_1951_ = lean_io_mono_nanos_now();
v___x_1952_ = lean_float_of_nat(v___y_1949_);
v___x_1953_ = lean_float_once(&l_Lean_mkBelow___closed__4, &l_Lean_mkBelow___closed__4_once, _init_l_Lean_mkBelow___closed__4);
v___x_1954_ = lean_float_div(v___x_1952_, v___x_1953_);
v___x_1955_ = lean_float_of_nat(v___x_1951_);
v___x_1956_ = lean_float_div(v___x_1955_, v___x_1953_);
v___x_1957_ = lean_box_float(v___x_1954_);
v___x_1958_ = lean_box_float(v___x_1956_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v_a_1950_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_unbox(v_a_1941_);
lean_dec(v_a_1941_);
v___x_1962_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_1939_, v_hasTrace_1864_, v___x_1946_, v_options_1863_, v___x_1961_, v___y_1948_, v___f_1945_, v___x_1960_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1962_;
}
v___jp_1963_:
{
lean_object* v___x_1968_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set_tag(v___x_1943_, 1);
lean_ctor_set(v___x_1943_, 0, v_a_1966_);
v___x_1968_ = v___x_1943_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1966_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
v___y_1948_ = v___y_1964_;
v___y_1949_ = v___y_1965_;
v_a_1950_ = v___x_1968_;
goto v___jp_1947_;
}
}
v___jp_1970_:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v_a_1973_);
v___y_1948_ = v___y_1971_;
v___y_1949_ = v___y_1972_;
v_a_1950_ = v___x_1974_;
goto v___jp_1947_;
}
v___jp_1975_:
{
lean_object* v___x_1979_; double v___x_1980_; double v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; 
v___x_1979_ = lean_io_get_num_heartbeats();
v___x_1980_ = lean_float_of_nat(v___y_1977_);
v___x_1981_ = lean_float_of_nat(v___x_1979_);
v___x_1982_ = lean_box_float(v___x_1980_);
v___x_1983_ = lean_box_float(v___x_1981_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v_a_1978_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_unbox(v_a_1941_);
lean_dec(v_a_1941_);
v___x_1987_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_1939_, v_hasTrace_1864_, v___x_1946_, v_options_1863_, v___x_1986_, v___y_1976_, v___f_1945_, v___x_1985_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
return v___x_1987_;
}
v___jp_1988_:
{
lean_object* v___x_1992_; 
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_a_1991_);
v___y_1976_ = v___y_1989_;
v___y_1977_ = v___y_1990_;
v_a_1978_ = v___x_1992_;
goto v___jp_1975_;
}
v___jp_1993_:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1997_, 0, v_a_1996_);
v___y_1976_ = v___y_1994_;
v___y_1977_ = v___y_1995_;
v_a_1978_ = v___x_1997_;
goto v___jp_1975_;
}
v___jp_1998_:
{
lean_object* v___x_1999_; lean_object* v_a_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_1999_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v_a_1861_);
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref(v___x_1999_);
v___x_2001_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2002_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_1863_, v___x_2001_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_io_mono_nanos_now();
lean_inc(v_indName_1857_);
v___x_2004_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
if (lean_obj_tag(v_a_2005_) == 5)
{
lean_object* v_val_2006_; uint8_t v_isRec_2007_; 
v_val_2006_ = lean_ctor_get(v_a_2005_, 0);
lean_inc_ref(v_val_2006_);
lean_dec_ref(v_a_2005_);
v_isRec_2007_ = lean_ctor_get_uint8(v_val_2006_, sizeof(void*)*6);
if (v_isRec_2007_ == 0)
{
lean_object* v___x_2008_; 
lean_dec_ref(v_val_2006_);
lean_dec(v_indName_1857_);
v___x_2008_ = lean_box(0);
v___y_1964_ = v_a_2000_;
v___y_1965_ = v___x_2003_;
v_a_1966_ = v___x_2008_;
goto v___jp_1963_;
}
else
{
lean_object* v_toConstantVal_2009_; lean_object* v_numParams_2010_; lean_object* v_all_2011_; lean_object* v_numNested_2012_; lean_object* v_type_2013_; lean_object* v___x_2014_; 
v_toConstantVal_2009_ = lean_ctor_get(v_val_2006_, 0);
lean_inc_ref(v_toConstantVal_2009_);
v_numParams_2010_ = lean_ctor_get(v_val_2006_, 1);
lean_inc(v_numParams_2010_);
v_all_2011_ = lean_ctor_get(v_val_2006_, 3);
lean_inc(v_all_2011_);
v_numNested_2012_ = lean_ctor_get(v_val_2006_, 5);
lean_inc(v_numNested_2012_);
lean_dec_ref(v_val_2006_);
v_type_2013_ = lean_ctor_get(v_toConstantVal_2009_, 2);
lean_inc_ref(v_type_2013_);
lean_dec_ref(v_toConstantVal_2009_);
v___x_2014_ = l_Lean_Meta_isPropFormerType(v_type_2013_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; uint8_t v___x_2016_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
v___x_2016_ = lean_unbox(v_a_2015_);
lean_dec(v_a_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
lean_inc(v_indName_1857_);
v___x_2017_ = l_Lean_mkRecName(v_indName_1857_);
lean_inc(v_indName_1857_);
v___x_2018_ = l_Lean_mkBelowName(v_indName_1857_);
lean_inc(v___x_2018_);
lean_inc(v_numParams_2010_);
lean_inc(v___x_2017_);
v___x_2019_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2017_, v_numParams_2010_, v___x_2018_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; 
lean_dec_ref(v___x_2019_);
v___x_2020_ = lean_box(0);
v___x_2021_ = lean_unsigned_to_nat(0u);
v___x_2022_ = l_List_get_x21Internal___redArg(v___x_2020_, v_all_2011_, v___x_2021_);
lean_dec(v_all_2011_);
v___x_2023_ = lean_name_eq(v___x_2022_, v_indName_1857_);
lean_dec(v_indName_1857_);
lean_dec(v___x_2022_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
lean_dec(v___x_2018_);
lean_dec(v___x_2017_);
lean_dec(v_numNested_2012_);
lean_dec(v_numParams_2010_);
v___x_2024_ = lean_box(0);
v___y_1964_ = v_a_2000_;
v___y_1965_ = v___x_2003_;
v_a_1966_ = v___x_2024_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = lean_box(0);
v___x_2026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2012_, v___x_2017_, v___x_2018_, v_numParams_2010_, v___x_2021_, v___x_2025_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_numNested_2012_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_dec_ref(v___x_2026_);
v___y_1964_ = v_a_2000_;
v___y_1965_ = v___x_2003_;
v_a_1966_ = v___x_2025_;
goto v___jp_1963_;
}
else
{
lean_object* v_a_2027_; 
lean_del_object(v___x_1943_);
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v___y_1971_ = v_a_2000_;
v___y_1972_ = v___x_2003_;
v_a_1973_ = v_a_2027_;
goto v___jp_1970_;
}
}
}
else
{
lean_dec(v___x_2018_);
lean_dec(v___x_2017_);
lean_dec(v_numNested_2012_);
lean_dec(v_all_2011_);
lean_dec(v_numParams_2010_);
lean_dec(v_indName_1857_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2028_; 
v_a_2028_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2019_);
v___y_1964_ = v_a_2000_;
v___y_1965_ = v___x_2003_;
v_a_1966_ = v_a_2028_;
goto v___jp_1963_;
}
else
{
lean_object* v_a_2029_; 
lean_del_object(v___x_1943_);
v_a_2029_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2019_);
v___y_1971_ = v_a_2000_;
v___y_1972_ = v___x_2003_;
v_a_1973_ = v_a_2029_;
goto v___jp_1970_;
}
}
}
else
{
lean_object* v___x_2030_; 
lean_dec(v_numNested_2012_);
lean_dec(v_all_2011_);
lean_dec(v_numParams_2010_);
lean_dec(v_indName_1857_);
v___x_2030_ = lean_box(0);
v___y_1964_ = v_a_2000_;
v___y_1965_ = v___x_2003_;
v_a_1966_ = v___x_2030_;
goto v___jp_1963_;
}
}
else
{
lean_object* v_a_2031_; 
lean_dec(v_numNested_2012_);
lean_dec(v_all_2011_);
lean_dec(v_numParams_2010_);
lean_del_object(v___x_1943_);
lean_dec(v_indName_1857_);
v_a_2031_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2014_);
v___y_1971_ = v_a_2000_;
v___y_1972_ = v___x_2003_;
v_a_1973_ = v_a_2031_;
goto v___jp_1970_;
}
}
}
else
{
lean_object* v___x_2032_; 
lean_dec(v_a_2005_);
lean_dec(v_indName_1857_);
v___x_2032_ = lean_box(0);
v___y_1964_ = v_a_2000_;
v___y_1965_ = v___x_2003_;
v_a_1966_ = v___x_2032_;
goto v___jp_1963_;
}
}
else
{
lean_object* v_a_2033_; 
lean_del_object(v___x_1943_);
lean_dec(v_indName_1857_);
v_a_2033_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2004_);
v___y_1971_ = v_a_2000_;
v___y_1972_ = v___x_2003_;
v_a_1973_ = v_a_2033_;
goto v___jp_1970_;
}
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_del_object(v___x_1943_);
v___x_2034_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_1857_);
v___x_2035_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v_a_2036_; 
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref(v___x_2035_);
if (lean_obj_tag(v_a_2036_) == 5)
{
lean_object* v_val_2037_; uint8_t v_isRec_2038_; 
v_val_2037_ = lean_ctor_get(v_a_2036_, 0);
lean_inc_ref(v_val_2037_);
lean_dec_ref(v_a_2036_);
v_isRec_2038_ = lean_ctor_get_uint8(v_val_2037_, sizeof(void*)*6);
if (v_isRec_2038_ == 0)
{
lean_object* v___x_2039_; 
lean_dec_ref(v_val_2037_);
lean_dec(v_indName_1857_);
v___x_2039_ = lean_box(0);
v___y_1989_ = v_a_2000_;
v___y_1990_ = v___x_2034_;
v_a_1991_ = v___x_2039_;
goto v___jp_1988_;
}
else
{
lean_object* v_toConstantVal_2040_; lean_object* v_numParams_2041_; lean_object* v_all_2042_; lean_object* v_numNested_2043_; lean_object* v_type_2044_; lean_object* v___x_2045_; 
v_toConstantVal_2040_ = lean_ctor_get(v_val_2037_, 0);
lean_inc_ref(v_toConstantVal_2040_);
v_numParams_2041_ = lean_ctor_get(v_val_2037_, 1);
lean_inc(v_numParams_2041_);
v_all_2042_ = lean_ctor_get(v_val_2037_, 3);
lean_inc(v_all_2042_);
v_numNested_2043_ = lean_ctor_get(v_val_2037_, 5);
lean_inc(v_numNested_2043_);
lean_dec_ref(v_val_2037_);
v_type_2044_ = lean_ctor_get(v_toConstantVal_2040_, 2);
lean_inc_ref(v_type_2044_);
lean_dec_ref(v_toConstantVal_2040_);
v___x_2045_ = l_Lean_Meta_isPropFormerType(v_type_2044_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; uint8_t v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref(v___x_2045_);
v___x_2047_ = lean_unbox(v_a_2046_);
lean_dec(v_a_2046_);
if (v___x_2047_ == 0)
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_inc(v_indName_1857_);
v___x_2048_ = l_Lean_mkRecName(v_indName_1857_);
lean_inc(v_indName_1857_);
v___x_2049_ = l_Lean_mkBelowName(v_indName_1857_);
lean_inc(v___x_2049_);
lean_inc(v_numParams_2041_);
lean_inc(v___x_2048_);
v___x_2050_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec(v___x_2048_, v_numParams_2041_, v___x_2049_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
lean_dec_ref(v___x_2050_);
v___x_2051_ = lean_box(0);
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = l_List_get_x21Internal___redArg(v___x_2051_, v_all_2042_, v___x_2052_);
lean_dec(v_all_2042_);
v___x_2054_ = lean_name_eq(v___x_2053_, v_indName_1857_);
lean_dec(v_indName_1857_);
lean_dec(v___x_2053_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; 
lean_dec(v___x_2049_);
lean_dec(v___x_2048_);
lean_dec(v_numNested_2043_);
lean_dec(v_numParams_2041_);
v___x_2055_ = lean_box(0);
v___y_1989_ = v_a_2000_;
v___y_1990_ = v___x_2034_;
v_a_1991_ = v___x_2055_;
goto v___jp_1988_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_box(0);
v___x_2057_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_numNested_2043_, v___x_2048_, v___x_2049_, v_numParams_2041_, v___x_2052_, v___x_2056_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_);
lean_dec(v_numNested_2043_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_dec_ref(v___x_2057_);
v___y_1989_ = v_a_2000_;
v___y_1990_ = v___x_2034_;
v_a_1991_ = v___x_2056_;
goto v___jp_1988_;
}
else
{
lean_object* v_a_2058_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2057_);
v___y_1994_ = v_a_2000_;
v___y_1995_ = v___x_2034_;
v_a_1996_ = v_a_2058_;
goto v___jp_1993_;
}
}
}
else
{
lean_dec(v___x_2049_);
lean_dec(v___x_2048_);
lean_dec(v_numNested_2043_);
lean_dec(v_all_2042_);
lean_dec(v_numParams_2041_);
lean_dec(v_indName_1857_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2050_);
v___y_1989_ = v_a_2000_;
v___y_1990_ = v___x_2034_;
v_a_1991_ = v_a_2059_;
goto v___jp_1988_;
}
else
{
lean_object* v_a_2060_; 
v_a_2060_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2060_);
lean_dec_ref(v___x_2050_);
v___y_1994_ = v_a_2000_;
v___y_1995_ = v___x_2034_;
v_a_1996_ = v_a_2060_;
goto v___jp_1993_;
}
}
}
else
{
lean_object* v___x_2061_; 
lean_dec(v_numNested_2043_);
lean_dec(v_all_2042_);
lean_dec(v_numParams_2041_);
lean_dec(v_indName_1857_);
v___x_2061_ = lean_box(0);
v___y_1989_ = v_a_2000_;
v___y_1990_ = v___x_2034_;
v_a_1991_ = v___x_2061_;
goto v___jp_1988_;
}
}
else
{
lean_object* v_a_2062_; 
lean_dec(v_numNested_2043_);
lean_dec(v_all_2042_);
lean_dec(v_numParams_2041_);
lean_dec(v_indName_1857_);
v_a_2062_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2062_);
lean_dec_ref(v___x_2045_);
v___y_1994_ = v_a_2000_;
v___y_1995_ = v___x_2034_;
v_a_1996_ = v_a_2062_;
goto v___jp_1993_;
}
}
}
else
{
lean_object* v___x_2063_; 
lean_dec(v_a_2036_);
lean_dec(v_indName_1857_);
v___x_2063_ = lean_box(0);
v___y_1989_ = v_a_2000_;
v___y_1990_ = v___x_2034_;
v_a_1991_ = v___x_2063_;
goto v___jp_1988_;
}
}
else
{
lean_object* v_a_2064_; 
lean_dec(v_indName_1857_);
v_a_2064_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2035_);
v___y_1994_ = v_a_2000_;
v___y_1995_ = v___x_2034_;
v_a_1996_ = v_a_2064_;
goto v___jp_1993_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBelow___boxed(lean_object* v_indName_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l_Lean_mkBelow(v_indName_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(lean_object* v_upperBound_2150_, lean_object* v___x_2151_, lean_object* v___x_2152_, lean_object* v___x_2153_, lean_object* v_inst_2154_, lean_object* v_R_2155_, lean_object* v_a_2156_, lean_object* v_b_2157_, lean_object* v_c_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___redArg(v_upperBound_2150_, v___x_2151_, v___x_2152_, v___x_2153_, v_a_2156_, v_b_2157_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0___boxed(lean_object* v_upperBound_2165_, lean_object* v___x_2166_, lean_object* v___x_2167_, lean_object* v___x_2168_, lean_object* v_inst_2169_, lean_object* v_R_2170_, lean_object* v_a_2171_, lean_object* v_b_2172_, lean_object* v_c_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBelow_spec__0(v_upperBound_2165_, v___x_2166_, v___x_2167_, v___x_2168_, v_inst_2169_, v_R_2170_, v_a_2171_, v_b_2172_, v_c_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v_upperBound_2165_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6(lean_object* v_00_u03b1_2180_, lean_object* v_x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___redArg(v_x_2181_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4_spec__6(v_00_u03b1_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(lean_object* v_a_2196_, lean_object* v_a_2197_){
_start:
{
if (lean_obj_tag(v_a_2196_) == 0)
{
lean_object* v___x_2198_; 
v___x_2198_ = l_List_reverse___redArg(v_a_2197_);
return v___x_2198_;
}
else
{
lean_object* v_head_2199_; lean_object* v_tail_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2209_; 
v_head_2199_ = lean_ctor_get(v_a_2196_, 0);
v_tail_2200_ = lean_ctor_get(v_a_2196_, 1);
v_isSharedCheck_2209_ = !lean_is_exclusive(v_a_2196_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2202_ = v_a_2196_;
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_tail_2200_);
lean_inc(v_head_2199_);
lean_dec(v_a_2196_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2209_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2204_ = l_Lean_MessageData_ofExpr(v_head_2199_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 1, v_a_2197_);
lean_ctor_set(v___x_2202_, 0, v___x_2204_);
v___x_2206_ = v___x_2202_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_a_2197_);
v___x_2206_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
v_a_2196_ = v_tail_2200_;
v_a_2197_ = v___x_2206_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(lean_object* v_xs_2210_, lean_object* v_v_2211_, lean_object* v_i_2212_){
_start:
{
lean_object* v___x_2213_; uint8_t v___x_2214_; 
v___x_2213_ = lean_array_get_size(v_xs_2210_);
v___x_2214_ = lean_nat_dec_lt(v_i_2212_, v___x_2213_);
if (v___x_2214_ == 0)
{
lean_object* v___x_2215_; 
lean_dec(v_i_2212_);
v___x_2215_ = lean_box(0);
return v___x_2215_;
}
else
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_array_fget_borrowed(v_xs_2210_, v_i_2212_);
v___x_2217_ = lean_expr_eqv(v___x_2216_, v_v_2211_);
if (v___x_2217_ == 0)
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_add(v_i_2212_, v___x_2218_);
lean_dec(v_i_2212_);
v_i_2212_ = v___x_2219_;
goto _start;
}
else
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2221_, 0, v_i_2212_);
return v___x_2221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1___boxed(lean_object* v_xs_2222_, lean_object* v_v_2223_, lean_object* v_i_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2222_, v_v_2223_, v_i_2224_);
lean_dec_ref(v_v_2223_);
lean_dec_ref(v_xs_2222_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(lean_object* v_xs_2226_, lean_object* v_v_2227_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0_spec__1(v_xs_2226_, v_v_2227_, v___x_2228_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0___boxed(lean_object* v_xs_2230_, lean_object* v_v_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2230_, v_v_2231_);
lean_dec_ref(v_v_2231_);
lean_dec_ref(v_xs_2230_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(lean_object* v_xs_2233_, lean_object* v_v_2234_){
_start:
{
lean_object* v___x_2235_; 
v___x_2235_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0_spec__0(v_xs_2233_, v_v_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_box(0);
return v___x_2236_;
}
else
{
lean_object* v_val_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
v_val_2237_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2235_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_val_2237_);
lean_dec(v___x_2235_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_val_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0___boxed(lean_object* v_xs_2245_, lean_object* v_v_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_xs_2245_, v_v_2246_);
lean_dec_ref(v_v_2246_);
lean_dec_ref(v_xs_2245_);
return v_res_2247_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__0));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__2));
v___x_2253_ = l_Lean_stringToMessageData(v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(lean_object* v_rlvl_2254_, lean_object* v_prods_2255_, lean_object* v_motives_2256_, lean_object* v_fs_2257_, lean_object* v_minor__type_2258_, lean_object* v_x_2259_, lean_object* v_x_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
if (lean_obj_tag(v_x_2259_) == 5)
{
lean_object* v_fn_2267_; lean_object* v_arg_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_fn_2267_ = lean_ctor_get(v_x_2259_, 0);
lean_inc_ref(v_fn_2267_);
v_arg_2268_ = lean_ctor_get(v_x_2259_, 1);
lean_inc_ref(v_arg_2268_);
lean_dec_ref(v_x_2259_);
v___x_2269_ = lean_array_set(v_x_2260_, v_x_2261_, v_arg_2268_);
v___x_2270_ = lean_unsigned_to_nat(1u);
v___x_2271_ = lean_nat_sub(v_x_2261_, v___x_2270_);
lean_dec(v_x_2261_);
v_x_2259_ = v_fn_2267_;
v_x_2260_ = v___x_2269_;
v_x_2261_ = v___x_2271_;
goto _start;
}
else
{
lean_object* v___x_2273_; 
lean_dec(v_x_2261_);
v___x_2273_ = l_Lean_Meta_PProdN_mk(v_rlvl_2254_, v_prods_2255_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2256_, v_x_2259_);
lean_dec_ref(v_x_2259_);
if (lean_obj_tag(v___x_2275_) == 1)
{
lean_object* v_val_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_dec_ref(v_minor__type_2258_);
lean_dec_ref(v_motives_2256_);
v_val_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_val_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = l_Lean_instInhabitedExpr;
v___x_2278_ = lean_array_get_borrowed(v___x_2277_, v_fs_2257_, v_val_2276_);
lean_dec(v_val_2276_);
lean_inc(v_a_2274_);
v___x_2279_ = lean_array_push(v_x_2260_, v_a_2274_);
lean_inc(v___x_2278_);
v___x_2280_ = l_Lean_mkAppN(v___x_2278_, v___x_2279_);
lean_dec_ref(v___x_2279_);
v___x_2281_ = l_Lean_Meta_mkPProdMk(v___x_2280_, v_a_2274_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2281_;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v___x_2275_);
lean_dec(v_a_2274_);
lean_dec_ref(v_x_2260_);
v___x_2282_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__1);
v___x_2283_ = l_Lean_MessageData_ofExpr(v_minor__type_2258_);
v___x_2284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3, &l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___closed__3);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2284_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_array_to_list(v_motives_2256_);
v___x_2288_ = lean_box(0);
v___x_2289_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_2287_, v___x_2288_);
v___x_2290_ = l_Lean_MessageData_ofList(v___x_2289_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2286_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_2291_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2292_;
}
}
else
{
lean_dec_ref(v_x_2260_);
lean_dec_ref(v_x_2259_);
lean_dec_ref(v_minor__type_2258_);
lean_dec_ref(v_motives_2256_);
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2___boxed(lean_object* v_rlvl_2293_, lean_object* v_prods_2294_, lean_object* v_motives_2295_, lean_object* v_fs_2296_, lean_object* v_minor__type_2297_, lean_object* v_x_2298_, lean_object* v_x_2299_, lean_object* v_x_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2293_, v_prods_2294_, v_motives_2295_, v_fs_2296_, v_minor__type_2297_, v_x_2298_, v_x_2299_, v_x_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec_ref(v_fs_2296_);
return v_res_2306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2307_; lean_object* v_dummy_2308_; 
v___x_2307_ = lean_box(0);
v_dummy_2308_ = l_Lean_Expr_sort___override(v___x_2307_);
return v_dummy_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed(lean_object* v_motives_2309_, lean_object* v_head_2310_, lean_object* v_belows_2311_, lean_object* v_prods_2312_, lean_object* v_rlvl_2313_, lean_object* v_fs_2314_, lean_object* v_minor__type_2315_, lean_object* v_tail_2316_, lean_object* v_arg__args_2317_, lean_object* v_arg__type_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(v_motives_2309_, v_head_2310_, v_belows_2311_, v_prods_2312_, v_rlvl_2313_, v_fs_2314_, v_minor__type_2315_, v_tail_2316_, v_arg__args_2317_, v_arg__type_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec_ref(v_arg__args_2317_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(lean_object* v_rlvl_2325_, lean_object* v_motives_2326_, lean_object* v_belows_2327_, lean_object* v_fs_2328_, lean_object* v_minor__type_2329_, lean_object* v_prods_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
if (lean_obj_tag(v_a_2331_) == 0)
{
lean_object* v_dummy_2337_; lean_object* v_nargs_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec_ref(v_belows_2327_);
v_dummy_2337_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2338_ = l_Lean_Expr_getAppNumArgs(v_minor__type_2329_);
lean_inc(v_nargs_2338_);
v___x_2339_ = lean_mk_array(v_nargs_2338_, v_dummy_2337_);
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = lean_nat_sub(v_nargs_2338_, v___x_2340_);
lean_dec(v_nargs_2338_);
lean_inc_ref(v_minor__type_2329_);
v___x_2342_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__2(v_rlvl_2325_, v_prods_2330_, v_motives_2326_, v_fs_2328_, v_minor__type_2329_, v_minor__type_2329_, v___x_2339_, v___x_2341_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
lean_dec_ref(v_fs_2328_);
return v___x_2342_;
}
else
{
lean_object* v_head_2343_; lean_object* v_tail_2344_; lean_object* v___x_2345_; 
v_head_2343_ = lean_ctor_get(v_a_2331_, 0);
lean_inc(v_head_2343_);
v_tail_2344_ = lean_ctor_get(v_a_2331_, 1);
lean_inc(v_tail_2344_);
lean_dec_ref(v_a_2331_);
lean_inc(v_a_2335_);
lean_inc_ref(v_a_2334_);
lean_inc(v_a_2333_);
lean_inc_ref(v_a_2332_);
lean_inc(v_head_2343_);
v___x_2345_ = lean_infer_type(v_head_2343_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___f_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2345_);
v___f_2347_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___boxed), 15, 8);
lean_closure_set(v___f_2347_, 0, v_motives_2326_);
lean_closure_set(v___f_2347_, 1, v_head_2343_);
lean_closure_set(v___f_2347_, 2, v_belows_2327_);
lean_closure_set(v___f_2347_, 3, v_prods_2330_);
lean_closure_set(v___f_2347_, 4, v_rlvl_2325_);
lean_closure_set(v___f_2347_, 5, v_fs_2328_);
lean_closure_set(v___f_2347_, 6, v_minor__type_2329_);
lean_closure_set(v___f_2347_, 7, v_tail_2344_);
v___x_2348_ = 0;
v___x_2349_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2346_, v___f_2347_, v___x_2348_, v_a_2332_, v_a_2333_, v_a_2334_, v_a_2335_);
return v___x_2349_;
}
else
{
lean_dec(v_tail_2344_);
lean_dec(v_head_2343_);
lean_dec_ref(v_prods_2330_);
lean_dec_ref(v_minor__type_2329_);
lean_dec_ref(v_fs_2328_);
lean_dec_ref(v_belows_2327_);
lean_dec_ref(v_motives_2326_);
lean_dec(v_rlvl_2325_);
return v___x_2345_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(lean_object* v_prods_2350_, lean_object* v_rlvl_2351_, lean_object* v_motives_2352_, lean_object* v_belows_2353_, lean_object* v_fs_2354_, lean_object* v_minor__type_2355_, lean_object* v_tail_2356_, uint8_t v___x_2357_, uint8_t v___x_2358_, uint8_t v___x_2359_, lean_object* v_arg_x27_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_inc_ref(v_arg_x27_2360_);
v___x_2366_ = lean_array_push(v_prods_2350_, v_arg_x27_2360_);
v___x_2367_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2351_, v_motives_2352_, v_belows_2353_, v_fs_2354_, v_minor__type_2355_, v___x_2366_, v_tail_2356_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref(v___x_2367_);
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_mk_empty_array_with_capacity(v___x_2369_);
v___x_2371_ = lean_array_push(v___x_2370_, v_arg_x27_2360_);
v___x_2372_ = l_Lean_Meta_mkLambdaFVars(v___x_2371_, v_a_2368_, v___x_2357_, v___x_2358_, v___x_2357_, v___x_2358_, v___x_2359_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec_ref(v___x_2371_);
return v___x_2372_;
}
else
{
lean_dec_ref(v_arg_x27_2360_);
return v___x_2367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed(lean_object* v_prods_2373_, lean_object* v_rlvl_2374_, lean_object* v_motives_2375_, lean_object* v_belows_2376_, lean_object* v_fs_2377_, lean_object* v_minor__type_2378_, lean_object* v_tail_2379_, lean_object* v___x_2380_, lean_object* v___x_2381_, lean_object* v___x_2382_, lean_object* v_arg_x27_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
uint8_t v___x_1776__boxed_2389_; uint8_t v___x_1777__boxed_2390_; uint8_t v___x_1778__boxed_2391_; lean_object* v_res_2392_; 
v___x_1776__boxed_2389_ = lean_unbox(v___x_2380_);
v___x_1777__boxed_2390_ = lean_unbox(v___x_2381_);
v___x_1778__boxed_2391_ = lean_unbox(v___x_2382_);
v_res_2392_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0(v_prods_2373_, v_rlvl_2374_, v_motives_2375_, v_belows_2376_, v_fs_2377_, v_minor__type_2378_, v_tail_2379_, v___x_1776__boxed_2389_, v___x_1777__boxed_2390_, v___x_1778__boxed_2391_, v_arg_x27_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(lean_object* v_motives_2393_, lean_object* v_head_2394_, lean_object* v_belows_2395_, lean_object* v_arg__type_2396_, lean_object* v_prods_2397_, lean_object* v_rlvl_2398_, lean_object* v_fs_2399_, lean_object* v_minor__type_2400_, lean_object* v_tail_2401_, lean_object* v_arg__args_2402_, lean_object* v_x_2403_, lean_object* v_x_2404_, lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
if (lean_obj_tag(v_x_2403_) == 5)
{
lean_object* v_fn_2411_; lean_object* v_arg_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_fn_2411_ = lean_ctor_get(v_x_2403_, 0);
lean_inc_ref(v_fn_2411_);
v_arg_2412_ = lean_ctor_get(v_x_2403_, 1);
lean_inc_ref(v_arg_2412_);
lean_dec_ref(v_x_2403_);
v___x_2413_ = lean_array_set(v_x_2404_, v_x_2405_, v_arg_2412_);
v___x_2414_ = lean_unsigned_to_nat(1u);
v___x_2415_ = lean_nat_sub(v_x_2405_, v___x_2414_);
lean_dec(v_x_2405_);
v_x_2403_ = v_fn_2411_;
v_x_2404_ = v___x_2413_;
v_x_2405_ = v___x_2415_;
goto _start;
}
else
{
lean_object* v___x_2417_; 
lean_dec(v_x_2405_);
v___x_2417_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v_motives_2393_, v_x_2403_);
lean_dec_ref(v_x_2403_);
if (lean_obj_tag(v___x_2417_) == 1)
{
lean_object* v_val_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v_val_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_val_2418_);
lean_dec_ref(v___x_2417_);
v___x_2419_ = l_Lean_Expr_fvarId_x21(v_head_2394_);
lean_dec_ref(v_head_2394_);
v___x_2420_ = l_Lean_FVarId_getUserName___redArg(v___x_2419_, v___y_2406_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
v___x_2422_ = l_Lean_instInhabitedExpr;
v___x_2423_ = lean_array_get_borrowed(v___x_2422_, v_belows_2395_, v_val_2418_);
lean_dec(v_val_2418_);
lean_inc(v___x_2423_);
v___x_2424_ = l_Lean_mkAppN(v___x_2423_, v_x_2404_);
lean_dec_ref(v_x_2404_);
v___x_2425_ = l_Lean_Meta_mkPProd(v_arg__type_2396_, v___x_2424_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; uint8_t v___x_2427_; uint8_t v___x_2428_; uint8_t v___x_2429_; lean_object* v___x_2430_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = 0;
v___x_2428_ = 1;
v___x_2429_ = 1;
v___x_2430_ = l_Lean_Meta_mkForallFVars(v_arg__args_2402_, v_a_2426_, v___x_2427_, v___x_2428_, v___x_2428_, v___x_2429_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc(v_a_2431_);
lean_dec_ref(v___x_2430_);
v___x_2432_ = lean_box(v___x_2427_);
v___x_2433_ = lean_box(v___x_2428_);
v___x_2434_ = lean_box(v___x_2429_);
v___f_2435_ = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___lam__0___boxed), 16, 10);
lean_closure_set(v___f_2435_, 0, v_prods_2397_);
lean_closure_set(v___f_2435_, 1, v_rlvl_2398_);
lean_closure_set(v___f_2435_, 2, v_motives_2393_);
lean_closure_set(v___f_2435_, 3, v_belows_2395_);
lean_closure_set(v___f_2435_, 4, v_fs_2399_);
lean_closure_set(v___f_2435_, 5, v_minor__type_2400_);
lean_closure_set(v___f_2435_, 6, v_tail_2401_);
lean_closure_set(v___f_2435_, 7, v___x_2432_);
lean_closure_set(v___f_2435_, 8, v___x_2433_);
lean_closure_set(v___f_2435_, 9, v___x_2434_);
v___x_2436_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v_a_2421_, v_a_2431_, v___f_2435_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
return v___x_2436_;
}
else
{
lean_dec(v_a_2421_);
lean_dec(v_tail_2401_);
lean_dec_ref(v_minor__type_2400_);
lean_dec_ref(v_fs_2399_);
lean_dec(v_rlvl_2398_);
lean_dec_ref(v_prods_2397_);
lean_dec_ref(v_belows_2395_);
lean_dec_ref(v_motives_2393_);
return v___x_2430_;
}
}
else
{
lean_dec(v_a_2421_);
lean_dec(v_tail_2401_);
lean_dec_ref(v_minor__type_2400_);
lean_dec_ref(v_fs_2399_);
lean_dec(v_rlvl_2398_);
lean_dec_ref(v_prods_2397_);
lean_dec_ref(v_belows_2395_);
lean_dec_ref(v_motives_2393_);
return v___x_2425_;
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec(v_val_2418_);
lean_dec_ref(v_x_2404_);
lean_dec(v_tail_2401_);
lean_dec_ref(v_minor__type_2400_);
lean_dec_ref(v_fs_2399_);
lean_dec(v_rlvl_2398_);
lean_dec_ref(v_prods_2397_);
lean_dec_ref(v_arg__type_2396_);
lean_dec_ref(v_belows_2395_);
lean_dec_ref(v_motives_2393_);
v_a_2437_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2420_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2420_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_object* v___x_2445_; 
lean_dec(v___x_2417_);
lean_dec_ref(v_x_2404_);
lean_dec_ref(v_arg__type_2396_);
v___x_2445_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2398_, v_motives_2393_, v_belows_2395_, v_fs_2399_, v_minor__type_2400_, v_prods_2397_, v_tail_2401_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; uint8_t v___x_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref(v___x_2445_);
v___x_2447_ = lean_unsigned_to_nat(1u);
v___x_2448_ = lean_mk_empty_array_with_capacity(v___x_2447_);
v___x_2449_ = lean_array_push(v___x_2448_, v_head_2394_);
v___x_2450_ = 0;
v___x_2451_ = 1;
v___x_2452_ = 1;
v___x_2453_ = l_Lean_Meta_mkLambdaFVars(v___x_2449_, v_a_2446_, v___x_2450_, v___x_2451_, v___x_2450_, v___x_2451_, v___x_2452_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec_ref(v___x_2449_);
return v___x_2453_;
}
else
{
lean_dec_ref(v_head_2394_);
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0(lean_object* v_motives_2454_, lean_object* v_head_2455_, lean_object* v_belows_2456_, lean_object* v_prods_2457_, lean_object* v_rlvl_2458_, lean_object* v_fs_2459_, lean_object* v_minor__type_2460_, lean_object* v_tail_2461_, lean_object* v_arg__args_2462_, lean_object* v_arg__type_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
lean_object* v_dummy_2469_; lean_object* v_nargs_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_dummy_2469_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___lam__0___closed__0);
v_nargs_2470_ = l_Lean_Expr_getAppNumArgs(v_arg__type_2463_);
lean_inc(v_nargs_2470_);
v___x_2471_ = lean_mk_array(v_nargs_2470_, v_dummy_2469_);
v___x_2472_ = lean_unsigned_to_nat(1u);
v___x_2473_ = lean_nat_sub(v_nargs_2470_, v___x_2472_);
lean_dec(v_nargs_2470_);
lean_inc_ref(v_arg__type_2463_);
v___x_2474_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2454_, v_head_2455_, v_belows_2456_, v_arg__type_2463_, v_prods_2457_, v_rlvl_2458_, v_fs_2459_, v_minor__type_2460_, v_tail_2461_, v_arg__args_2462_, v_arg__type_2463_, v___x_2471_, v___x_2473_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go___boxed(lean_object* v_rlvl_2475_, lean_object* v_motives_2476_, lean_object* v_belows_2477_, lean_object* v_fs_2478_, lean_object* v_minor__type_2479_, lean_object* v_prods_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2475_, v_motives_2476_, v_belows_2477_, v_fs_2478_, v_minor__type_2479_, v_prods_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
lean_dec(v_a_2483_);
lean_dec_ref(v_a_2482_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3___boxed(lean_object** _args){
lean_object* v_motives_2488_ = _args[0];
lean_object* v_head_2489_ = _args[1];
lean_object* v_belows_2490_ = _args[2];
lean_object* v_arg__type_2491_ = _args[3];
lean_object* v_prods_2492_ = _args[4];
lean_object* v_rlvl_2493_ = _args[5];
lean_object* v_fs_2494_ = _args[6];
lean_object* v_minor__type_2495_ = _args[7];
lean_object* v_tail_2496_ = _args[8];
lean_object* v_arg__args_2497_ = _args[9];
lean_object* v_x_2498_ = _args[10];
lean_object* v_x_2499_ = _args[11];
lean_object* v_x_2500_ = _args[12];
lean_object* v___y_2501_ = _args[13];
lean_object* v___y_2502_ = _args[14];
lean_object* v___y_2503_ = _args[15];
lean_object* v___y_2504_ = _args[16];
lean_object* v___y_2505_ = _args[17];
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__3(v_motives_2488_, v_head_2489_, v_belows_2490_, v_arg__type_2491_, v_prods_2492_, v_rlvl_2493_, v_fs_2494_, v_minor__type_2495_, v_tail_2496_, v_arg__args_2497_, v_x_2498_, v_x_2499_, v_x_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec_ref(v_arg__args_2497_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(lean_object* v_rlvl_2507_, lean_object* v_motives_2508_, lean_object* v_belows_2509_, lean_object* v_fs_2510_, lean_object* v_minor__args_2511_, lean_object* v_minor__type_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2518_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_2519_ = lean_array_to_list(v_minor__args_2511_);
v___x_2520_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go(v_rlvl_2507_, v_motives_2508_, v_belows_2509_, v_fs_2510_, v_minor__type_2512_, v___x_2518_, v___x_2519_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed(lean_object* v_rlvl_2521_, lean_object* v_motives_2522_, lean_object* v_belows_2523_, lean_object* v_fs_2524_, lean_object* v_minor__args_2525_, lean_object* v_minor__type_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0(v_rlvl_2521_, v_motives_2522_, v_belows_2523_, v_fs_2524_, v_minor__args_2525_, v_minor__type_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(lean_object* v_rlvl_2533_, lean_object* v_motives_2534_, lean_object* v_belows_2535_, lean_object* v_fs_2536_, lean_object* v_minorType_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___f_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; 
v___f_2543_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___lam__0___boxed), 11, 4);
lean_closure_set(v___f_2543_, 0, v_rlvl_2533_);
lean_closure_set(v___f_2543_, 1, v_motives_2534_);
lean_closure_set(v___f_2543_, 2, v_belows_2535_);
lean_closure_set(v___f_2543_, 3, v_fs_2536_);
v___x_2544_ = 0;
v___x_2545_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_minorType_2537_, v___f_2543_, v___x_2544_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise___boxed(lean_object* v_rlvl_2546_, lean_object* v_motives_2547_, lean_object* v_belows_2548_, lean_object* v_fs_2549_, lean_object* v_minorType_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v_rlvl_2546_, v_motives_2547_, v_belows_2548_, v_fs_2549_, v_minorType_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(lean_object* v_msg_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___f_2563_; lean_object* v___x_27349__overap_2564_; lean_object* v___x_2565_; 
v___f_2563_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__2___closed__0));
v___x_27349__overap_2564_ = lean_panic_fn(v___f_2563_, v_msg_2557_);
lean_inc(v___y_2561_);
lean_inc_ref(v___y_2560_);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
v___x_2565_ = lean_apply_5(v___x_27349__overap_2564_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_, lean_box(0));
return v___x_2565_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0___boxed(lean_object* v_msg_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v_msg_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(lean_object* v_e_2573_, lean_object* v___y_2574_){
_start:
{
uint8_t v___x_2576_; 
v___x_2576_ = l_Lean_Expr_hasMVar(v_e_2573_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2577_, 0, v_e_2573_);
return v___x_2577_;
}
else
{
lean_object* v___x_2578_; lean_object* v_mctx_2579_; lean_object* v___x_2580_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; lean_object* v___x_2583_; lean_object* v_cache_2584_; lean_object* v_zetaDeltaFVarIds_2585_; lean_object* v_postponed_2586_; lean_object* v_diag_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2596_; 
v___x_2578_ = lean_st_ref_get(v___y_2574_);
v_mctx_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc_ref(v_mctx_2579_);
lean_dec(v___x_2578_);
v___x_2580_ = l_Lean_instantiateMVarsCore(v_mctx_2579_, v_e_2573_);
v_fst_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_fst_2581_);
v_snd_2582_ = lean_ctor_get(v___x_2580_, 1);
lean_inc(v_snd_2582_);
lean_dec_ref(v___x_2580_);
v___x_2583_ = lean_st_ref_take(v___y_2574_);
v_cache_2584_ = lean_ctor_get(v___x_2583_, 1);
v_zetaDeltaFVarIds_2585_ = lean_ctor_get(v___x_2583_, 2);
v_postponed_2586_ = lean_ctor_get(v___x_2583_, 3);
v_diag_2587_ = lean_ctor_get(v___x_2583_, 4);
v_isSharedCheck_2596_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v___x_2583_, 0);
lean_dec(v_unused_2597_);
v___x_2589_ = v___x_2583_;
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_diag_2587_);
lean_inc(v_postponed_2586_);
lean_inc(v_zetaDeltaFVarIds_2585_);
lean_inc(v_cache_2584_);
lean_dec(v___x_2583_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2596_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 0, v_snd_2582_);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_snd_2582_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_cache_2584_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v_zetaDeltaFVarIds_2585_);
lean_ctor_set(v_reuseFailAlloc_2595_, 3, v_postponed_2586_);
lean_ctor_set(v_reuseFailAlloc_2595_, 4, v_diag_2587_);
v___x_2592_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_st_ref_set(v___y_2574_, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_fst_2581_);
return v___x_2594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg___boxed(lean_object* v_e_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2598_, v___y_2599_);
lean_dec(v___y_2599_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(lean_object* v_e_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_){
_start:
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_e_2602_, v___y_2604_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___boxed(lean_object* v_e_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5(v_e_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(lean_object* v_thm_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; lean_object* v_env_2620_; lean_object* v_toConstantVal_2621_; lean_object* v_value_2622_; lean_object* v_all_2623_; uint8_t v___y_2625_; lean_object* v_type_2633_; uint8_t v___x_2634_; 
v___x_2619_ = lean_st_ref_get(v___y_2617_);
v_env_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc_ref(v_env_2620_);
lean_dec(v___x_2619_);
v_toConstantVal_2621_ = lean_ctor_get(v_thm_2616_, 0);
v_value_2622_ = lean_ctor_get(v_thm_2616_, 1);
v_all_2623_ = lean_ctor_get(v_thm_2616_, 2);
v_type_2633_ = lean_ctor_get(v_toConstantVal_2621_, 2);
lean_inc_ref(v_env_2620_);
v___x_2634_ = l_Lean_Environment_hasUnsafe(v_env_2620_, v_type_2633_);
if (v___x_2634_ == 0)
{
uint8_t v___x_2635_; 
v___x_2635_ = l_Lean_Environment_hasUnsafe(v_env_2620_, v_value_2622_);
v___y_2625_ = v___x_2635_;
goto v___jp_2624_;
}
else
{
lean_dec_ref(v_env_2620_);
v___y_2625_ = v___x_2634_;
goto v___jp_2624_;
}
v___jp_2624_:
{
if (v___y_2625_ == 0)
{
lean_object* v___x_2626_; lean_object* v___x_2627_; 
v___x_2626_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_thm_2616_);
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
return v___x_2627_;
}
else
{
lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_inc(v_all_2623_);
lean_inc_ref(v_value_2622_);
lean_inc_ref(v_toConstantVal_2621_);
lean_dec_ref(v_thm_2616_);
v___x_2628_ = lean_box(0);
v___x_2629_ = 0;
v___x_2630_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2630_, 0, v_toConstantVal_2621_);
lean_ctor_set(v___x_2630_, 1, v_value_2622_);
lean_ctor_set(v___x_2630_, 2, v___x_2628_);
lean_ctor_set(v___x_2630_, 3, v_all_2623_);
lean_ctor_set_uint8(v___x_2630_, sizeof(void*)*4, v___x_2629_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg___boxed(lean_object* v_thm_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2636_, v___y_2637_);
lean_dec(v___y_2637_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(lean_object* v_thm_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v_thm_2640_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___boxed(lean_object* v_thm_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6(v_thm_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(lean_object* v___x_2655_, lean_object* v___x_2656_, lean_object* v___x_2657_, lean_object* v_all_2658_, lean_object* v___x_2659_, lean_object* v___x_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v___y_2663_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = lean_array_get_size(v_all_2658_);
v___x_2668_ = lean_nat_dec_lt(v_x_2661_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2669_ = lean_box(0);
v___x_2670_ = lean_array_get_borrowed(v___x_2669_, v_all_2658_, v___x_2659_);
v___x_2671_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___closed__0));
v___x_2672_ = lean_nat_sub(v_x_2661_, v___x_2667_);
v___x_2673_ = lean_nat_add(v___x_2672_, v___x_2660_);
lean_dec(v___x_2672_);
v___x_2674_ = l_Nat_reprFast(v___x_2673_);
v___x_2675_ = lean_string_append(v___x_2671_, v___x_2674_);
lean_dec_ref(v___x_2674_);
lean_inc(v___x_2670_);
v___x_2676_ = l_Lean_Name_str___override(v___x_2670_, v___x_2675_);
v___y_2663_ = v___x_2676_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_array_fget_borrowed(v_all_2658_, v_x_2661_);
lean_inc(v___x_2677_);
v___x_2678_ = l_Lean_mkBelowName(v___x_2677_);
v___y_2663_ = v___x_2678_;
goto v___jp_2662_;
}
v___jp_2662_:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2664_ = l_Lean_Expr_const___override(v___y_2663_, v___x_2655_);
v___x_2665_ = l_Array_append___redArg(v___x_2656_, v___x_2657_);
v___x_2666_ = l_Lean_mkAppN(v___x_2664_, v___x_2665_);
lean_dec_ref(v___x_2665_);
return v___x_2666_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed(lean_object* v___x_2679_, lean_object* v___x_2680_, lean_object* v___x_2681_, lean_object* v_all_2682_, lean_object* v___x_2683_, lean_object* v___x_2684_, lean_object* v_x_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0(v___x_2679_, v___x_2680_, v___x_2681_, v_all_2682_, v___x_2683_, v___x_2684_, v_x_2685_);
lean_dec(v_x_2685_);
lean_dec(v___x_2684_);
lean_dec(v___x_2683_);
lean_dec_ref(v_all_2682_);
lean_dec_ref(v___x_2681_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(lean_object* v_a_2687_, lean_object* v___x_2688_, uint8_t v___x_2689_, lean_object* v_targs_2690_, lean_object* v_x_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = l_Lean_mkAppN(v_a_2687_, v_targs_2690_);
v___x_2698_ = l_Lean_mkAppN(v___x_2688_, v_targs_2690_);
v___x_2699_ = l_Lean_Meta_mkPProd(v___x_2697_, v___x_2698_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; uint8_t v___x_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
v___x_2701_ = 0;
v___x_2702_ = 1;
v___x_2703_ = l_Lean_Meta_mkLambdaFVars(v_targs_2690_, v_a_2700_, v___x_2701_, v___x_2689_, v___x_2701_, v___x_2689_, v___x_2702_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v___x_2703_;
}
else
{
return v___x_2699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed(lean_object* v_a_2704_, lean_object* v___x_2705_, lean_object* v___x_2706_, lean_object* v_targs_2707_, lean_object* v_x_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
uint8_t v___x_30548__boxed_2714_; lean_object* v_res_2715_; 
v___x_30548__boxed_2714_ = lean_unbox(v___x_2706_);
v_res_2715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0(v_a_2704_, v___x_2705_, v___x_30548__boxed_2714_, v_targs_2707_, v_x_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec_ref(v_x_2708_);
lean_dec_ref(v_targs_2707_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(lean_object* v_as_2716_, size_t v_sz_2717_, size_t v_i_2718_, lean_object* v_b_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
uint8_t v___x_2725_; 
v___x_2725_ = lean_usize_dec_lt(v_i_2718_, v_sz_2717_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_b_2719_);
return v___x_2726_;
}
else
{
lean_object* v_snd_2727_; lean_object* v_fst_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2784_; 
v_snd_2727_ = lean_ctor_get(v_b_2719_, 1);
v_fst_2728_ = lean_ctor_get(v_b_2719_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_b_2719_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2730_ = v_b_2719_;
v_isShared_2731_ = v_isSharedCheck_2784_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_snd_2727_);
lean_inc(v_fst_2728_);
lean_dec(v_b_2719_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2784_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v_array_2732_; lean_object* v_start_2733_; lean_object* v_stop_2734_; uint8_t v___x_2735_; 
v_array_2732_ = lean_ctor_get(v_snd_2727_, 0);
v_start_2733_ = lean_ctor_get(v_snd_2727_, 1);
v_stop_2734_ = lean_ctor_get(v_snd_2727_, 2);
v___x_2735_ = lean_nat_dec_lt(v_start_2733_, v_stop_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2737_; 
if (v_isShared_2731_ == 0)
{
v___x_2737_ = v___x_2730_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_fst_2728_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_snd_2727_);
v___x_2737_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
return v___x_2738_;
}
}
else
{
lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2780_; 
lean_inc(v_stop_2734_);
lean_inc(v_start_2733_);
lean_inc_ref(v_array_2732_);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_snd_2727_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; lean_object* v_unused_2782_; lean_object* v_unused_2783_; 
v_unused_2781_ = lean_ctor_get(v_snd_2727_, 2);
lean_dec(v_unused_2781_);
v_unused_2782_ = lean_ctor_get(v_snd_2727_, 1);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_snd_2727_, 0);
lean_dec(v_unused_2783_);
v___x_2741_ = v_snd_2727_;
v_isShared_2742_ = v_isSharedCheck_2780_;
goto v_resetjp_2740_;
}
else
{
lean_dec(v_snd_2727_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2780_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_a_2743_; lean_object* v___x_2744_; 
v_a_2743_ = lean_array_uget_borrowed(v_as_2716_, v_i_2718_);
lean_inc(v___y_2723_);
lean_inc_ref(v___y_2722_);
lean_inc(v___y_2721_);
lean_inc_ref(v___y_2720_);
lean_inc(v_a_2743_);
v___x_2744_ = lean_infer_type(v_a_2743_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___f_2748_; uint8_t v___x_2749_; lean_object* v___x_2750_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = lean_array_fget_borrowed(v_array_2732_, v_start_2733_);
v___x_2747_ = lean_box(v___x_2735_);
lean_inc(v___x_2746_);
lean_inc(v_a_2743_);
v___f_2748_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2748_, 0, v_a_2743_);
lean_closure_set(v___f_2748_, 1, v___x_2746_);
lean_closure_set(v___f_2748_, 2, v___x_2747_);
v___x_2749_ = 0;
v___x_2750_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_2745_, v___f_2748_, v___x_2749_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = lean_unsigned_to_nat(1u);
v___x_2753_ = lean_nat_add(v_start_2733_, v___x_2752_);
lean_dec(v_start_2733_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 1, v___x_2753_);
v___x_2755_ = v___x_2741_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_array_2732_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v_stop_2734_);
v___x_2755_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_Expr_app___override(v_fst_2728_, v_a_2751_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 1, v___x_2755_);
lean_ctor_set(v___x_2730_, 0, v___x_2756_);
v___x_2758_ = v___x_2730_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2756_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2755_);
v___x_2758_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
size_t v___x_2759_; size_t v___x_2760_; 
v___x_2759_ = ((size_t)1ULL);
v___x_2760_ = lean_usize_add(v_i_2718_, v___x_2759_);
v_i_2718_ = v___x_2760_;
v_b_2719_ = v___x_2758_;
goto _start;
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_del_object(v___x_2741_);
lean_dec(v_stop_2734_);
lean_dec(v_start_2733_);
lean_dec_ref(v_array_2732_);
lean_del_object(v___x_2730_);
lean_dec(v_fst_2728_);
v_a_2764_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2750_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2750_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_del_object(v___x_2741_);
lean_dec(v_stop_2734_);
lean_dec(v_start_2733_);
lean_dec_ref(v_array_2732_);
lean_del_object(v___x_2730_);
lean_dec(v_fst_2728_);
v_a_2772_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2744_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2744_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2___boxed(lean_object* v_as_2785_, lean_object* v_sz_2786_, lean_object* v_i_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
size_t v_sz_boxed_2794_; size_t v_i_boxed_2795_; lean_object* v_res_2796_; 
v_sz_boxed_2794_ = lean_unbox_usize(v_sz_2786_);
lean_dec(v_sz_2786_);
v_i_boxed_2795_ = lean_unbox_usize(v_i_2787_);
lean_dec(v_i_2787_);
v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v_as_2785_, v_sz_boxed_2794_, v_i_boxed_2795_, v_b_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec_ref(v_as_2785_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(lean_object* v_as_2797_, size_t v_sz_2798_, size_t v_i_2799_, lean_object* v_b_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
uint8_t v___x_2806_; 
v___x_2806_ = lean_usize_dec_lt(v_i_2799_, v_sz_2798_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v_b_2800_);
return v___x_2807_;
}
else
{
lean_object* v_a_2808_; lean_object* v_toInductionSubgoal_2809_; lean_object* v_mvarId_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; 
v_a_2808_ = lean_array_uget_borrowed(v_as_2797_, v_i_2799_);
v_toInductionSubgoal_2809_ = lean_ctor_get(v_a_2808_, 0);
v_mvarId_2810_ = lean_ctor_get(v_toInductionSubgoal_2809_, 0);
v___x_2811_ = 0;
lean_inc(v_mvarId_2810_);
v___x_2812_ = l_Lean_MVarId_refl(v_mvarId_2810_, v___x_2811_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2813_; size_t v___x_2814_; size_t v___x_2815_; 
lean_dec_ref(v___x_2812_);
v___x_2813_ = lean_box(0);
v___x_2814_ = ((size_t)1ULL);
v___x_2815_ = lean_usize_add(v_i_2799_, v___x_2814_);
v_i_2799_ = v___x_2815_;
v_b_2800_ = v___x_2813_;
goto _start;
}
else
{
return v___x_2812_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4___boxed(lean_object* v_as_2817_, lean_object* v_sz_2818_, lean_object* v_i_2819_, lean_object* v_b_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_){
_start:
{
size_t v_sz_boxed_2826_; size_t v_i_boxed_2827_; lean_object* v_res_2828_; 
v_sz_boxed_2826_ = lean_unbox_usize(v_sz_2818_);
lean_dec(v_sz_2818_);
v_i_boxed_2827_ = lean_unbox_usize(v_i_2819_);
lean_dec(v_i_2819_);
v_res_2828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_as_2817_, v_sz_boxed_2826_, v_i_boxed_2827_, v_b_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec_ref(v_as_2817_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(lean_object* v___x_2829_, lean_object* v___x_2830_, lean_object* v___x_2831_, lean_object* v_fs_2832_, lean_object* v_as_2833_, size_t v_sz_2834_, size_t v_i_2835_, lean_object* v_b_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
uint8_t v___x_2842_; 
v___x_2842_ = lean_usize_dec_lt(v_i_2835_, v_sz_2834_);
if (v___x_2842_ == 0)
{
lean_object* v___x_2843_; 
lean_dec_ref(v_fs_2832_);
lean_dec_ref(v___x_2831_);
lean_dec_ref(v___x_2830_);
lean_dec(v___x_2829_);
v___x_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2843_, 0, v_b_2836_);
return v___x_2843_;
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2845_; 
v_a_2844_ = lean_array_uget_borrowed(v_as_2833_, v_i_2835_);
lean_inc(v___y_2840_);
lean_inc_ref(v___y_2839_);
lean_inc(v___y_2838_);
lean_inc_ref(v___y_2837_);
lean_inc(v_a_2844_);
v___x_2845_ = lean_infer_type(v_a_2844_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v_a_2846_; lean_object* v___x_2847_; 
v_a_2846_ = lean_ctor_get(v___x_2845_, 0);
lean_inc(v_a_2846_);
lean_dec_ref(v___x_2845_);
lean_inc_ref(v_fs_2832_);
lean_inc_ref(v___x_2831_);
lean_inc_ref(v___x_2830_);
lean_inc(v___x_2829_);
v___x_2847_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise(v___x_2829_, v___x_2830_, v___x_2831_, v_fs_2832_, v_a_2846_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2849_; size_t v___x_2850_; size_t v___x_2851_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref(v___x_2847_);
v___x_2849_ = l_Lean_Expr_app___override(v_b_2836_, v_a_2848_);
v___x_2850_ = ((size_t)1ULL);
v___x_2851_ = lean_usize_add(v_i_2835_, v___x_2850_);
v_i_2835_ = v___x_2851_;
v_b_2836_ = v___x_2849_;
goto _start;
}
else
{
lean_dec_ref(v_b_2836_);
lean_dec_ref(v_fs_2832_);
lean_dec_ref(v___x_2831_);
lean_dec_ref(v___x_2830_);
lean_dec(v___x_2829_);
return v___x_2847_;
}
}
else
{
lean_dec_ref(v_b_2836_);
lean_dec_ref(v_fs_2832_);
lean_dec_ref(v___x_2831_);
lean_dec_ref(v___x_2830_);
lean_dec(v___x_2829_);
return v___x_2845_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3___boxed(lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v___x_2855_, lean_object* v_fs_2856_, lean_object* v_as_2857_, lean_object* v_sz_2858_, lean_object* v_i_2859_, lean_object* v_b_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
size_t v_sz_boxed_2866_; size_t v_i_boxed_2867_; lean_object* v_res_2868_; 
v_sz_boxed_2866_ = lean_unbox_usize(v_sz_2858_);
lean_dec(v_sz_2858_);
v_i_boxed_2867_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_res_2868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2853_, v___x_2854_, v___x_2855_, v_fs_2856_, v_as_2857_, v_sz_boxed_2866_, v_i_boxed_2867_, v_b_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v_as_2857_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(lean_object* v___x_2869_, lean_object* v_tail_2870_, lean_object* v_recName_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, size_t v_sz_2875_, size_t v___x_2876_, lean_object* v___x_2877_, lean_object* v___x_2878_, lean_object* v___x_2879_, lean_object* v___x_2880_, lean_object* v___x_2881_, lean_object* v___x_2882_, lean_object* v_val_2883_, uint8_t v___x_2884_, lean_object* v_brecOnGoName_2885_, lean_object* v_levelParams_2886_, lean_object* v___x_2887_, lean_object* v_brecOnName_2888_, lean_object* v___x_2889_, lean_object* v_brecOnEqName_2890_, lean_object* v_fs_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_inc(v___x_2869_);
v___x_2897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2869_);
lean_ctor_set(v___x_2897_, 1, v_tail_2870_);
v___x_2898_ = l_Lean_Expr_const___override(v_recName_2871_, v___x_2897_);
v___x_2899_ = l_Lean_mkAppN(v___x_2898_, v___x_2872_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2873_);
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__2(v___x_2874_, v_sz_2875_, v___x_2876_, v___x_2900_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v_fst_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_3264_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
v_fst_2903_ = lean_ctor_get(v_a_2902_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_a_2902_);
if (v_isSharedCheck_3264_ == 0)
{
lean_object* v_unused_3265_; 
v_unused_3265_ = lean_ctor_get(v_a_2902_, 1);
lean_dec(v_unused_3265_);
v___x_2905_ = v_a_2902_;
v_isShared_2906_ = v_isSharedCheck_3264_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_fst_2903_);
lean_dec(v_a_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_3264_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
size_t v_sz_2907_; lean_object* v___x_2908_; 
v_sz_2907_ = lean_array_size(v___x_2877_);
lean_inc_ref(v_fs_2891_);
lean_inc_ref(v___x_2878_);
lean_inc_ref(v___x_2874_);
v___x_2908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__3(v___x_2869_, v___x_2874_, v___x_2878_, v_fs_2891_, v___x_2877_, v_sz_2907_, v___x_2876_, v_fst_2903_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref(v___x_2908_);
v___x_2910_ = l_Lean_mkAppN(v_a_2909_, v___x_2879_);
lean_inc_ref(v___x_2880_);
v___x_2911_ = l_Lean_Expr_app___override(v___x_2910_, v___x_2880_);
v___x_2912_ = l_Array_append___redArg(v___x_2872_, v___x_2874_);
v___x_2913_ = l_Array_append___redArg(v___x_2912_, v___x_2879_);
v___x_2914_ = lean_mk_empty_array_with_capacity(v___x_2881_);
lean_inc_ref(v___x_2880_);
v___x_2915_ = lean_array_push(v___x_2914_, v___x_2880_);
lean_inc_ref(v___x_2882_);
v___x_2916_ = lean_array_get(v___x_2882_, v___x_2874_, v_val_2883_);
lean_dec_ref(v___x_2874_);
lean_inc_ref(v___x_2880_);
v___x_2917_ = lean_array_push(v___x_2879_, v___x_2880_);
v___x_2918_ = l_Lean_mkAppN(v___x_2916_, v___x_2917_);
lean_inc_ref(v___x_2882_);
v___x_2919_ = lean_array_get(v___x_2882_, v___x_2878_, v_val_2883_);
lean_dec_ref(v___x_2878_);
v___x_2920_ = l_Lean_mkAppN(v___x_2919_, v___x_2917_);
lean_inc_ref(v___x_2918_);
v___x_2921_ = l_Lean_Meta_mkPProd(v___x_2918_, v___x_2920_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref(v___x_2921_);
v___x_2923_ = l_Array_append___redArg(v___x_2913_, v___x_2915_);
lean_dec_ref(v___x_2915_);
v___x_2924_ = l_Array_append___redArg(v___x_2923_, v_fs_2891_);
v___x_2925_ = 0;
v___x_2926_ = 1;
v___x_2927_ = l_Lean_Meta_mkForallFVars(v___x_2924_, v_a_2922_, v___x_2925_, v___x_2884_, v___x_2884_, v___x_2926_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2929_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref(v___x_2927_);
v___x_2929_ = l_Lean_Meta_mkLambdaFVars(v___x_2924_, v___x_2911_, v___x_2925_, v___x_2884_, v___x_2925_, v___x_2884_, v___x_2926_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_3231_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2929_);
v___x_2931_ = lean_box(1);
lean_inc(v_levelParams_2886_);
lean_inc(v_brecOnGoName_2885_);
v___x_2932_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnGoName_2885_, v_levelParams_2886_, v_a_2928_, v_a_2930_, v___x_2931_, v___y_2895_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_3231_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_3231_;
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
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_3230_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Lean_addDecl(v___x_2938_, v___x_2925_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_toConstantVal_2940_; lean_object* v_name_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_3227_; 
lean_dec_ref(v___x_2939_);
v_toConstantVal_2940_ = lean_ctor_get(v_a_2933_, 0);
lean_inc_ref(v_toConstantVal_2940_);
lean_dec(v_a_2933_);
v_name_2941_ = lean_ctor_get(v_toConstantVal_2940_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v_toConstantVal_2940_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; lean_object* v_unused_3229_; 
v_unused_3228_ = lean_ctor_get(v_toConstantVal_2940_, 2);
lean_dec(v_unused_3228_);
v_unused_3229_ = lean_ctor_get(v_toConstantVal_2940_, 1);
lean_dec(v_unused_3229_);
v___x_2943_ = v_toConstantVal_2940_;
v_isShared_2944_ = v_isSharedCheck_3227_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_name_2941_);
lean_dec(v_toConstantVal_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_3227_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v_env_2947_; lean_object* v_nextMacroScope_2948_; lean_object* v_ngen_2949_; lean_object* v_auxDeclNGen_2950_; lean_object* v_traceState_2951_; lean_object* v_messages_2952_; lean_object* v_infoState_2953_; lean_object* v_snapshotTasks_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_3225_; 
lean_inc(v_name_2941_);
v___x_2945_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2941_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec_ref(v___x_2945_);
v___x_2946_ = lean_st_ref_take(v___y_2895_);
v_env_2947_ = lean_ctor_get(v___x_2946_, 0);
v_nextMacroScope_2948_ = lean_ctor_get(v___x_2946_, 1);
v_ngen_2949_ = lean_ctor_get(v___x_2946_, 2);
v_auxDeclNGen_2950_ = lean_ctor_get(v___x_2946_, 3);
v_traceState_2951_ = lean_ctor_get(v___x_2946_, 4);
v_messages_2952_ = lean_ctor_get(v___x_2946_, 6);
v_infoState_2953_ = lean_ctor_get(v___x_2946_, 7);
v_snapshotTasks_2954_ = lean_ctor_get(v___x_2946_, 8);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_3225_ == 0)
{
lean_object* v_unused_3226_; 
v_unused_3226_ = lean_ctor_get(v___x_2946_, 5);
lean_dec(v_unused_3226_);
v___x_2956_ = v___x_2946_;
v_isShared_2957_ = v_isSharedCheck_3225_;
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
v_isShared_2957_ = v_isSharedCheck_3225_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2958_ = l_Lean_addProtected(v_env_2947_, v_name_2941_);
v___x_2959_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__2);
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 5, v___x_2959_);
lean_ctor_set(v___x_2956_, 0, v___x_2958_);
v___x_2961_ = v___x_2956_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_nextMacroScope_2948_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_ngen_2949_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_auxDeclNGen_2950_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_traceState_2951_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v_messages_2952_);
lean_ctor_set(v_reuseFailAlloc_3224_, 7, v_infoState_2953_);
lean_ctor_set(v_reuseFailAlloc_3224_, 8, v_snapshotTasks_2954_);
v___x_2961_ = v_reuseFailAlloc_3224_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v_mctx_2964_; lean_object* v_zetaDeltaFVarIds_2965_; lean_object* v_postponed_2966_; lean_object* v_diag_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3222_; 
v___x_2962_ = lean_st_ref_set(v___y_2895_, v___x_2961_);
v___x_2963_ = lean_st_ref_take(v___y_2893_);
v_mctx_2964_ = lean_ctor_get(v___x_2963_, 0);
v_zetaDeltaFVarIds_2965_ = lean_ctor_get(v___x_2963_, 2);
v_postponed_2966_ = lean_ctor_get(v___x_2963_, 3);
v_diag_2967_ = lean_ctor_get(v___x_2963_, 4);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; 
v_unused_3223_ = lean_ctor_get(v___x_2963_, 1);
lean_dec(v_unused_3223_);
v___x_2969_ = v___x_2963_;
v_isShared_2970_ = v_isSharedCheck_3222_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_diag_2967_);
lean_inc(v_postponed_2966_);
lean_inc(v_zetaDeltaFVarIds_2965_);
lean_inc(v_mctx_2964_);
lean_dec(v___x_2963_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3222_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7_spec__9___redArg___closed__3);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_mctx_2964_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_zetaDeltaFVarIds_2965_);
lean_ctor_set(v_reuseFailAlloc_3221_, 3, v_postponed_2966_);
lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_diag_2967_);
v___x_2973_ = v_reuseFailAlloc_3221_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2974_ = lean_st_ref_set(v___y_2893_, v___x_2973_);
lean_inc(v___x_2887_);
v___x_2975_ = l_Lean_Expr_const___override(v_brecOnGoName_2885_, v___x_2887_);
v___x_2976_ = l_Lean_mkAppN(v___x_2975_, v___x_2924_);
lean_inc_ref(v___x_2976_);
v___x_2977_ = l_Lean_Meta_mkPProdFstM(v___x_2976_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref(v___x_2977_);
v___x_2979_ = l_Lean_Meta_mkLambdaFVars(v___x_2924_, v_a_2978_, v___x_2925_, v___x_2884_, v___x_2925_, v___x_2884_, v___x_2926_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref(v___x_2979_);
v___x_2981_ = l_Lean_Meta_mkForallFVars(v___x_2924_, v___x_2918_, v___x_2925_, v___x_2884_, v___x_2884_, v___x_2926_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; lean_object* v___x_2983_; lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3196_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref(v___x_2981_);
lean_inc(v_levelParams_2886_);
v___x_2983_ = l_Lean_mkDefinitionValInferringUnsafe___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__5___redArg(v_brecOnName_2888_, v_levelParams_2886_, v_a_2982_, v_a_2980_, v___x_2931_, v___y_2895_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_3196_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3196_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
lean_inc(v_a_2984_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set_tag(v___x_2986_, 1);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_3195_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_addDecl(v___x_2989_, v___x_2925_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_toConstantVal_2991_; lean_object* v_name_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref(v___x_2990_);
v_toConstantVal_2991_ = lean_ctor_get(v_a_2984_, 0);
lean_inc_ref(v_toConstantVal_2991_);
lean_dec(v_a_2984_);
v_name_2992_ = lean_ctor_get(v_toConstantVal_2991_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_toConstantVal_2991_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; lean_object* v_unused_3194_; 
v_unused_3193_ = lean_ctor_get(v_toConstantVal_2991_, 2);
lean_dec(v_unused_3193_);
v_unused_3194_ = lean_ctor_get(v_toConstantVal_2991_, 1);
lean_dec(v_unused_3194_);
v___x_2994_ = v_toConstantVal_2991_;
v_isShared_2995_ = v_isSharedCheck_3192_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_name_2992_);
lean_dec(v_toConstantVal_2991_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3192_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_env_2998_; lean_object* v_nextMacroScope_2999_; lean_object* v_ngen_3000_; lean_object* v_auxDeclNGen_3001_; lean_object* v_traceState_3002_; lean_object* v_messages_3003_; lean_object* v_infoState_3004_; lean_object* v_snapshotTasks_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3190_; 
lean_inc(v_name_2992_);
v___x_2996_ = l_Lean_setReducibleAttribute___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__7(v_name_2992_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec_ref(v___x_2996_);
v___x_2997_ = lean_st_ref_take(v___y_2895_);
v_env_2998_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_2999_ = lean_ctor_get(v___x_2997_, 1);
v_ngen_3000_ = lean_ctor_get(v___x_2997_, 2);
v_auxDeclNGen_3001_ = lean_ctor_get(v___x_2997_, 3);
v_traceState_3002_ = lean_ctor_get(v___x_2997_, 4);
v_messages_3003_ = lean_ctor_get(v___x_2997_, 6);
v_infoState_3004_ = lean_ctor_get(v___x_2997_, 7);
v_snapshotTasks_3005_ = lean_ctor_get(v___x_2997_, 8);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3190_ == 0)
{
lean_object* v_unused_3191_; 
v_unused_3191_ = lean_ctor_get(v___x_2997_, 5);
lean_dec(v_unused_3191_);
v___x_3007_ = v___x_2997_;
v_isShared_3008_ = v_isSharedCheck_3190_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_snapshotTasks_3005_);
lean_inc(v_infoState_3004_);
lean_inc(v_messages_3003_);
lean_inc(v_traceState_3002_);
lean_inc(v_auxDeclNGen_3001_);
lean_inc(v_ngen_3000_);
lean_inc(v_nextMacroScope_2999_);
lean_inc(v_env_2998_);
lean_dec(v___x_2997_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3190_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_inc(v_name_2992_);
v___x_3009_ = l_Lean_markAuxRecursor(v_env_2998_, v_name_2992_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 5, v___x_2959_);
lean_ctor_set(v___x_3007_, 0, v___x_3009_);
v___x_3011_ = v___x_3007_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v___x_3009_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_nextMacroScope_2999_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v_ngen_3000_);
lean_ctor_set(v_reuseFailAlloc_3189_, 3, v_auxDeclNGen_3001_);
lean_ctor_set(v_reuseFailAlloc_3189_, 4, v_traceState_3002_);
lean_ctor_set(v_reuseFailAlloc_3189_, 5, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3189_, 6, v_messages_3003_);
lean_ctor_set(v_reuseFailAlloc_3189_, 7, v_infoState_3004_);
lean_ctor_set(v_reuseFailAlloc_3189_, 8, v_snapshotTasks_3005_);
v___x_3011_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v_mctx_3014_; lean_object* v_zetaDeltaFVarIds_3015_; lean_object* v_postponed_3016_; lean_object* v_diag_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3187_; 
v___x_3012_ = lean_st_ref_set(v___y_2895_, v___x_3011_);
v___x_3013_ = lean_st_ref_take(v___y_2893_);
v_mctx_3014_ = lean_ctor_get(v___x_3013_, 0);
v_zetaDeltaFVarIds_3015_ = lean_ctor_get(v___x_3013_, 2);
v_postponed_3016_ = lean_ctor_get(v___x_3013_, 3);
v_diag_3017_ = lean_ctor_get(v___x_3013_, 4);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3187_ == 0)
{
lean_object* v_unused_3188_; 
v_unused_3188_ = lean_ctor_get(v___x_3013_, 1);
lean_dec(v_unused_3188_);
v___x_3019_ = v___x_3013_;
v_isShared_3020_ = v_isSharedCheck_3187_;
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
v_isShared_3020_ = v_isSharedCheck_3187_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 1, v___x_2971_);
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_mctx_3014_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v_zetaDeltaFVarIds_3015_);
lean_ctor_set(v_reuseFailAlloc_3186_, 3, v_postponed_3016_);
lean_ctor_set(v_reuseFailAlloc_3186_, 4, v_diag_3017_);
v___x_3022_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v_env_3025_; lean_object* v_nextMacroScope_3026_; lean_object* v_ngen_3027_; lean_object* v_auxDeclNGen_3028_; lean_object* v_traceState_3029_; lean_object* v_messages_3030_; lean_object* v_infoState_3031_; lean_object* v_snapshotTasks_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3184_; 
v___x_3023_ = lean_st_ref_set(v___y_2893_, v___x_3022_);
v___x_3024_ = lean_st_ref_take(v___y_2895_);
v_env_3025_ = lean_ctor_get(v___x_3024_, 0);
v_nextMacroScope_3026_ = lean_ctor_get(v___x_3024_, 1);
v_ngen_3027_ = lean_ctor_get(v___x_3024_, 2);
v_auxDeclNGen_3028_ = lean_ctor_get(v___x_3024_, 3);
v_traceState_3029_ = lean_ctor_get(v___x_3024_, 4);
v_messages_3030_ = lean_ctor_get(v___x_3024_, 6);
v_infoState_3031_ = lean_ctor_get(v___x_3024_, 7);
v_snapshotTasks_3032_ = lean_ctor_get(v___x_3024_, 8);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3184_ == 0)
{
lean_object* v_unused_3185_; 
v_unused_3185_ = lean_ctor_get(v___x_3024_, 5);
lean_dec(v_unused_3185_);
v___x_3034_ = v___x_3024_;
v_isShared_3035_ = v_isSharedCheck_3184_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_snapshotTasks_3032_);
lean_inc(v_infoState_3031_);
lean_inc(v_messages_3030_);
lean_inc(v_traceState_3029_);
lean_inc(v_auxDeclNGen_3028_);
lean_inc(v_ngen_3027_);
lean_inc(v_nextMacroScope_3026_);
lean_inc(v_env_3025_);
lean_dec(v___x_3024_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3184_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3038_; 
lean_inc(v_name_2992_);
v___x_3036_ = l_Lean_addProtected(v_env_3025_, v_name_2992_);
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 5, v___x_2959_);
lean_ctor_set(v___x_3034_, 0, v___x_3036_);
v___x_3038_ = v___x_3034_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3183_, 1, v_nextMacroScope_3026_);
lean_ctor_set(v_reuseFailAlloc_3183_, 2, v_ngen_3027_);
lean_ctor_set(v_reuseFailAlloc_3183_, 3, v_auxDeclNGen_3028_);
lean_ctor_set(v_reuseFailAlloc_3183_, 4, v_traceState_3029_);
lean_ctor_set(v_reuseFailAlloc_3183_, 5, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3183_, 6, v_messages_3030_);
lean_ctor_set(v_reuseFailAlloc_3183_, 7, v_infoState_3031_);
lean_ctor_set(v_reuseFailAlloc_3183_, 8, v_snapshotTasks_3032_);
v___x_3038_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v_mctx_3041_; lean_object* v_zetaDeltaFVarIds_3042_; lean_object* v_postponed_3043_; lean_object* v_diag_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3181_; 
v___x_3039_ = lean_st_ref_set(v___y_2895_, v___x_3038_);
v___x_3040_ = lean_st_ref_take(v___y_2893_);
v_mctx_3041_ = lean_ctor_get(v___x_3040_, 0);
v_zetaDeltaFVarIds_3042_ = lean_ctor_get(v___x_3040_, 2);
v_postponed_3043_ = lean_ctor_get(v___x_3040_, 3);
v_diag_3044_ = lean_ctor_get(v___x_3040_, 4);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3181_ == 0)
{
lean_object* v_unused_3182_; 
v_unused_3182_ = lean_ctor_get(v___x_3040_, 1);
lean_dec(v_unused_3182_);
v___x_3046_ = v___x_3040_;
v_isShared_3047_ = v_isSharedCheck_3181_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_diag_3044_);
lean_inc(v_postponed_3043_);
lean_inc(v_zetaDeltaFVarIds_3042_);
lean_inc(v_mctx_3041_);
lean_dec(v___x_3040_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3181_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 1, v___x_2971_);
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_mctx_3041_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v_zetaDeltaFVarIds_3042_);
lean_ctor_set(v_reuseFailAlloc_3180_, 3, v_postponed_3043_);
lean_ctor_set(v_reuseFailAlloc_3180_, 4, v_diag_3044_);
v___x_3049_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_st_ref_set(v___y_2893_, v___x_3049_);
v___x_3051_ = l_Lean_Meta_mkPProdSndM(v___x_2976_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref(v___x_3051_);
v___x_3053_ = l_Lean_Expr_const___override(v_name_2992_, v___x_2887_);
v___x_3054_ = l_Lean_mkAppN(v___x_3053_, v___x_2924_);
v___x_3055_ = lean_array_get(v___x_2882_, v_fs_2891_, v_val_2883_);
lean_dec_ref(v_fs_2891_);
v___x_3056_ = l_Lean_mkAppN(v___x_3055_, v___x_2917_);
lean_dec_ref(v___x_2917_);
v___x_3057_ = l_Lean_Expr_app___override(v___x_3056_, v_a_3052_);
v___x_3058_ = l_Lean_Meta_mkEq(v___x_3054_, v___x_3057_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = lean_box(0);
lean_inc(v_a_3059_);
v___x_3061_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3059_, v___x_3060_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_a_3062_);
lean_dec_ref(v___x_3061_);
v___x_3063_ = l_Lean_Expr_mvarId_x21(v_a_3062_);
v___x_3064_ = l_Lean_Expr_fvarId_x21(v___x_2880_);
lean_dec_ref(v___x_2880_);
v___x_3065_ = lean_mk_empty_array_with_capacity(v___x_2889_);
v___x_3066_ = lean_box(0);
v___x_3067_ = l_Lean_MVarId_cases(v___x_3063_, v___x_3064_, v___x_3065_, v___x_2925_, v___x_3066_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; size_t v_sz_3070_; lean_object* v___x_3071_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref(v___x_3067_);
v___x_3069_ = lean_box(0);
v_sz_3070_ = lean_array_size(v_a_3068_);
v___x_3071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__4(v_a_3068_, v_sz_3070_, v___x_2876_, v___x_3069_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec(v_a_3068_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v___x_3072_; lean_object* v_a_3073_; lean_object* v___x_3074_; 
lean_dec_ref(v___x_3071_);
v___x_3072_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__5___redArg(v_a_3062_, v___y_2893_);
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref(v___x_3072_);
v___x_3074_ = l_Lean_Meta_mkForallFVars(v___x_2924_, v_a_3059_, v___x_2925_, v___x_2884_, v___x_2884_, v___x_2926_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3076_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref(v___x_3074_);
v___x_3076_ = l_Lean_Meta_mkLambdaFVars(v___x_2924_, v_a_3073_, v___x_2925_, v___x_2884_, v___x_2925_, v___x_2884_, v___x_2926_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec_ref(v___x_2924_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3079_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref(v___x_3076_);
lean_inc(v_brecOnEqName_2890_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 2, v_a_3075_);
lean_ctor_set(v___x_2994_, 1, v_levelParams_2886_);
lean_ctor_set(v___x_2994_, 0, v_brecOnEqName_2890_);
v___x_3079_ = v___x_2994_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_brecOnEqName_2890_);
lean_ctor_set(v_reuseFailAlloc_3131_, 1, v_levelParams_2886_);
lean_ctor_set(v_reuseFailAlloc_3131_, 2, v_a_3075_);
v___x_3079_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3080_ = lean_box(0);
lean_inc(v_brecOnEqName_2890_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 1);
lean_ctor_set(v___x_2905_, 1, v___x_3080_);
lean_ctor_set(v___x_2905_, 0, v_brecOnEqName_2890_);
v___x_3082_ = v___x_2905_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_brecOnEqName_2890_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3084_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 2, v___x_3082_);
lean_ctor_set(v___x_2943_, 1, v_a_3077_);
lean_ctor_set(v___x_2943_, 0, v___x_3079_);
v___x_3084_ = v___x_2943_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_a_3077_);
lean_ctor_set(v_reuseFailAlloc_3129_, 2, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v_a_3086_; lean_object* v___x_3087_; 
v___x_3085_ = l_Lean_mkThmOrUnsafeDef___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__6___redArg(v___x_3084_, v___y_2895_);
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref(v___x_3085_);
v___x_3087_ = l_Lean_addDecl(v_a_3086_, v___x_2925_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3127_; 
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3127_ == 0)
{
lean_object* v_unused_3128_; 
v_unused_3128_ = lean_ctor_get(v___x_3087_, 0);
lean_dec(v_unused_3128_);
v___x_3089_ = v___x_3087_;
v_isShared_3090_ = v_isSharedCheck_3127_;
goto v_resetjp_3088_;
}
else
{
lean_dec(v___x_3087_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3127_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3091_; lean_object* v_env_3092_; lean_object* v_nextMacroScope_3093_; lean_object* v_ngen_3094_; lean_object* v_auxDeclNGen_3095_; lean_object* v_traceState_3096_; lean_object* v_messages_3097_; lean_object* v_infoState_3098_; lean_object* v_snapshotTasks_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3125_; 
v___x_3091_ = lean_st_ref_take(v___y_2895_);
v_env_3092_ = lean_ctor_get(v___x_3091_, 0);
v_nextMacroScope_3093_ = lean_ctor_get(v___x_3091_, 1);
v_ngen_3094_ = lean_ctor_get(v___x_3091_, 2);
v_auxDeclNGen_3095_ = lean_ctor_get(v___x_3091_, 3);
v_traceState_3096_ = lean_ctor_get(v___x_3091_, 4);
v_messages_3097_ = lean_ctor_get(v___x_3091_, 6);
v_infoState_3098_ = lean_ctor_get(v___x_3091_, 7);
v_snapshotTasks_3099_ = lean_ctor_get(v___x_3091_, 8);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3091_);
if (v_isSharedCheck_3125_ == 0)
{
lean_object* v_unused_3126_; 
v_unused_3126_ = lean_ctor_get(v___x_3091_, 5);
lean_dec(v_unused_3126_);
v___x_3101_ = v___x_3091_;
v_isShared_3102_ = v_isSharedCheck_3125_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_snapshotTasks_3099_);
lean_inc(v_infoState_3098_);
lean_inc(v_messages_3097_);
lean_inc(v_traceState_3096_);
lean_inc(v_auxDeclNGen_3095_);
lean_inc(v_ngen_3094_);
lean_inc(v_nextMacroScope_3093_);
lean_inc(v_env_3092_);
lean_dec(v___x_3091_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3125_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3103_ = l_Lean_addProtected(v_env_3092_, v_brecOnEqName_2890_);
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 5, v___x_2959_);
lean_ctor_set(v___x_3101_, 0, v___x_3103_);
v___x_3105_ = v___x_3101_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3103_);
lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_nextMacroScope_3093_);
lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_ngen_3094_);
lean_ctor_set(v_reuseFailAlloc_3124_, 3, v_auxDeclNGen_3095_);
lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_traceState_3096_);
lean_ctor_set(v_reuseFailAlloc_3124_, 5, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3124_, 6, v_messages_3097_);
lean_ctor_set(v_reuseFailAlloc_3124_, 7, v_infoState_3098_);
lean_ctor_set(v_reuseFailAlloc_3124_, 8, v_snapshotTasks_3099_);
v___x_3105_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v_mctx_3108_; lean_object* v_zetaDeltaFVarIds_3109_; lean_object* v_postponed_3110_; lean_object* v_diag_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3122_; 
v___x_3106_ = lean_st_ref_set(v___y_2895_, v___x_3105_);
v___x_3107_ = lean_st_ref_take(v___y_2893_);
v_mctx_3108_ = lean_ctor_get(v___x_3107_, 0);
v_zetaDeltaFVarIds_3109_ = lean_ctor_get(v___x_3107_, 2);
v_postponed_3110_ = lean_ctor_get(v___x_3107_, 3);
v_diag_3111_ = lean_ctor_get(v___x_3107_, 4);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3122_ == 0)
{
lean_object* v_unused_3123_; 
v_unused_3123_ = lean_ctor_get(v___x_3107_, 1);
lean_dec(v_unused_3123_);
v___x_3113_ = v___x_3107_;
v_isShared_3114_ = v_isSharedCheck_3122_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_diag_3111_);
lean_inc(v_postponed_3110_);
lean_inc(v_zetaDeltaFVarIds_3109_);
lean_inc(v_mctx_3108_);
lean_dec(v___x_3107_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3122_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
lean_ctor_set(v___x_3113_, 1, v___x_2971_);
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_mctx_3108_);
lean_ctor_set(v_reuseFailAlloc_3121_, 1, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_3121_, 2, v_zetaDeltaFVarIds_3109_);
lean_ctor_set(v_reuseFailAlloc_3121_, 3, v_postponed_3110_);
lean_ctor_set(v_reuseFailAlloc_3121_, 4, v_diag_3111_);
v___x_3116_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3117_ = lean_st_ref_set(v___y_2893_, v___x_3116_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3069_);
v___x_3119_ = v___x_3089_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3069_);
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
}
}
}
else
{
lean_dec(v_brecOnEqName_2890_);
return v___x_3087_;
}
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_a_3075_);
lean_del_object(v___x_2994_);
lean_del_object(v___x_2943_);
lean_del_object(v___x_2905_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_levelParams_2886_);
v_a_3132_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3076_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3076_);
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
lean_dec(v_a_3073_);
lean_del_object(v___x_2994_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_del_object(v___x_2905_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_levelParams_2886_);
v_a_3140_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3074_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3074_);
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
lean_dec(v_a_3062_);
lean_dec(v_a_3059_);
lean_del_object(v___x_2994_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_del_object(v___x_2905_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_levelParams_2886_);
return v___x_3071_;
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_a_3062_);
lean_dec(v_a_3059_);
lean_del_object(v___x_2994_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_del_object(v___x_2905_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_levelParams_2886_);
v_a_3148_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3067_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3067_);
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
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_a_3059_);
lean_del_object(v___x_2994_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_del_object(v___x_2905_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_levelParams_2886_);
lean_dec_ref(v___x_2880_);
v_a_3156_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3061_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3061_);
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
lean_del_object(v___x_2994_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_del_object(v___x_2905_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_levelParams_2886_);
lean_dec_ref(v___x_2880_);
v_a_3164_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3058_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3058_);
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
lean_del_object(v___x_2994_);
lean_dec(v_name_2992_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2917_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
v_a_3172_ = lean_ctor_get(v___x_3051_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3051_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3051_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3051_);
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
}
}
}
}
else
{
lean_dec(v_a_2984_);
lean_dec_ref(v___x_2976_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2917_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3204_; 
lean_dec(v_a_2980_);
lean_dec_ref(v___x_2976_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2917_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
v_a_3197_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_2981_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_2981_);
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
lean_dec_ref(v___x_2976_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2917_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
v_a_3205_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3207_ = v___x_2979_;
v_isShared_3208_ = v_isSharedCheck_3212_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_a_3205_);
lean_dec(v___x_2979_);
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
else
{
lean_object* v_a_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3220_; 
lean_dec_ref(v___x_2976_);
lean_del_object(v___x_2943_);
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2917_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
v_a_3213_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3215_ = v___x_2977_;
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_a_3213_);
lean_dec(v___x_2977_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3220_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3218_; 
if (v_isShared_3216_ == 0)
{
v___x_3218_ = v___x_3215_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_a_3213_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
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
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2917_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec(v_brecOnGoName_2885_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
return v___x_2939_;
}
}
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v_a_2928_);
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2917_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec(v_brecOnGoName_2885_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
v_a_3232_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_2929_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_2929_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec_ref(v___x_2924_);
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2911_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec(v_brecOnGoName_2885_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
v_a_3240_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_2927_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_2927_);
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
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v___x_2918_);
lean_dec_ref(v___x_2917_);
lean_dec_ref(v___x_2915_);
lean_dec_ref(v___x_2913_);
lean_dec_ref(v___x_2911_);
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec(v_brecOnGoName_2885_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
v_a_3248_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_2921_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_2921_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_del_object(v___x_2905_);
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec(v_brecOnGoName_2885_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2878_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2872_);
v_a_3256_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_2908_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_2908_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec_ref(v_fs_2891_);
lean_dec(v_brecOnEqName_2890_);
lean_dec(v_brecOnName_2888_);
lean_dec(v___x_2887_);
lean_dec(v_levelParams_2886_);
lean_dec(v_brecOnGoName_2885_);
lean_dec_ref(v___x_2882_);
lean_dec_ref(v___x_2880_);
lean_dec_ref(v___x_2879_);
lean_dec_ref(v___x_2878_);
lean_dec_ref(v___x_2874_);
lean_dec_ref(v___x_2872_);
lean_dec(v___x_2869_);
v_a_3266_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_2901_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_2901_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed(lean_object** _args){
lean_object* v___x_3274_ = _args[0];
lean_object* v_tail_3275_ = _args[1];
lean_object* v_recName_3276_ = _args[2];
lean_object* v___x_3277_ = _args[3];
lean_object* v___x_3278_ = _args[4];
lean_object* v___x_3279_ = _args[5];
lean_object* v_sz_3280_ = _args[6];
lean_object* v___x_3281_ = _args[7];
lean_object* v___x_3282_ = _args[8];
lean_object* v___x_3283_ = _args[9];
lean_object* v___x_3284_ = _args[10];
lean_object* v___x_3285_ = _args[11];
lean_object* v___x_3286_ = _args[12];
lean_object* v___x_3287_ = _args[13];
lean_object* v_val_3288_ = _args[14];
lean_object* v___x_3289_ = _args[15];
lean_object* v_brecOnGoName_3290_ = _args[16];
lean_object* v_levelParams_3291_ = _args[17];
lean_object* v___x_3292_ = _args[18];
lean_object* v_brecOnName_3293_ = _args[19];
lean_object* v___x_3294_ = _args[20];
lean_object* v_brecOnEqName_3295_ = _args[21];
lean_object* v_fs_3296_ = _args[22];
lean_object* v___y_3297_ = _args[23];
lean_object* v___y_3298_ = _args[24];
lean_object* v___y_3299_ = _args[25];
lean_object* v___y_3300_ = _args[26];
lean_object* v___y_3301_ = _args[27];
_start:
{
size_t v_sz_boxed_3302_; size_t v___x_30806__boxed_3303_; uint8_t v___x_30814__boxed_3304_; lean_object* v_res_3305_; 
v_sz_boxed_3302_ = lean_unbox_usize(v_sz_3280_);
lean_dec(v_sz_3280_);
v___x_30806__boxed_3303_ = lean_unbox_usize(v___x_3281_);
lean_dec(v___x_3281_);
v___x_30814__boxed_3304_ = lean_unbox(v___x_3289_);
v_res_3305_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1(v___x_3274_, v_tail_3275_, v_recName_3276_, v___x_3277_, v___x_3278_, v___x_3279_, v_sz_boxed_3302_, v___x_30806__boxed_3303_, v___x_3282_, v___x_3283_, v___x_3284_, v___x_3285_, v___x_3286_, v___x_3287_, v_val_3288_, v___x_30814__boxed_3304_, v_brecOnGoName_3290_, v_levelParams_3291_, v___x_3292_, v_brecOnName_3293_, v___x_3294_, v_brecOnEqName_3295_, v_fs_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v___x_3294_);
lean_dec(v_val_3288_);
lean_dec(v___x_3286_);
lean_dec_ref(v___x_3282_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(lean_object* v_targs_3306_, lean_object* v_a_3307_, uint8_t v___x_3308_, lean_object* v_f_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; 
lean_inc_ref(v_targs_3306_);
v___x_3315_ = lean_array_push(v_targs_3306_, v_f_3309_);
v___x_3316_ = l_Lean_mkAppN(v_a_3307_, v_targs_3306_);
lean_dec_ref(v_targs_3306_);
v___x_3317_ = 0;
v___x_3318_ = 1;
v___x_3319_ = l_Lean_Meta_mkForallFVars(v___x_3315_, v___x_3316_, v___x_3317_, v___x_3308_, v___x_3308_, v___x_3318_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
lean_dec_ref(v___x_3315_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed(lean_object* v_targs_3320_, lean_object* v_a_3321_, lean_object* v___x_3322_, lean_object* v_f_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v___x_31524__boxed_3329_; lean_object* v_res_3330_; 
v___x_31524__boxed_3329_ = lean_unbox(v___x_3322_);
v_res_3330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0(v_targs_3320_, v_a_3321_, v___x_31524__boxed_3329_, v_f_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(lean_object* v_a_3334_, uint8_t v___x_3335_, lean_object* v___x_3336_, lean_object* v_targs_3337_, lean_object* v_x_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v___x_3344_; lean_object* v___f_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3344_ = lean_box(v___x_3335_);
lean_inc_ref(v_targs_3337_);
v___f_3345_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__0___boxed), 9, 3);
lean_closure_set(v___f_3345_, 0, v_targs_3337_);
lean_closure_set(v___f_3345_, 1, v_a_3334_);
lean_closure_set(v___f_3345_, 2, v___x_3344_);
v___x_3346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___closed__1));
v___x_3347_ = l_Lean_mkAppN(v___x_3336_, v_targs_3337_);
lean_dec_ref(v_targs_3337_);
v___x_3348_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2___redArg(v___x_3346_, v___x_3347_, v___f_3345_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed(lean_object* v_a_3349_, lean_object* v___x_3350_, lean_object* v___x_3351_, lean_object* v_targs_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
uint8_t v___x_31558__boxed_3359_; lean_object* v_res_3360_; 
v___x_31558__boxed_3359_ = lean_unbox(v___x_3350_);
v_res_3360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1(v_a_3349_, v___x_31558__boxed_3359_, v___x_3351_, v_targs_3352_, v_x_3353_, v___y_3354_, v___y_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
lean_dec(v___y_3355_);
lean_dec_ref(v___y_3354_);
lean_dec_ref(v_x_3353_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(lean_object* v_a_3361_, lean_object* v_x_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3368_, 0, v_a_3361_);
return v___x_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed(lean_object* v_a_3369_, lean_object* v_x_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2(v_a_3369_, v_x_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec_ref(v_x_3370_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(lean_object* v_as_3378_, size_t v_sz_3379_, size_t v_i_3380_, lean_object* v_b_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_){
_start:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_usize_dec_lt(v_i_3380_, v_sz_3379_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
v___x_3388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3388_, 0, v_b_3381_);
return v___x_3388_;
}
else
{
lean_object* v_snd_3389_; lean_object* v_fst_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3486_; 
v_snd_3389_ = lean_ctor_get(v_b_3381_, 1);
v_fst_3390_ = lean_ctor_get(v_b_3381_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v_b_3381_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3392_ = v_b_3381_;
v_isShared_3393_ = v_isSharedCheck_3486_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_snd_3389_);
lean_inc(v_fst_3390_);
lean_dec(v_b_3381_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3486_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v_fst_3394_; lean_object* v_snd_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3485_; 
v_fst_3394_ = lean_ctor_get(v_snd_3389_, 0);
v_snd_3395_ = lean_ctor_get(v_snd_3389_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_snd_3389_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3397_ = v_snd_3389_;
v_isShared_3398_ = v_isSharedCheck_3485_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_snd_3395_);
lean_inc(v_fst_3394_);
lean_dec(v_snd_3389_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3485_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_next_3407_; 
v_next_3407_ = lean_ctor_get(v_snd_3395_, 0);
lean_inc(v_next_3407_);
if (lean_obj_tag(v_next_3407_) == 0)
{
goto v___jp_3399_;
}
else
{
lean_object* v_upperBound_3408_; lean_object* v_val_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3484_; 
v_upperBound_3408_ = lean_ctor_get(v_snd_3395_, 1);
v_val_3409_ = lean_ctor_get(v_next_3407_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_next_3407_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3411_ = v_next_3407_;
v_isShared_3412_ = v_isSharedCheck_3484_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_val_3409_);
lean_dec(v_next_3407_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3484_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_nat_dec_lt(v_val_3409_, v_upperBound_3408_);
if (v___x_3413_ == 0)
{
lean_del_object(v___x_3411_);
lean_dec(v_val_3409_);
goto v___jp_3399_;
}
else
{
lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3481_; 
lean_inc(v_upperBound_3408_);
lean_del_object(v___x_3397_);
lean_del_object(v___x_3392_);
v_isSharedCheck_3481_ = !lean_is_exclusive(v_snd_3395_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; lean_object* v_unused_3483_; 
v_unused_3482_ = lean_ctor_get(v_snd_3395_, 1);
lean_dec(v_unused_3482_);
v_unused_3483_ = lean_ctor_get(v_snd_3395_, 0);
lean_dec(v_unused_3483_);
v___x_3415_ = v_snd_3395_;
v_isShared_3416_ = v_isSharedCheck_3481_;
goto v_resetjp_3414_;
}
else
{
lean_dec(v_snd_3395_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3481_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v_array_3417_; lean_object* v_start_3418_; lean_object* v_stop_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3423_; 
v_array_3417_ = lean_ctor_get(v_fst_3394_, 0);
v_start_3418_ = lean_ctor_get(v_fst_3394_, 1);
v_stop_3419_ = lean_ctor_get(v_fst_3394_, 2);
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_add(v_val_3409_, v___x_3420_);
lean_dec(v_val_3409_);
lean_inc(v___x_3421_);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3421_);
v___x_3423_ = v___x_3411_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3421_);
v___x_3423_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3425_; 
if (v_isShared_3416_ == 0)
{
lean_ctor_set(v___x_3415_, 0, v___x_3423_);
v___x_3425_ = v___x_3415_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3423_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_upperBound_3408_);
v___x_3425_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_nat_dec_lt(v_start_3418_, v_stop_3419_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
lean_dec(v___x_3421_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v_fst_3394_);
lean_ctor_set(v___x_3427_, 1, v___x_3425_);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v_fst_3390_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
return v___x_3429_;
}
else
{
lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3475_; 
lean_inc(v_stop_3419_);
lean_inc(v_start_3418_);
lean_inc_ref(v_array_3417_);
v_isSharedCheck_3475_ = !lean_is_exclusive(v_fst_3394_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; lean_object* v_unused_3477_; lean_object* v_unused_3478_; 
v_unused_3476_ = lean_ctor_get(v_fst_3394_, 2);
lean_dec(v_unused_3476_);
v_unused_3477_ = lean_ctor_get(v_fst_3394_, 1);
lean_dec(v_unused_3477_);
v_unused_3478_ = lean_ctor_get(v_fst_3394_, 0);
lean_dec(v_unused_3478_);
v___x_3431_ = v_fst_3394_;
v_isShared_3432_ = v_isSharedCheck_3475_;
goto v_resetjp_3430_;
}
else
{
lean_dec(v_fst_3394_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3475_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_a_3433_; lean_object* v___x_3434_; 
v_a_3433_ = lean_array_uget_borrowed(v_as_3378_, v_i_3380_);
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v___y_3383_);
lean_inc_ref(v___y_3382_);
lean_inc(v_a_3433_);
v___x_3434_ = lean_infer_type(v_a_3433_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; uint8_t v___x_3439_; lean_object* v___x_3440_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref(v___x_3434_);
v___x_3436_ = lean_array_fget_borrowed(v_array_3417_, v_start_3418_);
v___x_3437_ = lean_box(v___x_3426_);
lean_inc(v___x_3436_);
lean_inc(v_a_3433_);
v___f_3438_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__1___boxed), 10, 3);
lean_closure_set(v___f_3438_, 0, v_a_3433_);
lean_closure_set(v___f_3438_, 1, v___x_3437_);
lean_closure_set(v___f_3438_, 2, v___x_3436_);
v___x_3439_ = 0;
v___x_3440_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_a_3435_, v___f_3438_, v___x_3439_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; lean_object* v___f_3442_; lean_object* v___x_3443_; lean_object* v___x_3445_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref(v___x_3440_);
v___f_3442_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___lam__2___boxed), 7, 1);
lean_closure_set(v___f_3442_, 0, v_a_3441_);
v___x_3443_ = lean_nat_add(v_start_3418_, v___x_3420_);
lean_dec(v_start_3418_);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 1, v___x_3443_);
v___x_3445_ = v___x_3431_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_array_3417_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3458_, 2, v_stop_3419_);
v___x_3445_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; 
v___x_3446_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___closed__0));
v___x_3447_ = l_Nat_reprFast(v___x_3421_);
v___x_3448_ = lean_string_append(v___x_3446_, v___x_3447_);
lean_dec_ref(v___x_3447_);
v___x_3449_ = lean_box(0);
v___x_3450_ = l_Lean_Name_str___override(v___x_3449_, v___x_3448_);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3450_);
lean_ctor_set(v___x_3451_, 1, v___f_3442_);
v___x_3452_ = lean_array_push(v_fst_3390_, v___x_3451_);
v___x_3453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3453_, 0, v___x_3445_);
lean_ctor_set(v___x_3453_, 1, v___x_3425_);
v___x_3454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3452_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = ((size_t)1ULL);
v___x_3456_ = lean_usize_add(v_i_3380_, v___x_3455_);
v_i_3380_ = v___x_3456_;
v_b_3381_ = v___x_3454_;
goto _start;
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_del_object(v___x_3431_);
lean_dec_ref(v___x_3425_);
lean_dec(v___x_3421_);
lean_dec(v_stop_3419_);
lean_dec(v_start_3418_);
lean_dec_ref(v_array_3417_);
lean_dec(v_fst_3390_);
v_a_3459_ = lean_ctor_get(v___x_3440_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3440_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3440_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3440_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_del_object(v___x_3431_);
lean_dec_ref(v___x_3425_);
lean_dec(v___x_3421_);
lean_dec(v_stop_3419_);
lean_dec(v_start_3418_);
lean_dec_ref(v_array_3417_);
lean_dec(v_fst_3390_);
v_a_3467_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3434_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3434_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
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
v___jp_3399_:
{
lean_object* v___x_3401_; 
if (v_isShared_3398_ == 0)
{
v___x_3401_ = v___x_3397_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_fst_3394_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_snd_3395_);
v___x_3401_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3393_ == 0)
{
lean_ctor_set(v___x_3392_, 1, v___x_3401_);
v___x_3403_ = v___x_3392_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_fst_3390_);
lean_ctor_set(v_reuseFailAlloc_3405_, 1, v___x_3401_);
v___x_3403_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
return v___x_3404_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1___boxed(lean_object* v_as_3487_, lean_object* v_sz_3488_, lean_object* v_i_3489_, lean_object* v_b_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
size_t v_sz_boxed_3496_; size_t v_i_boxed_3497_; lean_object* v_res_3498_; 
v_sz_boxed_3496_ = lean_unbox_usize(v_sz_3488_);
lean_dec(v_sz_3488_);
v_i_boxed_3497_ = lean_unbox_usize(v_i_3489_);
lean_dec(v_i_3489_);
v_res_3498_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v_as_3487_, v_sz_boxed_3496_, v_i_boxed_3497_, v_b_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_);
lean_dec(v___y_3494_);
lean_dec_ref(v___y_3493_);
lean_dec(v___y_3492_);
lean_dec_ref(v___y_3491_);
lean_dec_ref(v_as_3487_);
return v_res_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(size_t v_sz_3499_, size_t v_i_3500_, lean_object* v_bs_3501_){
_start:
{
uint8_t v___x_3502_; 
v___x_3502_ = lean_usize_dec_lt(v_i_3500_, v_sz_3499_);
if (v___x_3502_ == 0)
{
return v_bs_3501_;
}
else
{
lean_object* v_v_3503_; lean_object* v_fst_3504_; lean_object* v_snd_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3521_; 
v_v_3503_ = lean_array_uget(v_bs_3501_, v_i_3500_);
v_fst_3504_ = lean_ctor_get(v_v_3503_, 0);
v_snd_3505_ = lean_ctor_get(v_v_3503_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_v_3503_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3507_ = v_v_3503_;
v_isShared_3508_ = v_isSharedCheck_3521_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_snd_3505_);
lean_inc(v_fst_3504_);
lean_dec(v_v_3503_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3521_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3509_; lean_object* v_bs_x27_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3514_; 
v___x_3509_ = lean_unsigned_to_nat(0u);
v_bs_x27_3510_ = lean_array_uset(v_bs_3501_, v_i_3500_, v___x_3509_);
v___x_3511_ = 0;
v___x_3512_ = lean_box(v___x_3511_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 0, v___x_3512_);
v___x_3514_ = v___x_3507_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3512_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v_snd_3505_);
v___x_3514_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
lean_object* v___x_3515_; size_t v___x_3516_; size_t v___x_3517_; lean_object* v___x_3518_; 
v___x_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3515_, 0, v_fst_3504_);
lean_ctor_set(v___x_3515_, 1, v___x_3514_);
v___x_3516_ = ((size_t)1ULL);
v___x_3517_ = lean_usize_add(v_i_3500_, v___x_3516_);
v___x_3518_ = lean_array_uset(v_bs_x27_3510_, v_i_3500_, v___x_3515_);
v_i_3500_ = v___x_3517_;
v_bs_3501_ = v___x_3518_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7___boxed(lean_object* v_sz_3522_, lean_object* v_i_3523_, lean_object* v_bs_3524_){
_start:
{
size_t v_sz_boxed_3525_; size_t v_i_boxed_3526_; lean_object* v_res_3527_; 
v_sz_boxed_3525_ = lean_unbox_usize(v_sz_3522_);
lean_dec(v_sz_3522_);
v_i_boxed_3526_ = lean_unbox_usize(v_i_3523_);
lean_dec(v_i_3523_);
v_res_3527_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_boxed_3525_, v_i_boxed_3526_, v_bs_3524_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0(lean_object* v___x_3528_, lean_object* v_a_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_30367__overap_3536_; lean_object* v___x_3537_; 
v___x_3535_ = l_Lean_instInhabitedExpr;
v___x_30367__overap_3536_ = l_instInhabitedOfMonad___redArg(v___x_3528_, v___x_3535_);
lean_inc(v___y_3533_);
lean_inc_ref(v___y_3532_);
lean_inc(v___y_3531_);
lean_inc_ref(v___y_3530_);
v___x_3537_ = lean_apply_5(v___x_30367__overap_3536_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, lean_box(0));
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0___boxed(lean_object* v___x_3538_, lean_object* v_a_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0(v___x_3538_, v_a_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
lean_dec_ref(v_a_3539_);
return v_res_3545_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_instMonadEIO(lean_box(0));
return v___x_3546_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__0);
v___x_3548_ = l_StateRefT_x27_instMonad___redArg(v___x_3547_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0___boxed(lean_object* v_acc_3553_, lean_object* v_declInfos_3554_, lean_object* v_k_3555_, lean_object* v_kind_3556_, lean_object* v_inst_3557_, lean_object* v_b_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
uint8_t v_kind_boxed_3564_; lean_object* v_res_3565_; 
v_kind_boxed_3564_ = lean_unbox(v_kind_3556_);
v_res_3565_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0(v_acc_3553_, v_declInfos_3554_, v_k_3555_, v_kind_boxed_3564_, v_inst_3557_, v_b_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(lean_object* v_acc_3566_, lean_object* v_declInfos_3567_, lean_object* v_k_3568_, uint8_t v_kind_3569_, lean_object* v_inst_3570_, lean_object* v_name_3571_, uint8_t v_bi_3572_, lean_object* v_type_3573_, uint8_t v_kind_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_){
_start:
{
lean_object* v___x_3580_; lean_object* v___f_3581_; lean_object* v___x_3582_; 
v___x_3580_ = lean_box(v_kind_3569_);
v___f_3581_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3581_, 0, v_acc_3566_);
lean_closure_set(v___f_3581_, 1, v_declInfos_3567_);
lean_closure_set(v___f_3581_, 2, v_k_3568_);
lean_closure_set(v___f_3581_, 3, v___x_3580_);
lean_closure_set(v___f_3581_, 4, v_inst_3570_);
v___x_3582_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3571_, v_bi_3572_, v_type_3573_, v___f_3581_, v_kind_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3582_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3582_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
v_a_3591_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3582_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3582_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(lean_object* v_declInfos_3599_, lean_object* v_k_3600_, uint8_t v_kind_3601_, lean_object* v_inst_3602_, lean_object* v_acc_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v_toApplicative_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3695_; 
v___x_3609_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__1);
v_toApplicative_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3695_ == 0)
{
lean_object* v_unused_3696_; 
v_unused_3696_ = lean_ctor_get(v___x_3609_, 1);
lean_dec(v_unused_3696_);
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3695_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_toApplicative_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3695_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v_toFunctor_3614_; lean_object* v_toSeq_3615_; lean_object* v_toSeqLeft_3616_; lean_object* v_toSeqRight_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3693_; 
v_toFunctor_3614_ = lean_ctor_get(v_toApplicative_3610_, 0);
v_toSeq_3615_ = lean_ctor_get(v_toApplicative_3610_, 2);
v_toSeqLeft_3616_ = lean_ctor_get(v_toApplicative_3610_, 3);
v_toSeqRight_3617_ = lean_ctor_get(v_toApplicative_3610_, 4);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_toApplicative_3610_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; 
v_unused_3694_ = lean_ctor_get(v_toApplicative_3610_, 1);
lean_dec(v_unused_3694_);
v___x_3619_ = v_toApplicative_3610_;
v_isShared_3620_ = v_isSharedCheck_3693_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_toSeqRight_3617_);
lean_inc(v_toSeqLeft_3616_);
lean_inc(v_toSeq_3615_);
lean_inc(v_toFunctor_3614_);
lean_dec(v_toApplicative_3610_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3693_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___f_3621_; lean_object* v___f_3622_; lean_object* v___f_3623_; lean_object* v___f_3624_; lean_object* v___x_3625_; lean_object* v___f_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___x_3630_; 
v___f_3621_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__2));
v___f_3622_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__3));
lean_inc_ref(v_toFunctor_3614_);
v___f_3623_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3623_, 0, v_toFunctor_3614_);
v___f_3624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3624_, 0, v_toFunctor_3614_);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___f_3623_);
lean_ctor_set(v___x_3625_, 1, v___f_3624_);
v___f_3626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3626_, 0, v_toSeqRight_3617_);
v___f_3627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3627_, 0, v_toSeqLeft_3616_);
v___f_3628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3628_, 0, v_toSeq_3615_);
if (v_isShared_3620_ == 0)
{
lean_ctor_set(v___x_3619_, 4, v___f_3626_);
lean_ctor_set(v___x_3619_, 3, v___f_3627_);
lean_ctor_set(v___x_3619_, 2, v___f_3628_);
lean_ctor_set(v___x_3619_, 1, v___f_3621_);
lean_ctor_set(v___x_3619_, 0, v___x_3625_);
v___x_3630_ = v___x_3619_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3625_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___f_3621_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v___f_3628_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v___f_3627_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v___f_3626_);
v___x_3630_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
lean_object* v___x_3632_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v___f_3622_);
lean_ctor_set(v___x_3612_, 0, v___x_3630_);
v___x_3632_ = v___x_3612_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___f_3622_);
v___x_3632_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v_toApplicative_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3689_; 
v___x_3633_ = l_StateRefT_x27_instMonad___redArg(v___x_3632_);
v_toApplicative_3634_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v___x_3633_, 1);
lean_dec(v_unused_3690_);
v___x_3636_ = v___x_3633_;
v_isShared_3637_ = v_isSharedCheck_3689_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_toApplicative_3634_);
lean_dec(v___x_3633_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3689_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v_toFunctor_3638_; lean_object* v_toSeq_3639_; lean_object* v_toSeqLeft_3640_; lean_object* v_toSeqRight_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3687_; 
v_toFunctor_3638_ = lean_ctor_get(v_toApplicative_3634_, 0);
v_toSeq_3639_ = lean_ctor_get(v_toApplicative_3634_, 2);
v_toSeqLeft_3640_ = lean_ctor_get(v_toApplicative_3634_, 3);
v_toSeqRight_3641_ = lean_ctor_get(v_toApplicative_3634_, 4);
v_isSharedCheck_3687_ = !lean_is_exclusive(v_toApplicative_3634_);
if (v_isSharedCheck_3687_ == 0)
{
lean_object* v_unused_3688_; 
v_unused_3688_ = lean_ctor_get(v_toApplicative_3634_, 1);
lean_dec(v_unused_3688_);
v___x_3643_ = v_toApplicative_3634_;
v_isShared_3644_ = v_isSharedCheck_3687_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_toSeqRight_3641_);
lean_inc(v_toSeqLeft_3640_);
lean_inc(v_toSeq_3639_);
lean_inc(v_toFunctor_3638_);
lean_dec(v_toApplicative_3634_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3687_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___f_3645_; lean_object* v___f_3646_; lean_object* v___f_3647_; lean_object* v___f_3648_; lean_object* v___x_3649_; lean_object* v___f_3650_; lean_object* v___f_3651_; lean_object* v___f_3652_; lean_object* v___x_3654_; 
v___f_3645_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__4));
v___f_3646_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___closed__5));
lean_inc_ref(v_toFunctor_3638_);
v___f_3647_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3647_, 0, v_toFunctor_3638_);
v___f_3648_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3648_, 0, v_toFunctor_3638_);
v___x_3649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___f_3647_);
lean_ctor_set(v___x_3649_, 1, v___f_3648_);
v___f_3650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3650_, 0, v_toSeqRight_3641_);
v___f_3651_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3651_, 0, v_toSeqLeft_3640_);
v___f_3652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3652_, 0, v_toSeq_3639_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set(v___x_3643_, 4, v___f_3650_);
lean_ctor_set(v___x_3643_, 3, v___f_3651_);
lean_ctor_set(v___x_3643_, 2, v___f_3652_);
lean_ctor_set(v___x_3643_, 1, v___f_3645_);
lean_ctor_set(v___x_3643_, 0, v___x_3649_);
v___x_3654_ = v___x_3643_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3649_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v___f_3645_);
lean_ctor_set(v_reuseFailAlloc_3686_, 2, v___f_3652_);
lean_ctor_set(v_reuseFailAlloc_3686_, 3, v___f_3651_);
lean_ctor_set(v_reuseFailAlloc_3686_, 4, v___f_3650_);
v___x_3654_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3656_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 1, v___f_3646_);
lean_ctor_set(v___x_3636_, 0, v___x_3654_);
v___x_3656_ = v___x_3636_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v___f_3646_);
v___x_3656_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; 
v___x_3657_ = lean_array_get_size(v_acc_3603_);
v___x_3658_ = lean_array_get_size(v_declInfos_3599_);
v___x_3659_ = lean_nat_dec_lt(v___x_3657_, v___x_3658_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; 
lean_dec_ref(v___x_3656_);
lean_dec(v_inst_3602_);
lean_dec_ref(v_declInfos_3599_);
lean_inc(v___y_3607_);
lean_inc_ref(v___y_3606_);
lean_inc(v___y_3605_);
lean_inc_ref(v___y_3604_);
v___x_3660_ = lean_apply_6(v_k_3600_, v_acc_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, lean_box(0));
return v___x_3660_;
}
else
{
lean_object* v___f_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; lean_object* v___f_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v_snd_3669_; lean_object* v_fst_3670_; lean_object* v_fst_3671_; lean_object* v_snd_3672_; lean_object* v___x_3673_; 
v___f_3661_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3661_, 0, v___x_3656_);
v___x_3662_ = lean_box(0);
v___x_3663_ = 0;
v___f_3664_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3664_, 0, v___f_3661_);
v___x_3665_ = lean_box(v___x_3663_);
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
lean_ctor_set(v___x_3666_, 1, v___f_3664_);
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3662_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = lean_array_get_borrowed(v___x_3667_, v_declInfos_3599_, v___x_3657_);
v_snd_3669_ = lean_ctor_get(v___x_3668_, 1);
v_fst_3670_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_fst_3670_);
v_fst_3671_ = lean_ctor_get(v_snd_3669_, 0);
v_snd_3672_ = lean_ctor_get(v_snd_3669_, 1);
lean_inc(v_snd_3672_);
lean_inc(v___y_3607_);
lean_inc_ref(v___y_3606_);
lean_inc(v___y_3605_);
lean_inc_ref(v___y_3604_);
lean_inc_ref(v_acc_3603_);
v___x_3673_ = lean_apply_6(v_snd_3672_, v_acc_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_, lean_box(0));
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; uint8_t v___x_3675_; lean_object* v___x_3676_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref(v___x_3673_);
v___x_3675_ = lean_unbox(v_fst_3671_);
v___x_3676_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(v_acc_3603_, v_declInfos_3599_, v_k_3600_, v_kind_3601_, v_inst_3602_, v_fst_3670_, v___x_3675_, v_a_3674_, v_kind_3601_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
return v___x_3676_;
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec(v_fst_3670_);
lean_dec_ref(v_acc_3603_);
lean_dec(v_inst_3602_);
lean_dec_ref(v_k_3600_);
lean_dec_ref(v_declInfos_3599_);
v_a_3677_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3673_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3673_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___lam__0(lean_object* v_acc_3697_, lean_object* v_declInfos_3698_, lean_object* v_k_3699_, uint8_t v_kind_3700_, lean_object* v_inst_3701_, lean_object* v_b_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = lean_array_push(v_acc_3697_, v_b_3702_);
v___x_3709_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_3698_, v_k_3699_, v_kind_3700_, v_inst_3701_, v___x_3708_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg___boxed(lean_object* v_acc_3710_, lean_object* v_declInfos_3711_, lean_object* v_k_3712_, lean_object* v_kind_3713_, lean_object* v_inst_3714_, lean_object* v_name_3715_, lean_object* v_bi_3716_, lean_object* v_type_3717_, lean_object* v_kind_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
uint8_t v_kind_boxed_3724_; uint8_t v_bi_boxed_3725_; uint8_t v_kind_boxed_3726_; lean_object* v_res_3727_; 
v_kind_boxed_3724_ = lean_unbox(v_kind_3713_);
v_bi_boxed_3725_ = lean_unbox(v_bi_3716_);
v_kind_boxed_3726_ = lean_unbox(v_kind_3718_);
v_res_3727_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(v_acc_3710_, v_declInfos_3711_, v_k_3712_, v_kind_boxed_3724_, v_inst_3714_, v_name_3715_, v_bi_boxed_3725_, v_type_3717_, v_kind_boxed_3726_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg___boxed(lean_object* v_declInfos_3728_, lean_object* v_k_3729_, lean_object* v_kind_3730_, lean_object* v_inst_3731_, lean_object* v_acc_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v_kind_boxed_3738_; lean_object* v_res_3739_; 
v_kind_boxed_3738_ = lean_unbox(v_kind_3730_);
v_res_3739_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_3728_, v_k_3729_, v_kind_boxed_3738_, v_inst_3731_, v_acc_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(lean_object* v_inst_3740_, lean_object* v_declInfos_3741_, lean_object* v_k_3742_, uint8_t v_kind_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise___lam__0___closed__0));
v___x_3750_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_3741_, v_k_3742_, v_kind_3743_, v_inst_3740_, v___x_3749_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg___boxed(lean_object* v_inst_3751_, lean_object* v_declInfos_3752_, lean_object* v_k_3753_, lean_object* v_kind_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v_kind_boxed_3760_; lean_object* v_res_3761_; 
v_kind_boxed_3760_ = lean_unbox(v_kind_3754_);
v_res_3761_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(v_inst_3751_, v_declInfos_3752_, v_k_3753_, v_kind_boxed_3760_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(lean_object* v_inst_3762_, lean_object* v_declInfos_3763_, lean_object* v_k_3764_, uint8_t v_kind_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
size_t v_sz_3771_; size_t v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v_sz_3771_ = lean_array_size(v_declInfos_3763_);
v___x_3772_ = ((size_t)0ULL);
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__7(v_sz_3771_, v___x_3772_, v_declInfos_3763_);
v___x_3774_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(v_inst_3762_, v___x_3773_, v_k_3764_, v_kind_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg___boxed(lean_object* v_inst_3775_, lean_object* v_declInfos_3776_, lean_object* v_k_3777_, lean_object* v_kind_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v_kind_boxed_3784_; lean_object* v_res_3785_; 
v_kind_boxed_3784_ = lean_unbox(v_kind_3778_);
v_res_3785_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(v_inst_3775_, v_declInfos_3776_, v_k_3777_, v_kind_boxed_3784_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3785_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3787_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__2));
v___x_3788_ = lean_unsigned_to_nat(4u);
v___x_3789_ = lean_unsigned_to_nat(202u);
v___x_3790_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__0));
v___x_3791_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__0));
v___x_3792_ = l_mkPanicMessageWithDecl(v___x_3791_, v___x_3790_, v___x_3789_, v___x_3788_, v___x_3787_);
return v___x_3792_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5(void){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__4));
v___x_3799_ = l_Lean_stringToMessageData(v___x_3798_);
return v___x_3799_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7(void){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__6));
v___x_3802_ = l_Lean_stringToMessageData(v___x_3801_);
return v___x_3802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(lean_object* v_nParams_3805_, lean_object* v_numMotives_3806_, lean_object* v_numMinors_3807_, lean_object* v___x_3808_, lean_object* v_all_3809_, lean_object* v_head_3810_, lean_object* v_tail_3811_, lean_object* v_recName_3812_, lean_object* v_brecOnGoName_3813_, lean_object* v_levelParams_3814_, lean_object* v_brecOnName_3815_, lean_object* v_brecOnEqName_3816_, lean_object* v_type_3817_, lean_object* v_refArgs_3818_, lean_object* v_refBody_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v___x_3825_ = lean_nat_add(v_nParams_3805_, v_numMotives_3806_);
v___x_3826_ = lean_nat_add(v___x_3825_, v_numMinors_3807_);
v___x_3827_ = lean_array_get_size(v_refArgs_3818_);
v___x_3828_ = lean_nat_dec_lt(v___x_3826_, v___x_3827_);
if (v___x_3828_ == 0)
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec(v___x_3826_);
lean_dec(v___x_3825_);
lean_dec_ref(v_refArgs_3818_);
lean_dec_ref(v_type_3817_);
lean_dec(v_brecOnEqName_3816_);
lean_dec(v_brecOnName_3815_);
lean_dec(v_levelParams_3814_);
lean_dec(v_brecOnGoName_3813_);
lean_dec(v_recName_3812_);
lean_dec(v_tail_3811_);
lean_dec(v_head_3810_);
lean_dec_ref(v_all_3809_);
lean_dec(v___x_3808_);
lean_dec(v_nParams_3805_);
v___x_3829_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__1);
v___x_3830_ = l_panic___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__0(v___x_3829_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
return v___x_3830_;
}
else
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3831_ = lean_unsigned_to_nat(0u);
lean_inc(v_nParams_3805_);
lean_inc_ref(v_refArgs_3818_);
v___x_3832_ = l_Array_toSubarray___redArg(v_refArgs_3818_, v___x_3831_, v_nParams_3805_);
lean_inc(v___x_3825_);
lean_inc_ref(v_refArgs_3818_);
v___x_3833_ = l_Array_toSubarray___redArg(v_refArgs_3818_, v_nParams_3805_, v___x_3825_);
v___x_3834_ = l_Subarray_copy___redArg(v___x_3833_);
v___x_3835_ = l_Lean_Expr_getAppFn(v_refBody_3819_);
v___x_3836_ = l_Array_idxOf_x3f___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__0(v___x_3834_, v___x_3835_);
lean_dec_ref(v___x_3835_);
if (lean_obj_tag(v___x_3836_) == 1)
{
lean_object* v_val_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
lean_dec_ref(v_type_3817_);
v_val_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_val_3837_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l_Lean_instInhabitedExpr;
v___x_3839_ = lean_unsigned_to_nat(1u);
v___x_3840_ = lean_nat_sub(v___x_3827_, v___x_3839_);
v___x_3841_ = lean_array_get(v___x_3838_, v_refArgs_3818_, v___x_3840_);
lean_inc(v___y_3823_);
lean_inc_ref(v___y_3822_);
lean_inc(v___y_3821_);
lean_inc_ref(v___y_3820_);
lean_inc(v___x_3841_);
v___x_3842_ = lean_infer_type(v___x_3841_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v___x_3844_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref(v___x_3842_);
lean_inc(v___y_3823_);
lean_inc_ref(v___y_3822_);
lean_inc(v___y_3821_);
lean_inc_ref(v___y_3820_);
v___x_3844_ = lean_infer_type(v_a_3843_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3846_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
v___x_3846_ = l_Lean_Meta_typeFormerTypeLevel(v_a_3845_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref(v___x_3846_);
if (lean_obj_tag(v_a_3847_) == 1)
{
lean_object* v_val_3848_; lean_object* v___x_3849_; lean_object* v___f_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; size_t v_sz_3860_; size_t v___x_3861_; lean_object* v___x_3862_; 
v_val_3848_ = lean_ctor_get(v_a_3847_, 0);
lean_inc(v_val_3848_);
lean_dec_ref(v_a_3847_);
v___x_3849_ = l_Subarray_copy___redArg(v___x_3832_);
lean_inc_ref(v___x_3834_);
lean_inc_ref(v___x_3849_);
lean_inc(v___x_3808_);
v___f_3850_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__0___boxed), 7, 6);
lean_closure_set(v___f_3850_, 0, v___x_3808_);
lean_closure_set(v___f_3850_, 1, v___x_3849_);
lean_closure_set(v___f_3850_, 2, v___x_3834_);
lean_closure_set(v___f_3850_, 3, v_all_3809_);
lean_closure_set(v___f_3850_, 4, v___x_3831_);
lean_closure_set(v___f_3850_, 5, v___x_3839_);
v___x_3851_ = lean_array_get_size(v___x_3834_);
v___x_3852_ = l_Array_ofFn___redArg(v___x_3851_, v___f_3850_);
v___x_3853_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__2));
v___x_3854_ = lean_array_get_size(v___x_3852_);
lean_inc_ref(v___x_3852_);
v___x_3855_ = l_Array_toSubarray___redArg(v___x_3852_, v___x_3831_, v___x_3854_);
v___x_3856_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__3));
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v___x_3851_);
lean_inc_ref(v___x_3855_);
v___x_3858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3855_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3853_);
lean_ctor_set(v___x_3859_, 1, v___x_3858_);
v_sz_3860_ = lean_array_size(v___x_3834_);
v___x_3861_ = ((size_t)0ULL);
v___x_3862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__1(v___x_3834_, v_sz_3860_, v___x_3861_, v___x_3859_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v_fst_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___f_3873_; lean_object* v___x_3874_; uint8_t v___x_3875_; lean_object* v___x_3876_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref(v___x_3862_);
v_fst_3864_ = lean_ctor_get(v_a_3863_, 0);
lean_inc(v_fst_3864_);
lean_dec(v_a_3863_);
lean_inc(v___x_3826_);
lean_inc_ref(v_refArgs_3818_);
v___x_3865_ = l_Array_toSubarray___redArg(v_refArgs_3818_, v___x_3825_, v___x_3826_);
v___x_3866_ = l_Subarray_copy___redArg(v___x_3865_);
v___x_3867_ = l_Array_toSubarray___redArg(v_refArgs_3818_, v___x_3826_, v___x_3840_);
v___x_3868_ = l_Subarray_copy___redArg(v___x_3867_);
v___x_3869_ = l_Lean_mkLevelMax(v_val_3848_, v_head_3810_);
v___x_3870_ = lean_box_usize(v_sz_3860_);
v___x_3871_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed__const__1));
v___x_3872_ = lean_box(v___x_3828_);
v___f_3873_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__1___boxed), 28, 22);
lean_closure_set(v___f_3873_, 0, v___x_3869_);
lean_closure_set(v___f_3873_, 1, v_tail_3811_);
lean_closure_set(v___f_3873_, 2, v_recName_3812_);
lean_closure_set(v___f_3873_, 3, v___x_3849_);
lean_closure_set(v___f_3873_, 4, v___x_3855_);
lean_closure_set(v___f_3873_, 5, v___x_3834_);
lean_closure_set(v___f_3873_, 6, v___x_3870_);
lean_closure_set(v___f_3873_, 7, v___x_3871_);
lean_closure_set(v___f_3873_, 8, v___x_3866_);
lean_closure_set(v___f_3873_, 9, v___x_3852_);
lean_closure_set(v___f_3873_, 10, v___x_3868_);
lean_closure_set(v___f_3873_, 11, v___x_3841_);
lean_closure_set(v___f_3873_, 12, v___x_3839_);
lean_closure_set(v___f_3873_, 13, v___x_3838_);
lean_closure_set(v___f_3873_, 14, v_val_3837_);
lean_closure_set(v___f_3873_, 15, v___x_3872_);
lean_closure_set(v___f_3873_, 16, v_brecOnGoName_3813_);
lean_closure_set(v___f_3873_, 17, v_levelParams_3814_);
lean_closure_set(v___f_3873_, 18, v___x_3808_);
lean_closure_set(v___f_3873_, 19, v_brecOnName_3815_);
lean_closure_set(v___f_3873_, 20, v___x_3831_);
lean_closure_set(v___f_3873_, 21, v_brecOnEqName_3816_);
v___x_3874_ = lean_box(0);
v___x_3875_ = 0;
v___x_3876_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(v___x_3874_, v_fst_3864_, v___f_3873_, v___x_3875_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
return v___x_3876_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v___x_3855_);
lean_dec_ref(v___x_3852_);
lean_dec_ref(v___x_3849_);
lean_dec(v_val_3848_);
lean_dec(v___x_3841_);
lean_dec(v___x_3840_);
lean_dec(v_val_3837_);
lean_dec_ref(v___x_3834_);
lean_dec(v___x_3826_);
lean_dec(v___x_3825_);
lean_dec_ref(v_refArgs_3818_);
lean_dec(v_brecOnEqName_3816_);
lean_dec(v_brecOnName_3815_);
lean_dec(v_levelParams_3814_);
lean_dec(v_brecOnGoName_3813_);
lean_dec(v_recName_3812_);
lean_dec(v_tail_3811_);
lean_dec(v_head_3810_);
lean_dec(v___x_3808_);
v_a_3877_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3862_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3862_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_dec(v_a_3847_);
lean_dec(v___x_3840_);
lean_dec(v_val_3837_);
lean_dec_ref(v___x_3834_);
lean_dec_ref(v___x_3832_);
lean_dec(v___x_3826_);
lean_dec(v___x_3825_);
lean_dec_ref(v_refArgs_3818_);
lean_dec(v_brecOnEqName_3816_);
lean_dec(v_brecOnName_3815_);
lean_dec(v_levelParams_3814_);
lean_dec(v_brecOnGoName_3813_);
lean_dec(v_recName_3812_);
lean_dec(v_tail_3811_);
lean_dec(v_head_3810_);
lean_dec_ref(v_all_3809_);
lean_dec(v___x_3808_);
v___x_3885_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__5);
v___x_3886_ = l_Lean_MessageData_ofExpr(v___x_3841_);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___lam__0___closed__7);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3889_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
return v___x_3890_;
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
lean_dec(v___x_3841_);
lean_dec(v___x_3840_);
lean_dec(v_val_3837_);
lean_dec_ref(v___x_3834_);
lean_dec_ref(v___x_3832_);
lean_dec(v___x_3826_);
lean_dec(v___x_3825_);
lean_dec_ref(v_refArgs_3818_);
lean_dec(v_brecOnEqName_3816_);
lean_dec(v_brecOnName_3815_);
lean_dec(v_levelParams_3814_);
lean_dec(v_brecOnGoName_3813_);
lean_dec(v_recName_3812_);
lean_dec(v_tail_3811_);
lean_dec(v_head_3810_);
lean_dec_ref(v_all_3809_);
lean_dec(v___x_3808_);
v_a_3891_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3846_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3846_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v___x_3841_);
lean_dec(v___x_3840_);
lean_dec(v_val_3837_);
lean_dec_ref(v___x_3834_);
lean_dec_ref(v___x_3832_);
lean_dec(v___x_3826_);
lean_dec(v___x_3825_);
lean_dec_ref(v_refArgs_3818_);
lean_dec(v_brecOnEqName_3816_);
lean_dec(v_brecOnName_3815_);
lean_dec(v_levelParams_3814_);
lean_dec(v_brecOnGoName_3813_);
lean_dec(v_recName_3812_);
lean_dec(v_tail_3811_);
lean_dec(v_head_3810_);
lean_dec_ref(v_all_3809_);
lean_dec(v___x_3808_);
v_a_3899_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3844_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3844_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
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
lean_dec(v___x_3841_);
lean_dec(v___x_3840_);
lean_dec(v_val_3837_);
lean_dec_ref(v___x_3834_);
lean_dec_ref(v___x_3832_);
lean_dec(v___x_3826_);
lean_dec(v___x_3825_);
lean_dec_ref(v_refArgs_3818_);
lean_dec(v_brecOnEqName_3816_);
lean_dec(v_brecOnName_3815_);
lean_dec(v_levelParams_3814_);
lean_dec(v_brecOnGoName_3813_);
lean_dec(v_recName_3812_);
lean_dec(v_tail_3811_);
lean_dec(v_head_3810_);
lean_dec_ref(v_all_3809_);
lean_dec(v___x_3808_);
v_a_3907_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3842_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3842_);
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
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_dec(v___x_3836_);
lean_dec_ref(v___x_3832_);
lean_dec(v___x_3826_);
lean_dec(v___x_3825_);
lean_dec_ref(v_refArgs_3818_);
lean_dec(v_brecOnEqName_3816_);
lean_dec(v_brecOnName_3815_);
lean_dec(v_levelParams_3814_);
lean_dec(v_brecOnGoName_3813_);
lean_dec(v_recName_3812_);
lean_dec(v_tail_3811_);
lean_dec(v_head_3810_);
lean_dec_ref(v_all_3809_);
lean_dec(v___x_3808_);
v___x_3915_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__5);
v___x_3916_ = l_Lean_MessageData_ofExpr(v_type_3817_);
v___x_3917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3915_);
lean_ctor_set(v___x_3917_, 1, v___x_3916_);
v___x_3918_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___closed__7);
v___x_3919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
v___x_3920_ = lean_array_to_list(v___x_3834_);
v___x_3921_ = lean_box(0);
v___x_3922_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBRecOnMinorPremise_go_spec__1(v___x_3920_, v___x_3921_);
v___x_3923_ = l_Lean_MessageData_ofList(v___x_3922_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3919_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___x_3925_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3924_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_);
return v___x_3925_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed(lean_object** _args){
lean_object* v_nParams_3926_ = _args[0];
lean_object* v_numMotives_3927_ = _args[1];
lean_object* v_numMinors_3928_ = _args[2];
lean_object* v___x_3929_ = _args[3];
lean_object* v_all_3930_ = _args[4];
lean_object* v_head_3931_ = _args[5];
lean_object* v_tail_3932_ = _args[6];
lean_object* v_recName_3933_ = _args[7];
lean_object* v_brecOnGoName_3934_ = _args[8];
lean_object* v_levelParams_3935_ = _args[9];
lean_object* v_brecOnName_3936_ = _args[10];
lean_object* v_brecOnEqName_3937_ = _args[11];
lean_object* v_type_3938_ = _args[12];
lean_object* v_refArgs_3939_ = _args[13];
lean_object* v_refBody_3940_ = _args[14];
lean_object* v___y_3941_ = _args[15];
lean_object* v___y_3942_ = _args[16];
lean_object* v___y_3943_ = _args[17];
lean_object* v___y_3944_ = _args[18];
lean_object* v___y_3945_ = _args[19];
_start:
{
lean_object* v_res_3946_; 
v_res_3946_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2(v_nParams_3926_, v_numMotives_3927_, v_numMinors_3928_, v___x_3929_, v_all_3930_, v_head_3931_, v_tail_3932_, v_recName_3933_, v_brecOnGoName_3934_, v_levelParams_3935_, v_brecOnName_3936_, v_brecOnEqName_3937_, v_type_3938_, v_refArgs_3939_, v_refBody_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec_ref(v_refBody_3940_);
lean_dec(v_numMinors_3928_);
lean_dec(v_numMotives_3927_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(lean_object* v_recName_3949_, lean_object* v_nParams_3950_, lean_object* v_all_3951_, lean_object* v_brecOnName_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
lean_object* v___x_3958_; 
lean_inc(v_recName_3949_);
v___x_3958_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_recName_3949_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3990_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3961_ = v___x_3958_;
v_isShared_3962_ = v_isSharedCheck_3990_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3958_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3990_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
if (lean_obj_tag(v_a_3959_) == 7)
{
lean_object* v_val_3963_; lean_object* v_toConstantVal_3964_; lean_object* v_numMotives_3965_; lean_object* v_numMinors_3966_; lean_object* v_levelParams_3967_; lean_object* v_type_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
lean_del_object(v___x_3961_);
v_val_3963_ = lean_ctor_get(v_a_3959_, 0);
lean_inc_ref(v_val_3963_);
lean_dec_ref(v_a_3959_);
v_toConstantVal_3964_ = lean_ctor_get(v_val_3963_, 0);
lean_inc_ref(v_toConstantVal_3964_);
v_numMotives_3965_ = lean_ctor_get(v_val_3963_, 4);
lean_inc(v_numMotives_3965_);
v_numMinors_3966_ = lean_ctor_get(v_val_3963_, 5);
lean_inc(v_numMinors_3966_);
lean_dec_ref(v_val_3963_);
v_levelParams_3967_ = lean_ctor_get(v_toConstantVal_3964_, 1);
lean_inc(v_levelParams_3967_);
v_type_3968_ = lean_ctor_get(v_toConstantVal_3964_, 2);
lean_inc_ref(v_type_3968_);
lean_dec_ref(v_toConstantVal_3964_);
v___x_3969_ = lean_box(0);
lean_inc(v_levelParams_3967_);
v___x_3970_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__1(v_levelParams_3967_, v___x_3969_);
if (lean_obj_tag(v___x_3970_) == 1)
{
lean_object* v_head_3971_; lean_object* v_tail_3972_; lean_object* v___x_3973_; lean_object* v_brecOnGoName_3974_; lean_object* v___x_3975_; lean_object* v_brecOnEqName_3976_; lean_object* v___f_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; 
v_head_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_head_3971_);
v_tail_3972_ = lean_ctor_get(v___x_3970_, 1);
lean_inc(v_tail_3972_);
v___x_3973_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__0));
lean_inc(v_brecOnName_3952_);
v_brecOnGoName_3974_ = l_Lean_Name_str___override(v_brecOnName_3952_, v___x_3973_);
v___x_3975_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___closed__1));
lean_inc(v_brecOnName_3952_);
v_brecOnEqName_3976_ = l_Lean_Name_str___override(v_brecOnName_3952_, v___x_3975_);
lean_inc_ref(v_type_3968_);
v___f_3977_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___lam__2___boxed), 20, 13);
lean_closure_set(v___f_3977_, 0, v_nParams_3950_);
lean_closure_set(v___f_3977_, 1, v_numMotives_3965_);
lean_closure_set(v___f_3977_, 2, v_numMinors_3966_);
lean_closure_set(v___f_3977_, 3, v___x_3970_);
lean_closure_set(v___f_3977_, 4, v_all_3951_);
lean_closure_set(v___f_3977_, 5, v_head_3971_);
lean_closure_set(v___f_3977_, 6, v_tail_3972_);
lean_closure_set(v___f_3977_, 7, v_recName_3949_);
lean_closure_set(v___f_3977_, 8, v_brecOnGoName_3974_);
lean_closure_set(v___f_3977_, 9, v_levelParams_3967_);
lean_closure_set(v___f_3977_, 10, v_brecOnName_3952_);
lean_closure_set(v___f_3977_, 11, v_brecOnEqName_3976_);
lean_closure_set(v___f_3977_, 12, v_type_3968_);
v___x_3978_ = 0;
v___x_3979_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__1___redArg(v_type_3968_, v___f_3977_, v___x_3978_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
return v___x_3979_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_dec(v___x_3970_);
lean_dec_ref(v_type_3968_);
lean_dec(v_levelParams_3967_);
lean_dec(v_numMinors_3966_);
lean_dec(v_numMotives_3965_);
lean_dec(v_brecOnName_3952_);
lean_dec_ref(v_all_3951_);
lean_dec(v_nParams_3950_);
v___x_3980_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__1);
v___x_3981_ = l_Lean_MessageData_ofName(v_recName_3949_);
v___x_3982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3_once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec___closed__3);
v___x_3984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3982_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = l_Lean_throwError___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__6___redArg(v___x_3984_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
return v___x_3985_;
}
}
else
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
lean_dec(v_a_3959_);
lean_dec(v_brecOnName_3952_);
lean_dec_ref(v_all_3951_);
lean_dec(v_nParams_3950_);
lean_dec(v_recName_3949_);
v___x_3986_ = lean_box(0);
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 0, v___x_3986_);
v___x_3988_ = v___x_3961_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec(v_brecOnName_3952_);
lean_dec_ref(v_all_3951_);
lean_dec(v_nParams_3950_);
lean_dec(v_recName_3949_);
v_a_3991_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3958_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3958_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec___boxed(lean_object* v_recName_3999_, lean_object* v_nParams_4000_, lean_object* v_all_4001_, lean_object* v_brecOnName_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v_recName_3999_, v_nParams_4000_, v_all_4001_, v_brecOnName_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(lean_object* v_00_u03b1_4009_, lean_object* v_inst_4010_, lean_object* v_declInfos_4011_, lean_object* v_k_4012_, uint8_t v_kind_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___redArg(v_inst_4010_, v_declInfos_4011_, v_k_4012_, v_kind_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7___boxed(lean_object* v_00_u03b1_4020_, lean_object* v_inst_4021_, lean_object* v_declInfos_4022_, lean_object* v_k_4023_, lean_object* v_kind_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
uint8_t v_kind_boxed_4030_; lean_object* v_res_4031_; 
v_kind_boxed_4030_ = lean_unbox(v_kind_4024_);
v_res_4031_ = l_Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7(v_00_u03b1_4020_, v_inst_4021_, v_declInfos_4022_, v_k_4023_, v_kind_boxed_4030_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(lean_object* v_00_u03b1_4032_, lean_object* v_inst_4033_, lean_object* v_declInfos_4034_, lean_object* v_k_4035_, uint8_t v_kind_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___redArg(v_inst_4033_, v_declInfos_4034_, v_k_4035_, v_kind_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4043_, lean_object* v_inst_4044_, lean_object* v_declInfos_4045_, lean_object* v_k_4046_, lean_object* v_kind_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
uint8_t v_kind_boxed_4053_; lean_object* v_res_4054_; 
v_kind_boxed_4053_ = lean_unbox(v_kind_4047_);
v_res_4054_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8(v_00_u03b1_4043_, v_inst_4044_, v_declInfos_4045_, v_k_4046_, v_kind_boxed_4053_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
return v_res_4054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(lean_object* v_00_u03b1_4055_, lean_object* v_acc_4056_, lean_object* v_declInfos_4057_, lean_object* v_k_4058_, uint8_t v_kind_4059_, lean_object* v_inst_4060_, lean_object* v_name_4061_, uint8_t v_bi_4062_, lean_object* v_type_4063_, uint8_t v_kind_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___redArg(v_acc_4056_, v_declInfos_4057_, v_k_4058_, v_kind_4059_, v_inst_4060_, v_name_4061_, v_bi_4062_, v_type_4063_, v_kind_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4071_, lean_object* v_acc_4072_, lean_object* v_declInfos_4073_, lean_object* v_k_4074_, lean_object* v_kind_4075_, lean_object* v_inst_4076_, lean_object* v_name_4077_, lean_object* v_bi_4078_, lean_object* v_type_4079_, lean_object* v_kind_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
uint8_t v_kind_boxed_4086_; uint8_t v_bi_boxed_4087_; uint8_t v_kind_boxed_4088_; lean_object* v_res_4089_; 
v_kind_boxed_4086_ = lean_unbox(v_kind_4075_);
v_bi_boxed_4087_ = lean_unbox(v_bi_4078_);
v_kind_boxed_4088_ = lean_unbox(v_kind_4080_);
v_res_4089_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_buildBelowMinorPremise_go_spec__2_spec__3___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9_spec__11(v_00_u03b1_4071_, v_acc_4072_, v_declInfos_4073_, v_k_4074_, v_kind_boxed_4086_, v_inst_4076_, v_name_4077_, v_bi_boxed_4087_, v_type_4079_, v_kind_boxed_4088_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(lean_object* v_00_u03b1_4090_, lean_object* v_declInfos_4091_, lean_object* v_k_4092_, uint8_t v_kind_4093_, lean_object* v_inst_4094_, lean_object* v_acc_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v___x_4101_; 
v___x_4101_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___redArg(v_declInfos_4091_, v_k_4092_, v_kind_4093_, v_inst_4094_, v_acc_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
return v___x_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9___boxed(lean_object* v_00_u03b1_4102_, lean_object* v_declInfos_4103_, lean_object* v_k_4104_, lean_object* v_kind_4105_, lean_object* v_inst_4106_, lean_object* v_acc_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
uint8_t v_kind_boxed_4113_; lean_object* v_res_4114_; 
v_kind_boxed_4113_ = lean_unbox(v_kind_4105_);
v_res_4114_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec_spec__7_spec__8_spec__9(v_00_u03b1_4102_, v_declInfos_4103_, v_k_4104_, v_kind_boxed_4113_, v_inst_4106_, v_acc_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(lean_object* v_upperBound_4115_, lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v___x_4118_, lean_object* v___x_4119_, lean_object* v_a_4120_, lean_object* v_b_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
uint8_t v___x_4127_; 
v___x_4127_ = lean_nat_dec_lt(v_a_4120_, v_upperBound_4115_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; 
lean_dec(v_a_4120_);
lean_dec_ref(v___x_4119_);
lean_dec(v___x_4118_);
lean_dec(v___x_4117_);
lean_dec(v___x_4116_);
v___x_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4128_, 0, v_b_4121_);
return v___x_4128_;
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4129_ = lean_unsigned_to_nat(1u);
v___x_4130_ = lean_nat_add(v_a_4120_, v___x_4129_);
lean_dec(v_a_4120_);
lean_inc(v___x_4130_);
lean_inc(v___x_4116_);
v___x_4131_ = lean_name_append_index_after(v___x_4116_, v___x_4130_);
lean_inc(v___x_4130_);
lean_inc(v___x_4117_);
v___x_4132_ = lean_name_append_index_after(v___x_4117_, v___x_4130_);
lean_inc_ref(v___x_4119_);
lean_inc(v___x_4118_);
v___x_4133_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4131_, v___x_4118_, v___x_4119_, v___x_4132_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v___x_4134_; 
lean_dec_ref(v___x_4133_);
v___x_4134_ = lean_box(0);
v_a_4120_ = v___x_4130_;
v_b_4121_ = v___x_4134_;
goto _start;
}
else
{
lean_dec(v___x_4130_);
lean_dec_ref(v___x_4119_);
lean_dec(v___x_4118_);
lean_dec(v___x_4117_);
lean_dec(v___x_4116_);
return v___x_4133_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg___boxed(lean_object* v_upperBound_4136_, lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v___x_4139_, lean_object* v___x_4140_, lean_object* v_a_4141_, lean_object* v_b_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4136_, v___x_4137_, v___x_4138_, v___x_4139_, v___x_4140_, v_a_4141_, v_b_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v_upperBound_4136_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn(lean_object* v_indName_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_options_4159_; uint8_t v_hasTrace_4160_; 
v_options_4159_ = lean_ctor_get(v_a_4156_, 2);
v_hasTrace_4160_ = lean_ctor_get_uint8(v_options_4159_, sizeof(void*)*1);
if (v_hasTrace_4160_ == 0)
{
lean_object* v___x_4161_; 
lean_inc(v_indName_4153_);
v___x_4161_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4227_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4164_ = v___x_4161_;
v_isShared_4165_ = v_isSharedCheck_4227_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4227_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
if (lean_obj_tag(v_a_4162_) == 5)
{
lean_object* v_val_4166_; uint8_t v_isRec_4167_; 
v_val_4166_ = lean_ctor_get(v_a_4162_, 0);
lean_inc_ref(v_val_4166_);
lean_dec_ref(v_a_4162_);
v_isRec_4167_ = lean_ctor_get_uint8(v_val_4166_, sizeof(void*)*6);
if (v_isRec_4167_ == 0)
{
lean_object* v___x_4168_; lean_object* v___x_4170_; 
lean_dec_ref(v_val_4166_);
lean_dec(v_indName_4153_);
v___x_4168_ = lean_box(0);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v___x_4168_);
v___x_4170_ = v___x_4164_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
else
{
lean_object* v_toConstantVal_4172_; lean_object* v_numParams_4173_; lean_object* v_all_4174_; lean_object* v_numNested_4175_; lean_object* v_type_4176_; lean_object* v___x_4177_; 
lean_del_object(v___x_4164_);
v_toConstantVal_4172_ = lean_ctor_get(v_val_4166_, 0);
lean_inc_ref(v_toConstantVal_4172_);
v_numParams_4173_ = lean_ctor_get(v_val_4166_, 1);
lean_inc(v_numParams_4173_);
v_all_4174_ = lean_ctor_get(v_val_4166_, 3);
lean_inc(v_all_4174_);
v_numNested_4175_ = lean_ctor_get(v_val_4166_, 5);
lean_inc(v_numNested_4175_);
lean_dec_ref(v_val_4166_);
v_type_4176_ = lean_ctor_get(v_toConstantVal_4172_, 2);
lean_inc_ref(v_type_4176_);
lean_dec_ref(v_toConstantVal_4172_);
v___x_4177_ = l_Lean_Meta_isPropFormerType(v_type_4176_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4177_) == 0)
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4214_; 
v_a_4178_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4180_ = v___x_4177_;
v_isShared_4181_ = v_isSharedCheck_4214_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4177_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4214_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
uint8_t v___x_4182_; 
v___x_4182_ = lean_unbox(v_a_4178_);
lean_dec(v_a_4178_);
if (v___x_4182_ == 0)
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
lean_del_object(v___x_4180_);
lean_inc(v_indName_4153_);
v___x_4183_ = l_Lean_mkRecName(v_indName_4153_);
lean_inc(v_indName_4153_);
v___x_4184_ = l_Lean_mkBRecOnName(v_indName_4153_);
lean_inc(v_all_4174_);
v___x_4185_ = lean_array_mk(v_all_4174_);
lean_inc(v___x_4184_);
lean_inc_ref(v___x_4185_);
lean_inc(v_numParams_4173_);
lean_inc(v___x_4183_);
v___x_4186_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4183_, v_numParams_4173_, v___x_4185_, v___x_4184_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4208_; 
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4208_ == 0)
{
lean_object* v_unused_4209_; 
v_unused_4209_ = lean_ctor_get(v___x_4186_, 0);
lean_dec(v_unused_4209_);
v___x_4188_ = v___x_4186_;
v_isShared_4189_ = v_isSharedCheck_4208_;
goto v_resetjp_4187_;
}
else
{
lean_dec(v___x_4186_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4208_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v___x_4190_ = lean_box(0);
v___x_4191_ = lean_unsigned_to_nat(0u);
v___x_4192_ = l_List_get_x21Internal___redArg(v___x_4190_, v_all_4174_, v___x_4191_);
lean_dec(v_all_4174_);
v___x_4193_ = lean_name_eq(v___x_4192_, v_indName_4153_);
lean_dec(v_indName_4153_);
lean_dec(v___x_4192_);
if (v___x_4193_ == 0)
{
lean_object* v___x_4194_; lean_object* v___x_4196_; 
lean_dec_ref(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec(v___x_4183_);
lean_dec(v_numNested_4175_);
lean_dec(v_numParams_4173_);
v___x_4194_ = lean_box(0);
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v___x_4194_);
v___x_4196_ = v___x_4188_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
else
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
lean_del_object(v___x_4188_);
v___x_4198_ = lean_box(0);
v___x_4199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4175_, v___x_4183_, v___x_4184_, v_numParams_4173_, v___x_4185_, v___x_4191_, v___x_4198_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_numNested_4175_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4206_ == 0)
{
lean_object* v_unused_4207_; 
v_unused_4207_ = lean_ctor_get(v___x_4199_, 0);
lean_dec(v_unused_4207_);
v___x_4201_ = v___x_4199_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_dec(v___x_4199_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
lean_ctor_set(v___x_4201_, 0, v___x_4198_);
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v___x_4198_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
else
{
return v___x_4199_;
}
}
}
}
else
{
lean_dec_ref(v___x_4185_);
lean_dec(v___x_4184_);
lean_dec(v___x_4183_);
lean_dec(v_numNested_4175_);
lean_dec(v_all_4174_);
lean_dec(v_numParams_4173_);
lean_dec(v_indName_4153_);
return v___x_4186_;
}
}
else
{
lean_object* v___x_4210_; lean_object* v___x_4212_; 
lean_dec(v_numNested_4175_);
lean_dec(v_all_4174_);
lean_dec(v_numParams_4173_);
lean_dec(v_indName_4153_);
v___x_4210_ = lean_box(0);
if (v_isShared_4181_ == 0)
{
lean_ctor_set(v___x_4180_, 0, v___x_4210_);
v___x_4212_ = v___x_4180_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec(v_numNested_4175_);
lean_dec(v_all_4174_);
lean_dec(v_numParams_4173_);
lean_dec(v_indName_4153_);
v_a_4215_ = lean_ctor_get(v___x_4177_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4177_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4177_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4177_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4225_; 
lean_dec(v_a_4162_);
lean_dec(v_indName_4153_);
v___x_4223_ = lean_box(0);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v___x_4223_);
v___x_4225_ = v___x_4164_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
else
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
lean_dec(v_indName_4153_);
v_a_4228_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4161_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4161_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
return v___x_4233_;
}
}
}
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4442_; 
v___x_4236_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4237_ = l_Lean_isTracingEnabledFor___at___00Lean_mkBelow_spec__1___redArg(v___x_4236_, v_a_4156_);
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4442_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4240_ = v___x_4237_;
v_isShared_4241_ = v_isSharedCheck_4442_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4237_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4442_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___f_4242_; lean_object* v___x_4243_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v_a_4247_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v_a_4263_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v_a_4270_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v_a_4275_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v_a_4288_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v_a_4293_; uint8_t v___x_4364_; 
lean_inc(v_indName_4153_);
v___f_4242_ = lean_alloc_closure((void*)(l_Lean_mkBelow___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4242_, 0, v_indName_4153_);
v___x_4243_ = ((lean_object*)(l_Lean_mkBelow___closed__3));
v___x_4364_ = lean_unbox(v_a_4238_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; uint8_t v___x_4366_; 
v___x_4365_ = l_Lean_trace_profiler;
v___x_4366_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_4159_, v___x_4365_);
if (v___x_4366_ == 0)
{
lean_object* v___x_4367_; 
lean_dec_ref(v___f_4242_);
lean_del_object(v___x_4240_);
lean_dec(v_a_4238_);
lean_inc(v_indName_4153_);
v___x_4367_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4433_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4433_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4433_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
if (lean_obj_tag(v_a_4368_) == 5)
{
lean_object* v_val_4372_; uint8_t v_isRec_4373_; 
v_val_4372_ = lean_ctor_get(v_a_4368_, 0);
lean_inc_ref(v_val_4372_);
lean_dec_ref(v_a_4368_);
v_isRec_4373_ = lean_ctor_get_uint8(v_val_4372_, sizeof(void*)*6);
if (v_isRec_4373_ == 0)
{
lean_object* v___x_4374_; lean_object* v___x_4376_; 
lean_dec_ref(v_val_4372_);
lean_dec(v_indName_4153_);
v___x_4374_ = lean_box(0);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4374_);
v___x_4376_ = v___x_4370_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v___x_4374_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
else
{
lean_object* v_toConstantVal_4378_; lean_object* v_numParams_4379_; lean_object* v_all_4380_; lean_object* v_numNested_4381_; lean_object* v_type_4382_; lean_object* v___x_4383_; 
lean_del_object(v___x_4370_);
v_toConstantVal_4378_ = lean_ctor_get(v_val_4372_, 0);
lean_inc_ref(v_toConstantVal_4378_);
v_numParams_4379_ = lean_ctor_get(v_val_4372_, 1);
lean_inc(v_numParams_4379_);
v_all_4380_ = lean_ctor_get(v_val_4372_, 3);
lean_inc(v_all_4380_);
v_numNested_4381_ = lean_ctor_get(v_val_4372_, 5);
lean_inc(v_numNested_4381_);
lean_dec_ref(v_val_4372_);
v_type_4382_ = lean_ctor_get(v_toConstantVal_4378_, 2);
lean_inc_ref(v_type_4382_);
lean_dec_ref(v_toConstantVal_4378_);
v___x_4383_ = l_Lean_Meta_isPropFormerType(v_type_4382_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; lean_object* v___x_4386_; uint8_t v_isShared_4387_; uint8_t v_isSharedCheck_4420_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4386_ = v___x_4383_;
v_isShared_4387_ = v_isSharedCheck_4420_;
goto v_resetjp_4385_;
}
else
{
lean_inc(v_a_4384_);
lean_dec(v___x_4383_);
v___x_4386_ = lean_box(0);
v_isShared_4387_ = v_isSharedCheck_4420_;
goto v_resetjp_4385_;
}
v_resetjp_4385_:
{
uint8_t v___x_4388_; 
v___x_4388_ = lean_unbox(v_a_4384_);
lean_dec(v_a_4384_);
if (v___x_4388_ == 0)
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
lean_del_object(v___x_4386_);
lean_inc(v_indName_4153_);
v___x_4389_ = l_Lean_mkRecName(v_indName_4153_);
lean_inc(v_indName_4153_);
v___x_4390_ = l_Lean_mkBRecOnName(v_indName_4153_);
lean_inc(v_all_4380_);
v___x_4391_ = lean_array_mk(v_all_4380_);
lean_inc(v___x_4390_);
lean_inc_ref(v___x_4391_);
lean_inc(v_numParams_4379_);
lean_inc(v___x_4389_);
v___x_4392_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4389_, v_numParams_4379_, v___x_4391_, v___x_4390_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4414_; 
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; 
v_unused_4415_ = lean_ctor_get(v___x_4392_, 0);
lean_dec(v_unused_4415_);
v___x_4394_ = v___x_4392_;
v_isShared_4395_ = v_isSharedCheck_4414_;
goto v_resetjp_4393_;
}
else
{
lean_dec(v___x_4392_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4414_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v___x_4396_ = lean_box(0);
v___x_4397_ = lean_unsigned_to_nat(0u);
v___x_4398_ = l_List_get_x21Internal___redArg(v___x_4396_, v_all_4380_, v___x_4397_);
lean_dec(v_all_4380_);
v___x_4399_ = lean_name_eq(v___x_4398_, v_indName_4153_);
lean_dec(v_indName_4153_);
lean_dec(v___x_4398_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
lean_dec_ref(v___x_4391_);
lean_dec(v___x_4390_);
lean_dec(v___x_4389_);
lean_dec(v_numNested_4381_);
lean_dec(v_numParams_4379_);
v___x_4400_ = lean_box(0);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v___x_4400_);
v___x_4402_ = v___x_4394_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v___x_4400_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
else
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
lean_del_object(v___x_4394_);
v___x_4404_ = lean_box(0);
v___x_4405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4381_, v___x_4389_, v___x_4390_, v_numParams_4379_, v___x_4391_, v___x_4397_, v___x_4404_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_numNested_4381_);
if (lean_obj_tag(v___x_4405_) == 0)
{
lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4412_; 
v_isSharedCheck_4412_ = !lean_is_exclusive(v___x_4405_);
if (v_isSharedCheck_4412_ == 0)
{
lean_object* v_unused_4413_; 
v_unused_4413_ = lean_ctor_get(v___x_4405_, 0);
lean_dec(v_unused_4413_);
v___x_4407_ = v___x_4405_;
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
else
{
lean_dec(v___x_4405_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4412_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4410_; 
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v___x_4404_);
v___x_4410_ = v___x_4407_;
goto v_reusejp_4409_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4404_);
v___x_4410_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4409_;
}
v_reusejp_4409_:
{
return v___x_4410_;
}
}
}
else
{
return v___x_4405_;
}
}
}
}
else
{
lean_dec_ref(v___x_4391_);
lean_dec(v___x_4390_);
lean_dec(v___x_4389_);
lean_dec(v_numNested_4381_);
lean_dec(v_all_4380_);
lean_dec(v_numParams_4379_);
lean_dec(v_indName_4153_);
return v___x_4392_;
}
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4418_; 
lean_dec(v_numNested_4381_);
lean_dec(v_all_4380_);
lean_dec(v_numParams_4379_);
lean_dec(v_indName_4153_);
v___x_4416_ = lean_box(0);
if (v_isShared_4387_ == 0)
{
lean_ctor_set(v___x_4386_, 0, v___x_4416_);
v___x_4418_ = v___x_4386_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v___x_4416_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
else
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4428_; 
lean_dec(v_numNested_4381_);
lean_dec(v_all_4380_);
lean_dec(v_numParams_4379_);
lean_dec(v_indName_4153_);
v_a_4421_ = lean_ctor_get(v___x_4383_, 0);
v_isSharedCheck_4428_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4428_ == 0)
{
v___x_4423_ = v___x_4383_;
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4383_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4428_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4426_; 
if (v_isShared_4424_ == 0)
{
v___x_4426_ = v___x_4423_;
goto v_reusejp_4425_;
}
else
{
lean_object* v_reuseFailAlloc_4427_; 
v_reuseFailAlloc_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4427_, 0, v_a_4421_);
v___x_4426_ = v_reuseFailAlloc_4427_;
goto v_reusejp_4425_;
}
v_reusejp_4425_:
{
return v___x_4426_;
}
}
}
}
}
else
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
lean_dec(v_a_4368_);
lean_dec(v_indName_4153_);
v___x_4429_ = lean_box(0);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4429_);
v___x_4431_ = v___x_4370_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v___x_4429_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec(v_indName_4153_);
v_a_4434_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4367_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4367_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
else
{
goto v___jp_4295_;
}
}
else
{
goto v___jp_4295_;
}
v___jp_4244_:
{
lean_object* v___x_4248_; double v___x_4249_; double v___x_4250_; double v___x_4251_; double v___x_4252_; double v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; lean_object* v___x_4259_; 
v___x_4248_ = lean_io_mono_nanos_now();
v___x_4249_ = lean_float_of_nat(v___y_4246_);
v___x_4250_ = lean_float_once(&l_Lean_mkBelow___closed__4, &l_Lean_mkBelow___closed__4_once, _init_l_Lean_mkBelow___closed__4);
v___x_4251_ = lean_float_div(v___x_4249_, v___x_4250_);
v___x_4252_ = lean_float_of_nat(v___x_4248_);
v___x_4253_ = lean_float_div(v___x_4252_, v___x_4250_);
v___x_4254_ = lean_box_float(v___x_4251_);
v___x_4255_ = lean_box_float(v___x_4253_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4254_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4257_, 0, v_a_4247_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = lean_unbox(v_a_4238_);
lean_dec(v_a_4238_);
v___x_4259_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_4236_, v_hasTrace_4160_, v___x_4243_, v_options_4159_, v___x_4258_, v___y_4245_, v___f_4242_, v___x_4257_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
return v___x_4259_;
}
v___jp_4260_:
{
lean_object* v___x_4265_; 
if (v_isShared_4241_ == 0)
{
lean_ctor_set_tag(v___x_4240_, 1);
lean_ctor_set(v___x_4240_, 0, v_a_4263_);
v___x_4265_ = v___x_4240_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
v___y_4245_ = v___y_4261_;
v___y_4246_ = v___y_4262_;
v_a_4247_ = v___x_4265_;
goto v___jp_4244_;
}
}
v___jp_4267_:
{
lean_object* v___x_4271_; 
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v_a_4270_);
v___y_4245_ = v___y_4268_;
v___y_4246_ = v___y_4269_;
v_a_4247_ = v___x_4271_;
goto v___jp_4244_;
}
v___jp_4272_:
{
lean_object* v___x_4276_; double v___x_4277_; double v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; 
v___x_4276_ = lean_io_get_num_heartbeats();
v___x_4277_ = lean_float_of_nat(v___y_4274_);
v___x_4278_ = lean_float_of_nat(v___x_4276_);
v___x_4279_ = lean_box_float(v___x_4277_);
v___x_4280_ = lean_box_float(v___x_4278_);
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4279_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4282_, 0, v_a_4275_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
v___x_4283_ = lean_unbox(v_a_4238_);
lean_dec(v_a_4238_);
v___x_4284_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkBelow_spec__4(v___x_4236_, v_hasTrace_4160_, v___x_4243_, v_options_4159_, v___x_4283_, v___y_4273_, v___f_4242_, v___x_4282_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
return v___x_4284_;
}
v___jp_4285_:
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4289_, 0, v_a_4288_);
v___y_4273_ = v___y_4286_;
v___y_4274_ = v___y_4287_;
v_a_4275_ = v___x_4289_;
goto v___jp_4272_;
}
v___jp_4290_:
{
lean_object* v___x_4294_; 
v___x_4294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4294_, 0, v_a_4293_);
v___y_4273_ = v___y_4291_;
v___y_4274_ = v___y_4292_;
v_a_4275_ = v___x_4294_;
goto v___jp_4272_;
}
v___jp_4295_:
{
lean_object* v___x_4296_; lean_object* v_a_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v___x_4296_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkBelow_spec__2___redArg(v_a_4157_);
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref(v___x_4296_);
v___x_4298_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4299_ = l_Lean_Option_get___at___00Lean_mkBelow_spec__3(v_options_4159_, v___x_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4300_ = lean_io_mono_nanos_now();
lean_inc(v_indName_4153_);
v___x_4301_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref(v___x_4301_);
if (lean_obj_tag(v_a_4302_) == 5)
{
lean_object* v_val_4303_; uint8_t v_isRec_4304_; 
v_val_4303_ = lean_ctor_get(v_a_4302_, 0);
lean_inc_ref(v_val_4303_);
lean_dec_ref(v_a_4302_);
v_isRec_4304_ = lean_ctor_get_uint8(v_val_4303_, sizeof(void*)*6);
if (v_isRec_4304_ == 0)
{
lean_object* v___x_4305_; 
lean_dec_ref(v_val_4303_);
lean_dec(v_indName_4153_);
v___x_4305_ = lean_box(0);
v___y_4261_ = v_a_4297_;
v___y_4262_ = v___x_4300_;
v_a_4263_ = v___x_4305_;
goto v___jp_4260_;
}
else
{
lean_object* v_toConstantVal_4306_; lean_object* v_numParams_4307_; lean_object* v_all_4308_; lean_object* v_numNested_4309_; lean_object* v_type_4310_; lean_object* v___x_4311_; 
v_toConstantVal_4306_ = lean_ctor_get(v_val_4303_, 0);
lean_inc_ref(v_toConstantVal_4306_);
v_numParams_4307_ = lean_ctor_get(v_val_4303_, 1);
lean_inc(v_numParams_4307_);
v_all_4308_ = lean_ctor_get(v_val_4303_, 3);
lean_inc(v_all_4308_);
v_numNested_4309_ = lean_ctor_get(v_val_4303_, 5);
lean_inc(v_numNested_4309_);
lean_dec_ref(v_val_4303_);
v_type_4310_ = lean_ctor_get(v_toConstantVal_4306_, 2);
lean_inc_ref(v_type_4310_);
lean_dec_ref(v_toConstantVal_4306_);
v___x_4311_ = l_Lean_Meta_isPropFormerType(v_type_4310_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; uint8_t v___x_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref(v___x_4311_);
v___x_4313_ = lean_unbox(v_a_4312_);
lean_dec(v_a_4312_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
lean_inc(v_indName_4153_);
v___x_4314_ = l_Lean_mkRecName(v_indName_4153_);
lean_inc(v_indName_4153_);
v___x_4315_ = l_Lean_mkBRecOnName(v_indName_4153_);
lean_inc(v_all_4308_);
v___x_4316_ = lean_array_mk(v_all_4308_);
lean_inc(v___x_4315_);
lean_inc_ref(v___x_4316_);
lean_inc(v_numParams_4307_);
lean_inc(v___x_4314_);
v___x_4317_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4314_, v_numParams_4307_, v___x_4316_, v___x_4315_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; uint8_t v___x_4321_; 
lean_dec_ref(v___x_4317_);
v___x_4318_ = lean_box(0);
v___x_4319_ = lean_unsigned_to_nat(0u);
v___x_4320_ = l_List_get_x21Internal___redArg(v___x_4318_, v_all_4308_, v___x_4319_);
lean_dec(v_all_4308_);
v___x_4321_ = lean_name_eq(v___x_4320_, v_indName_4153_);
lean_dec(v_indName_4153_);
lean_dec(v___x_4320_);
if (v___x_4321_ == 0)
{
lean_object* v___x_4322_; 
lean_dec_ref(v___x_4316_);
lean_dec(v___x_4315_);
lean_dec(v___x_4314_);
lean_dec(v_numNested_4309_);
lean_dec(v_numParams_4307_);
v___x_4322_ = lean_box(0);
v___y_4261_ = v_a_4297_;
v___y_4262_ = v___x_4300_;
v_a_4263_ = v___x_4322_;
goto v___jp_4260_;
}
else
{
lean_object* v___x_4323_; lean_object* v___x_4324_; 
v___x_4323_ = lean_box(0);
v___x_4324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4309_, v___x_4314_, v___x_4315_, v_numParams_4307_, v___x_4316_, v___x_4319_, v___x_4323_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_numNested_4309_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_dec_ref(v___x_4324_);
v___y_4261_ = v_a_4297_;
v___y_4262_ = v___x_4300_;
v_a_4263_ = v___x_4323_;
goto v___jp_4260_;
}
else
{
lean_object* v_a_4325_; 
lean_del_object(v___x_4240_);
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
lean_inc(v_a_4325_);
lean_dec_ref(v___x_4324_);
v___y_4268_ = v_a_4297_;
v___y_4269_ = v___x_4300_;
v_a_4270_ = v_a_4325_;
goto v___jp_4267_;
}
}
}
else
{
lean_dec_ref(v___x_4316_);
lean_dec(v___x_4315_);
lean_dec(v___x_4314_);
lean_dec(v_numNested_4309_);
lean_dec(v_all_4308_);
lean_dec(v_numParams_4307_);
lean_dec(v_indName_4153_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4326_; 
v_a_4326_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4326_);
lean_dec_ref(v___x_4317_);
v___y_4261_ = v_a_4297_;
v___y_4262_ = v___x_4300_;
v_a_4263_ = v_a_4326_;
goto v___jp_4260_;
}
else
{
lean_object* v_a_4327_; 
lean_del_object(v___x_4240_);
v_a_4327_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4327_);
lean_dec_ref(v___x_4317_);
v___y_4268_ = v_a_4297_;
v___y_4269_ = v___x_4300_;
v_a_4270_ = v_a_4327_;
goto v___jp_4267_;
}
}
}
else
{
lean_object* v___x_4328_; 
lean_dec(v_numNested_4309_);
lean_dec(v_all_4308_);
lean_dec(v_numParams_4307_);
lean_dec(v_indName_4153_);
v___x_4328_ = lean_box(0);
v___y_4261_ = v_a_4297_;
v___y_4262_ = v___x_4300_;
v_a_4263_ = v___x_4328_;
goto v___jp_4260_;
}
}
else
{
lean_object* v_a_4329_; 
lean_dec(v_numNested_4309_);
lean_dec(v_all_4308_);
lean_dec(v_numParams_4307_);
lean_del_object(v___x_4240_);
lean_dec(v_indName_4153_);
v_a_4329_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4329_);
lean_dec_ref(v___x_4311_);
v___y_4268_ = v_a_4297_;
v___y_4269_ = v___x_4300_;
v_a_4270_ = v_a_4329_;
goto v___jp_4267_;
}
}
}
else
{
lean_object* v___x_4330_; 
lean_dec(v_a_4302_);
lean_dec(v_indName_4153_);
v___x_4330_ = lean_box(0);
v___y_4261_ = v_a_4297_;
v___y_4262_ = v___x_4300_;
v_a_4263_ = v___x_4330_;
goto v___jp_4260_;
}
}
else
{
lean_object* v_a_4331_; 
lean_del_object(v___x_4240_);
lean_dec(v_indName_4153_);
v_a_4331_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4331_);
lean_dec_ref(v___x_4301_);
v___y_4268_ = v_a_4297_;
v___y_4269_ = v___x_4300_;
v_a_4270_ = v_a_4331_;
goto v___jp_4267_;
}
}
else
{
lean_object* v___x_4332_; lean_object* v___x_4333_; 
lean_del_object(v___x_4240_);
v___x_4332_ = lean_io_get_num_heartbeats();
lean_inc(v_indName_4153_);
v___x_4333_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBelowFromRec_spec__0(v_indName_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4333_) == 0)
{
lean_object* v_a_4334_; 
v_a_4334_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4334_);
lean_dec_ref(v___x_4333_);
if (lean_obj_tag(v_a_4334_) == 5)
{
lean_object* v_val_4335_; uint8_t v_isRec_4336_; 
v_val_4335_ = lean_ctor_get(v_a_4334_, 0);
lean_inc_ref(v_val_4335_);
lean_dec_ref(v_a_4334_);
v_isRec_4336_ = lean_ctor_get_uint8(v_val_4335_, sizeof(void*)*6);
if (v_isRec_4336_ == 0)
{
lean_object* v___x_4337_; 
lean_dec_ref(v_val_4335_);
lean_dec(v_indName_4153_);
v___x_4337_ = lean_box(0);
v___y_4286_ = v_a_4297_;
v___y_4287_ = v___x_4332_;
v_a_4288_ = v___x_4337_;
goto v___jp_4285_;
}
else
{
lean_object* v_toConstantVal_4338_; lean_object* v_numParams_4339_; lean_object* v_all_4340_; lean_object* v_numNested_4341_; lean_object* v_type_4342_; lean_object* v___x_4343_; 
v_toConstantVal_4338_ = lean_ctor_get(v_val_4335_, 0);
lean_inc_ref(v_toConstantVal_4338_);
v_numParams_4339_ = lean_ctor_get(v_val_4335_, 1);
lean_inc(v_numParams_4339_);
v_all_4340_ = lean_ctor_get(v_val_4335_, 3);
lean_inc(v_all_4340_);
v_numNested_4341_ = lean_ctor_get(v_val_4335_, 5);
lean_inc(v_numNested_4341_);
lean_dec_ref(v_val_4335_);
v_type_4342_ = lean_ctor_get(v_toConstantVal_4338_, 2);
lean_inc_ref(v_type_4342_);
lean_dec_ref(v_toConstantVal_4338_);
v___x_4343_ = l_Lean_Meta_isPropFormerType(v_type_4342_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4343_) == 0)
{
lean_object* v_a_4344_; uint8_t v___x_4345_; 
v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4344_);
lean_dec_ref(v___x_4343_);
v___x_4345_ = lean_unbox(v_a_4344_);
lean_dec(v_a_4344_);
if (v___x_4345_ == 0)
{
lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
lean_inc(v_indName_4153_);
v___x_4346_ = l_Lean_mkRecName(v_indName_4153_);
lean_inc(v_indName_4153_);
v___x_4347_ = l_Lean_mkBRecOnName(v_indName_4153_);
lean_inc(v_all_4340_);
v___x_4348_ = lean_array_mk(v_all_4340_);
lean_inc(v___x_4347_);
lean_inc_ref(v___x_4348_);
lean_inc(v_numParams_4339_);
lean_inc(v___x_4346_);
v___x_4349_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_mkBRecOnFromRec(v___x_4346_, v_numParams_4339_, v___x_4348_, v___x_4347_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
lean_dec_ref(v___x_4349_);
v___x_4350_ = lean_box(0);
v___x_4351_ = lean_unsigned_to_nat(0u);
v___x_4352_ = l_List_get_x21Internal___redArg(v___x_4350_, v_all_4340_, v___x_4351_);
lean_dec(v_all_4340_);
v___x_4353_ = lean_name_eq(v___x_4352_, v_indName_4153_);
lean_dec(v_indName_4153_);
lean_dec(v___x_4352_);
if (v___x_4353_ == 0)
{
lean_object* v___x_4354_; 
lean_dec_ref(v___x_4348_);
lean_dec(v___x_4347_);
lean_dec(v___x_4346_);
lean_dec(v_numNested_4341_);
lean_dec(v_numParams_4339_);
v___x_4354_ = lean_box(0);
v___y_4286_ = v_a_4297_;
v___y_4287_ = v___x_4332_;
v_a_4288_ = v___x_4354_;
goto v___jp_4285_;
}
else
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = lean_box(0);
v___x_4356_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_numNested_4341_, v___x_4346_, v___x_4347_, v_numParams_4339_, v___x_4348_, v___x_4351_, v___x_4355_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_numNested_4341_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_dec_ref(v___x_4356_);
v___y_4286_ = v_a_4297_;
v___y_4287_ = v___x_4332_;
v_a_4288_ = v___x_4355_;
goto v___jp_4285_;
}
else
{
lean_object* v_a_4357_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref(v___x_4356_);
v___y_4291_ = v_a_4297_;
v___y_4292_ = v___x_4332_;
v_a_4293_ = v_a_4357_;
goto v___jp_4290_;
}
}
}
else
{
lean_dec_ref(v___x_4348_);
lean_dec(v___x_4347_);
lean_dec(v___x_4346_);
lean_dec(v_numNested_4341_);
lean_dec(v_all_4340_);
lean_dec(v_numParams_4339_);
lean_dec(v_indName_4153_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4358_; 
v_a_4358_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4358_);
lean_dec_ref(v___x_4349_);
v___y_4286_ = v_a_4297_;
v___y_4287_ = v___x_4332_;
v_a_4288_ = v_a_4358_;
goto v___jp_4285_;
}
else
{
lean_object* v_a_4359_; 
v_a_4359_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4359_);
lean_dec_ref(v___x_4349_);
v___y_4291_ = v_a_4297_;
v___y_4292_ = v___x_4332_;
v_a_4293_ = v_a_4359_;
goto v___jp_4290_;
}
}
}
else
{
lean_object* v___x_4360_; 
lean_dec(v_numNested_4341_);
lean_dec(v_all_4340_);
lean_dec(v_numParams_4339_);
lean_dec(v_indName_4153_);
v___x_4360_ = lean_box(0);
v___y_4286_ = v_a_4297_;
v___y_4287_ = v___x_4332_;
v_a_4288_ = v___x_4360_;
goto v___jp_4285_;
}
}
else
{
lean_object* v_a_4361_; 
lean_dec(v_numNested_4341_);
lean_dec(v_all_4340_);
lean_dec(v_numParams_4339_);
lean_dec(v_indName_4153_);
v_a_4361_ = lean_ctor_get(v___x_4343_, 0);
lean_inc(v_a_4361_);
lean_dec_ref(v___x_4343_);
v___y_4291_ = v_a_4297_;
v___y_4292_ = v___x_4332_;
v_a_4293_ = v_a_4361_;
goto v___jp_4290_;
}
}
}
else
{
lean_object* v___x_4362_; 
lean_dec(v_a_4334_);
lean_dec(v_indName_4153_);
v___x_4362_ = lean_box(0);
v___y_4286_ = v_a_4297_;
v___y_4287_ = v___x_4332_;
v_a_4288_ = v___x_4362_;
goto v___jp_4285_;
}
}
else
{
lean_object* v_a_4363_; 
lean_dec(v_indName_4153_);
v_a_4363_ = lean_ctor_get(v___x_4333_, 0);
lean_inc(v_a_4363_);
lean_dec_ref(v___x_4333_);
v___y_4291_ = v_a_4297_;
v___y_4292_ = v___x_4332_;
v_a_4293_ = v_a_4363_;
goto v___jp_4290_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkBRecOn___boxed(lean_object* v_indName_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l_Lean_mkBRecOn(v_indName_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(lean_object* v_upperBound_4450_, lean_object* v___x_4451_, lean_object* v___x_4452_, lean_object* v___x_4453_, lean_object* v___x_4454_, lean_object* v_inst_4455_, lean_object* v_R_4456_, lean_object* v_a_4457_, lean_object* v_b_4458_, lean_object* v_c_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v___x_4465_; 
v___x_4465_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___redArg(v_upperBound_4450_, v___x_4451_, v___x_4452_, v___x_4453_, v___x_4454_, v_a_4457_, v_b_4458_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
return v___x_4465_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0___boxed(lean_object* v_upperBound_4466_, lean_object* v___x_4467_, lean_object* v___x_4468_, lean_object* v___x_4469_, lean_object* v___x_4470_, lean_object* v_inst_4471_, lean_object* v_R_4472_, lean_object* v_a_4473_, lean_object* v_b_4474_, lean_object* v_c_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v_res_4481_; 
v_res_4481_ = l_WellFounded_opaqueFix_u2083___at___00Lean_mkBRecOn_spec__0(v_upperBound_4466_, v___x_4467_, v___x_4468_, v___x_4469_, v___x_4470_, v_inst_4471_, v_R_4472_, v_a_4473_, v_b_4474_, v_c_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v_upperBound_4466_);
return v_res_4481_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = lean_unsigned_to_nat(2304625798u);
v___x_4528_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4529_ = l_Lean_Name_num___override(v___x_4528_, v___x_4527_);
return v___x_4529_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4531_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4532_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4533_ = l_Lean_Name_str___override(v___x_4532_, v___x_4531_);
return v___x_4533_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4535_ = ((lean_object*)(l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_));
v___x_4536_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4537_ = l_Lean_Name_str___override(v___x_4536_, v___x_4535_);
return v___x_4537_;
}
}
static lean_object* _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v___x_4538_ = lean_unsigned_to_nat(2u);
v___x_4539_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4540_ = l_Lean_Name_num___override(v___x_4539_, v___x_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4542_; uint8_t v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4542_ = ((lean_object*)(l_Lean_mkBRecOn___closed__1));
v___x_4543_ = 0;
v___x_4544_ = lean_obj_once(&l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_, &l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_);
v___x_4545_ = l_Lean_registerTraceClass(v___x_4542_, v___x_4543_, v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2____boxed(lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l___private_Lean_Meta_Constructions_BRecOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_BRecOn_2304625798____hygCtx___hyg_2_();
return v_res_4547_;
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
