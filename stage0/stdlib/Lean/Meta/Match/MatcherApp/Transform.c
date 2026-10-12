// Lean compiler output
// Module: Lean.Meta.Match.MatcherApp.Transform
// Imports: public import Lean.Meta.Match.MatcherApp.Basic public import Lean.Meta.Match.MatchEqsExt public import Lean.Meta.Match.AltTelescopes public import Lean.Meta.AppBuilder import Lean.Meta.Tactic.Split import Lean.Meta.Tactic.Refl
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
lean_object* l_Subarray_empty___redArg();
lean_object* l_Array_instInhabited___redArg();
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_LocalContext_setUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Meta_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_forallBoundedTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_forallAltVarsTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_getEquationsFor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_admit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_arrowDomainsN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
lean_object* l_Lean_mkArrowN(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected type at MatcherApp.addArg"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "unexpected matcher application, insufficient number of parameters in alternative"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "unexpected matcher application, alternative must have "};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " parameters"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "failed to add argument to matcher application, argument type was not refined by `casesOn`"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "failed to add argument to matcher application, type error when constructing the new motive"};
static const lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "unexpected matcher application, motive must be lambda expression with #"};
static const lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " arguments"};
static const lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "failed to transfer argument through matcher application, alt type must be telescope with #"};
static const lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__0_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 101, .m_capacity = 101, .m_length = 100, .m_data = "failed to transfer argument through matcher application, type error when constructing the new motive"};
static const lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 97, .m_capacity = 97, .m_length = 96, .m_data = "failed to transfer argument through matcher application, motive must be lambda expression with #"};
static const lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Function"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__1_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 8, 186, 189, 152, 89, 197, 12)}};
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__1_value),LEAN_SCALAR_PTR_LITERAL(231, 33, 22, 82, 100, 121, 126, 178)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__3 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__3_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__0_value;
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__3_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__0_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Match.MatcherApp.Transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.MatcherApp.transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "assertion violation: ys.size == splitterAltInfo.numFields\n        "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: altInfo.numOverlaps = 0\n      "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "failed to transform matcher, type error when constructing splitter motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "failed to transform matcher, type error when constructing new motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 83, .m_capacity = 83, .m_length = 82, .m_data = "failed to transform matcher, type error when constructing new pre-splitter motive:"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\nfailed with"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matcher "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " has no MatchInfo found"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object**);
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__2;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__3;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__4;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__5;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__6;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Cannot close goal after splitting: "};
static const lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " of alternative "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = " still depends on "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0;
static lean_once_cell_t l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_MatcherApp_inferMatchType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_MatcherApp_inferMatchType___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_inferMatchType___closed__0_value;
static const lean_closure_object l_Lean_Meta_MatcherApp_inferMatchType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_MatcherApp_inferMatchType___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_inferMatchType___closed__1_value;
static const lean_closure_object l_Lean_Meta_MatcherApp_inferMatchType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Meta_MatcherApp_inferMatchType___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_inferMatchType___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v_c_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v_b_12_, lean_object* v_c_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(v_k_11_, v_b_12_, v_c_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_19_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(lean_object* v_e_20_, lean_object* v_maxFVars_21_, lean_object* v_k_22_, uint8_t v_cleanupAnnotations_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; uint8_t v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_29_, 0, v_k_22_);
v___x_30_ = 1;
v___x_31_ = 0;
v___x_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_32_, 0, v_maxFVars_21_);
v___x_33_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_20_, v___x_30_, v___x_31_, v___x_30_, v___x_31_, v___x_32_, v___f_29_, v_cleanupAnnotations_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
lean_dec_ref_known(v___x_32_, 1);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v___x_33_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_a_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
v_a_42_ = lean_ctor_get(v___x_33_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_33_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_33_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_20_ = stack[0].m_obj;
lean_object* v_maxFVars_21_ = stack[1].m_obj;
lean_object* v_k_22_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_23_ = stack[3].m_num;
lean_object* v___y_24_ = stack[4].m_obj;
lean_object* v___y_25_ = stack[5].m_obj;
lean_object* v___y_26_ = stack[6].m_obj;
lean_object* v___y_27_ = stack[7].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_e_20_, v_maxFVars_21_, v_k_22_, v_cleanupAnnotations_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___boxed(lean_object* v_e_51_, lean_object* v_maxFVars_52_, lean_object* v_k_53_, lean_object* v_cleanupAnnotations_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_60_; lean_object* v_res_61_; 
v_cleanupAnnotations_boxed_60_ = lean_unbox(v_cleanupAnnotations_54_);
v_res_61_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_e_51_, v_maxFVars_52_, v_k_53_, v_cleanupAnnotations_boxed_60_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_61_;
}
}
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_object* v_00_u03b1_62_, lean_object* v_e_63_, lean_object* v_maxFVars_64_, lean_object* v_k_65_, uint8_t v_cleanupAnnotations_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_e_63_, v_maxFVars_64_, v_k_65_, v_cleanupAnnotations_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
return v___x_72_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_63_ = stack[1].m_obj;
lean_object* v_maxFVars_64_ = stack[2].m_obj;
lean_object* v_k_65_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_66_ = stack[4].m_num;
lean_object* v___y_67_ = stack[5].m_obj;
lean_object* v___y_68_ = stack[6].m_obj;
lean_object* v___y_69_ = stack[7].m_obj;
lean_object* v___y_70_ = stack[8].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_box(0), v_e_63_, v_maxFVars_64_, v_k_65_, v_cleanupAnnotations_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___boxed(lean_object* v_00_u03b1_74_, lean_object* v_e_75_, lean_object* v_maxFVars_76_, lean_object* v_k_77_, lean_object* v_cleanupAnnotations_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_84_; lean_object* v_res_85_; 
v_cleanupAnnotations_boxed_84_ = lean_unbox(v_cleanupAnnotations_78_);
v_res_85_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(v_00_u03b1_74_, v_e_75_, v_maxFVars_76_, v_k_77_, v_cleanupAnnotations_boxed_84_, v___y_79_, v___y_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_85_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object* v_xs_86_, lean_object* v_alt_87_, uint8_t v___x_88_, uint8_t v_refined_89_, lean_object* v_unrefinedArgType_90_, lean_object* v_binderType_91_, lean_object* v_x_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
uint8_t v_refined_99_; 
if (v_refined_89_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = l_Lean_Meta_isExprDefEq(v_unrefinedArgType_90_, v_binderType_91_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; uint8_t v___x_124_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = lean_unbox(v_a_123_);
lean_dec(v_a_123_);
if (v___x_124_ == 0)
{
v_refined_99_ = v___x_88_;
goto v___jp_98_;
}
else
{
v_refined_99_ = v_refined_89_;
goto v___jp_98_;
}
}
else
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_x_92_);
lean_dec_ref(v_alt_87_);
lean_dec_ref(v_xs_86_);
v_a_125_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v___x_122_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v___x_122_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_91_);
lean_dec_ref(v_unrefinedArgType_90_);
v_refined_99_ = v_refined_89_;
goto v___jp_98_;
}
v___jp_98_:
{
lean_object* v___x_100_; uint8_t v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; 
v___x_100_ = lean_array_push(v_xs_86_, v_x_92_);
v___x_101_ = 0;
v___x_102_ = 1;
v___x_103_ = l_Lean_Meta_mkLambdaFVars(v___x_100_, v_alt_87_, v___x_101_, v___x_88_, v___x_101_, v___x_88_, v___x_102_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec_ref(v___x_100_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_113_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_113_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_113_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_108_ = lean_box(v_refined_99_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_a_104_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_109_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_103_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_103_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_86_ = stack[0].m_obj;
lean_object* v_alt_87_ = stack[1].m_obj;
uint8_t v___x_88_ = stack[2].m_num;
uint8_t v_refined_89_ = stack[3].m_num;
lean_object* v_unrefinedArgType_90_ = stack[4].m_obj;
lean_object* v_binderType_91_ = stack[5].m_obj;
lean_object* v_x_92_ = stack[6].m_obj;
lean_object* v___y_93_ = stack[7].m_obj;
lean_object* v___y_94_ = stack[8].m_obj;
lean_object* v___y_95_ = stack[9].m_obj;
lean_object* v___y_96_ = stack[10].m_obj;
lean_object* v_res_133_;
v_res_133_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_xs_86_, v_alt_87_, v___x_88_, v_refined_89_, v_unrefinedArgType_90_, v_binderType_91_, v_x_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
stack->m_obj
 = v_res_133_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object* v_xs_134_, lean_object* v_alt_135_, lean_object* v___x_136_, lean_object* v_refined_137_, lean_object* v_unrefinedArgType_138_, lean_object* v_binderType_139_, lean_object* v_x_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
uint8_t v___x_3929__boxed_146_; uint8_t v_refined_boxed_147_; lean_object* v_res_148_; 
v___x_3929__boxed_146_ = lean_unbox(v___x_136_);
v_refined_boxed_147_ = lean_unbox(v_refined_137_);
v_res_148_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_xs_134_, v_alt_135_, v___x_3929__boxed_146_, v_refined_boxed_147_, v_unrefinedArgType_138_, v_binderType_139_, v_x_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_148_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object* v_msgData_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; lean_object* v_env_156_; uint8_t v___x_157_; lean_object* v_env_158_; lean_object* v___x_159_; lean_object* v_toCold_160_; lean_object* v_mctx_161_; lean_object* v_lctx_162_; lean_object* v_options_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_155_ = lean_st_ref_get(v___y_153_);
v_env_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc_ref(v_env_156_);
lean_dec(v___x_155_);
v___x_157_ = 0;
v_env_158_ = l_Lean_Environment_setRecordingDeps(v_env_156_, v___x_157_);
v___x_159_ = lean_st_ref_get(v___y_151_);
v_toCold_160_ = lean_ctor_get(v___y_152_, 0);
v_mctx_161_ = lean_ctor_get(v___x_159_, 0);
lean_inc_ref(v_mctx_161_);
lean_dec(v___x_159_);
v_lctx_162_ = lean_ctor_get(v___y_150_, 2);
v_options_163_ = lean_ctor_get(v_toCold_160_, 2);
lean_inc_ref(v_options_163_);
lean_inc_ref(v_lctx_162_);
v___x_164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_164_, 0, v_env_158_);
lean_ctor_set(v___x_164_, 1, v_mctx_161_);
lean_ctor_set(v___x_164_, 2, v_lctx_162_);
lean_ctor_set(v___x_164_, 3, v_options_163_);
v___x_165_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_msgData_149_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_149_ = stack[0].m_obj;
lean_object* v___y_150_ = stack[1].m_obj;
lean_object* v___y_151_ = stack[2].m_obj;
lean_object* v___y_152_ = stack[3].m_obj;
lean_object* v___y_153_ = stack[4].m_obj;
lean_object* v_res_167_;
v_res_167_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msgData_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
stack->m_obj
 = v_res_167_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object* v_msgData_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msgData_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object* v_msg_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_ref_181_; lean_object* v___x_182_; lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_ref_181_ = lean_ctor_get(v___y_178_, 2);
v___x_182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msg_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
v_a_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
lean_inc(v_ref_181_);
v___x_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_187_, 0, v_ref_181_);
lean_ctor_set(v___x_187_, 1, v_a_183_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 1);
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_175_ = stack[0].m_obj;
lean_object* v___y_176_ = stack[1].m_obj;
lean_object* v___y_177_ = stack[2].m_obj;
lean_object* v___y_178_ = stack[3].m_obj;
lean_object* v___y_179_ = stack[4].m_obj;
lean_object* v_res_192_;
v_res_192_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
stack->m_obj
 = v_res_192_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t v___x_212_, uint8_t v_refined_213_, lean_object* v_unrefinedArgType_214_, lean_object* v_binderType_215_, lean_object* v_numParams_216_, lean_object* v_xs_217_, lean_object* v_alt_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_229_; lean_object* v___y_259_; lean_object* v___y_260_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_272_ = lean_array_get_size(v_xs_217_);
v___x_273_ = lean_nat_dec_eq(v___x_272_, v_numParams_216_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_274_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5);
v___x_275_ = l_Nat_reprFast(v_numParams_216_);
v___x_276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_274_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_280_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_dec_ref_known(v___x_281_, 1);
goto v___jp_267_;
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec_ref(v_alt_218_);
lean_dec_ref(v_xs_217_);
lean_dec_ref(v_binderType_215_);
lean_dec_ref(v_unrefinedArgType_214_);
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
else
{
lean_dec(v_numParams_216_);
goto v___jp_267_;
}
v___jp_224_:
{
if (lean_obj_tag(v___y_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___y_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___y_229_, 1);
v___x_231_ = l_Lean_Meta_whnfForall(v_a_230_, v___y_226_, v___y_228_, v___y_227_, v___y_225_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
if (lean_obj_tag(v_a_232_) == 7)
{
lean_object* v_binderName_233_; lean_object* v_binderType_234_; uint8_t v_binderInfo_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___f_238_; lean_object* v___x_239_; 
v_binderName_233_ = lean_ctor_get(v_a_232_, 0);
lean_inc(v_binderName_233_);
v_binderType_234_ = lean_ctor_get(v_a_232_, 1);
lean_inc_ref_n(v_binderType_234_, 2);
v_binderInfo_235_ = lean_ctor_get_uint8(v_a_232_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_232_, 3);
v___x_236_ = lean_box(v___x_212_);
v___x_237_ = lean_box(v_refined_213_);
v___f_238_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 6);
lean_closure_set(v___f_238_, 0, v_xs_217_);
lean_closure_set(v___f_238_, 1, v_alt_218_);
lean_closure_set(v___f_238_, 2, v___x_236_);
lean_closure_set(v___f_238_, 3, v___x_237_);
lean_closure_set(v___f_238_, 4, v_unrefinedArgType_214_);
lean_closure_set(v___f_238_, 5, v_binderType_234_);
v___x_239_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_233_, v_binderInfo_235_, v_binderType_234_, v___f_238_, v___y_226_, v___y_228_, v___y_227_, v___y_225_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_a_232_);
lean_dec_ref(v_alt_218_);
lean_dec_ref(v_xs_217_);
lean_dec_ref(v_unrefinedArgType_214_);
v___x_240_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_241_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_240_, v___y_226_, v___y_228_, v___y_227_, v___y_225_);
return v___x_241_;
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v_alt_218_);
lean_dec_ref(v_xs_217_);
lean_dec_ref(v_unrefinedArgType_214_);
v_a_242_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_231_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_231_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec_ref(v_alt_218_);
lean_dec_ref(v_xs_217_);
lean_dec_ref(v_unrefinedArgType_214_);
v_a_250_ = lean_ctor_get(v___y_229_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___y_229_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___y_229_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___y_229_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
v___jp_258_:
{
if (v___y_264_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v___y_259_);
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_266_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_265_, v___y_261_, v___y_263_, v___y_262_, v___y_260_);
v___y_225_ = v___y_260_;
v___y_226_ = v___y_261_;
v___y_227_ = v___y_262_;
v___y_228_ = v___y_263_;
v___y_229_ = v___x_266_;
goto v___jp_224_;
}
else
{
v___y_225_ = v___y_260_;
v___y_226_ = v___y_261_;
v___y_227_ = v___y_262_;
v___y_228_ = v___y_263_;
v___y_229_ = v___y_259_;
goto v___jp_224_;
}
}
v___jp_267_:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_instantiateForall(v_binderType_215_, v_xs_217_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_268_) == 0)
{
v___y_225_ = v___y_222_;
v___y_226_ = v___y_219_;
v___y_227_ = v___y_221_;
v___y_228_ = v___y_220_;
v___y_229_ = v___x_268_;
goto v___jp_224_;
}
else
{
lean_object* v_a_269_; uint8_t v___x_270_; 
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v___x_270_ = l_Lean_Exception_isInterrupt(v_a_269_);
if (v___x_270_ == 0)
{
uint8_t v___x_271_; 
lean_inc(v_a_269_);
v___x_271_ = l_Lean_Exception_isRuntime(v_a_269_);
v___y_259_ = v___x_268_;
v___y_260_ = v___y_222_;
v___y_261_ = v___y_219_;
v___y_262_ = v___y_221_;
v___y_263_ = v___y_220_;
v___y_264_ = v___x_271_;
goto v___jp_258_;
}
else
{
v___y_259_ = v___x_268_;
v___y_260_ = v___y_222_;
v___y_261_ = v___y_219_;
v___y_262_ = v___y_221_;
v___y_263_ = v___y_220_;
v___y_264_ = v___x_270_;
goto v___jp_258_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_212_ = stack[0].m_num;
uint8_t v_refined_213_ = stack[1].m_num;
lean_object* v_unrefinedArgType_214_ = stack[2].m_obj;
lean_object* v_binderType_215_ = stack[3].m_obj;
lean_object* v_numParams_216_ = stack[4].m_obj;
lean_object* v_xs_217_ = stack[5].m_obj;
lean_object* v_alt_218_ = stack[6].m_obj;
lean_object* v___y_219_ = stack[7].m_obj;
lean_object* v___y_220_ = stack[8].m_obj;
lean_object* v___y_221_ = stack[9].m_obj;
lean_object* v___y_222_ = stack[10].m_obj;
lean_object* v_res_290_;
v_res_290_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_212_, v_refined_213_, v_unrefinedArgType_214_, v_binderType_215_, v_numParams_216_, v_xs_217_, v_alt_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* v___x_291_, lean_object* v_refined_292_, lean_object* v_unrefinedArgType_293_, lean_object* v_binderType_294_, lean_object* v_numParams_295_, lean_object* v_xs_296_, lean_object* v_alt_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_4189__boxed_303_; uint8_t v_refined_boxed_304_; lean_object* v_res_305_; 
v___x_4189__boxed_303_ = lean_unbox(v___x_291_);
v_refined_boxed_304_ = lean_unbox(v_refined_292_);
v_res_305_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4189__boxed_303_, v_refined_boxed_304_, v_unrefinedArgType_293_, v_binderType_294_, v_numParams_295_, v_xs_296_, v_alt_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* v_unrefinedArgType_309_, lean_object* v_typeNew_310_, lean_object* v_altNumParams_311_, lean_object* v_alts_312_, uint8_t v_refined_313_, lean_object* v_i_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = lean_array_get_size(v_alts_312_);
v___x_321_ = lean_nat_dec_lt(v_i_314_, v___x_320_);
if (v___x_321_ == 0)
{
lean_dec(v_i_314_);
lean_dec_ref(v_typeNew_310_);
lean_dec_ref(v_unrefinedArgType_309_);
if (v_refined_313_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec_ref(v_alts_312_);
v___x_322_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
v___x_323_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_322_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; 
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v_alts_312_);
return v___x_324_;
}
}
else
{
lean_object* v___x_325_; lean_object* v_alt_326_; lean_object* v_numParams_327_; lean_object* v___x_328_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v_alt_326_ = lean_array_fget_borrowed(v_alts_312_, v_i_314_);
v_numParams_327_ = lean_array_get_borrowed(v___x_325_, v_altNumParams_311_, v_i_314_);
v___x_328_ = l_Lean_Meta_whnfD(v_typeNew_310_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
if (lean_obj_tag(v_a_329_) == 7)
{
lean_object* v_binderType_330_; lean_object* v_body_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___f_334_; uint8_t v___x_335_; lean_object* v___x_336_; 
v_binderType_330_ = lean_ctor_get(v_a_329_, 1);
lean_inc_ref(v_binderType_330_);
v_body_331_ = lean_ctor_get(v_a_329_, 2);
lean_inc_ref(v_body_331_);
lean_dec_ref_known(v_a_329_, 3);
v___x_332_ = lean_box(v___x_321_);
v___x_333_ = lean_box(v_refined_313_);
lean_inc_n(v_numParams_327_, 2);
lean_inc_ref(v_unrefinedArgType_309_);
v___f_334_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(v___f_334_, 0, v___x_332_);
lean_closure_set(v___f_334_, 1, v___x_333_);
lean_closure_set(v___f_334_, 2, v_unrefinedArgType_309_);
lean_closure_set(v___f_334_, 3, v_binderType_330_);
lean_closure_set(v___f_334_, 4, v_numParams_327_);
v___x_335_ = 0;
lean_inc(v_alt_326_);
v___x_336_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_alt_326_, v_numParams_327_, v___f_334_, v___x_335_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v_fst_338_; lean_object* v_snd_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc(v_a_337_);
lean_dec_ref_known(v___x_336_, 1);
v_fst_338_ = lean_ctor_get(v_a_337_, 0);
lean_inc(v_fst_338_);
v_snd_339_ = lean_ctor_get(v_a_337_, 1);
lean_inc(v_snd_339_);
lean_dec(v_a_337_);
v___x_340_ = lean_expr_instantiate1(v_body_331_, v_fst_338_);
lean_dec_ref(v_body_331_);
v___x_341_ = lean_array_fset(v_alts_312_, v_i_314_, v_fst_338_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_i_314_, v___x_342_);
lean_dec(v_i_314_);
v___x_344_ = lean_unbox(v_snd_339_);
lean_dec(v_snd_339_);
v_typeNew_310_ = v___x_340_;
v_alts_312_ = v___x_341_;
v_refined_313_ = v___x_344_;
v_i_314_ = v___x_343_;
goto _start;
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
lean_dec_ref(v_body_331_);
lean_dec(v_i_314_);
lean_dec_ref(v_alts_312_);
lean_dec_ref(v_unrefinedArgType_309_);
v_a_346_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_336_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_336_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
}
else
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_a_329_);
lean_dec(v_i_314_);
lean_dec_ref(v_alts_312_);
lean_dec_ref(v_unrefinedArgType_309_);
v___x_354_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_355_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_354_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
return v___x_355_;
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_i_314_);
lean_dec_ref(v_alts_312_);
lean_dec_ref(v_unrefinedArgType_309_);
v_a_356_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_328_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_328_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_0interp(lean_interpreter_value* stack)
{
lean_object* v_unrefinedArgType_309_ = stack[0].m_obj;
lean_object* v_typeNew_310_ = stack[1].m_obj;
lean_object* v_altNumParams_311_ = stack[2].m_obj;
lean_object* v_alts_312_ = stack[3].m_obj;
uint8_t v_refined_313_ = stack[4].m_num;
lean_object* v_i_314_ = stack[5].m_obj;
lean_object* v_a_315_ = stack[6].m_obj;
lean_object* v_a_316_ = stack[7].m_obj;
lean_object* v_a_317_ = stack[8].m_obj;
lean_object* v_a_318_ = stack[9].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_309_, v_typeNew_310_, v_altNumParams_311_, v_alts_312_, v_refined_313_, v_i_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* v_unrefinedArgType_365_, lean_object* v_typeNew_366_, lean_object* v_altNumParams_367_, lean_object* v_alts_368_, lean_object* v_refined_369_, lean_object* v_i_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
uint8_t v_refined_boxed_376_; lean_object* v_res_377_; 
v_refined_boxed_376_ = lean_unbox(v_refined_369_);
v_res_377_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_365_, v_typeNew_366_, v_altNumParams_367_, v_alts_368_, v_refined_boxed_376_, v_i_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec_ref(v_altNumParams_367_);
return v_res_377_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* v_00_u03b1_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
return v___x_385_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_379_ = stack[1].m_obj;
lean_object* v___y_380_ = stack[2].m_obj;
lean_object* v___y_381_ = stack[3].m_obj;
lean_object* v___y_382_ = stack[4].m_obj;
lean_object* v___y_383_ = stack[5].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_box(0), v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* v_00_u03b1_387_, lean_object* v_msg_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(v_00_u03b1_387_, v_msg_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* v_e_395_, lean_object* v_k_396_, uint8_t v_cleanupAnnotations_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v___f_403_; uint8_t v___x_404_; uint8_t v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___f_403_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_403_, 0, v_k_396_);
v___x_404_ = 1;
v___x_405_ = 0;
v___x_406_ = lean_box(0);
v___x_407_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_395_, v___x_404_, v___x_405_, v___x_404_, v___x_405_, v___x_406_, v___f_403_, v_cleanupAnnotations_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
else
{
lean_object* v_a_416_; lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_423_; 
v_a_416_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_423_ == 0)
{
v___x_418_ = v___x_407_;
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
else
{
lean_inc(v_a_416_);
lean_dec(v___x_407_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_423_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_421_; 
if (v_isShared_419_ == 0)
{
v___x_421_ = v___x_418_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_a_416_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_395_ = stack[0].m_obj;
lean_object* v_k_396_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_397_ = stack[2].m_num;
lean_object* v___y_398_ = stack[3].m_obj;
lean_object* v___y_399_ = stack[4].m_obj;
lean_object* v___y_400_ = stack[5].m_obj;
lean_object* v___y_401_ = stack[6].m_obj;
lean_object* v_res_424_;
v_res_424_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_395_, v_k_396_, v_cleanupAnnotations_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* v_e_425_, lean_object* v_k_426_, lean_object* v_cleanupAnnotations_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_433_; lean_object* v_res_434_; 
v_cleanupAnnotations_boxed_433_ = lean_unbox(v_cleanupAnnotations_427_);
v_res_434_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_425_, v_k_426_, v_cleanupAnnotations_boxed_433_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
return v_res_434_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* v_00_u03b1_435_, lean_object* v_e_436_, lean_object* v_k_437_, uint8_t v_cleanupAnnotations_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_436_, v_k_437_, v_cleanupAnnotations_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_436_ = stack[1].m_obj;
lean_object* v_k_437_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_438_ = stack[3].m_num;
lean_object* v___y_439_ = stack[4].m_obj;
lean_object* v___y_440_ = stack[5].m_obj;
lean_object* v___y_441_ = stack[6].m_obj;
lean_object* v___y_442_ = stack[7].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_box(0), v_e_436_, v_k_437_, v_cleanupAnnotations_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* v_00_u03b1_446_, lean_object* v_e_447_, lean_object* v_k_448_, lean_object* v_cleanupAnnotations_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_455_; lean_object* v_res_456_; 
v_cleanupAnnotations_boxed_455_ = lean_unbox(v_cleanupAnnotations_449_);
v_res_456_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(v_00_u03b1_446_, v_e_447_, v_k_448_, v_cleanupAnnotations_boxed_455_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* v___x_457_, lean_object* v_motiveArgs_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_zero_461_; uint8_t v_isZero_462_; 
v_zero_461_ = lean_unsigned_to_nat(0u);
v_isZero_462_ = lean_nat_dec_eq(v_x_459_, v_zero_461_);
if (v_isZero_462_ == 1)
{
lean_dec(v_x_459_);
return v_x_460_;
}
else
{
lean_object* v_one_463_; lean_object* v_n_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_one_463_ = lean_unsigned_to_nat(1u);
v_n_464_ = lean_nat_sub(v_x_459_, v_one_463_);
lean_dec(v_x_459_);
v___x_465_ = lean_array_fget_borrowed(v___x_457_, v_n_464_);
v___x_466_ = l_Lean_Expr_isFVar(v___x_465_);
if (v___x_466_ == 0)
{
v_x_459_ = v_n_464_;
goto _start;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_468_ = l_Lean_instInhabitedExpr;
v___x_469_ = lean_array_get_borrowed(v___x_468_, v_motiveArgs_458_, v_n_464_);
lean_inc(v___x_465_);
v___x_470_ = l_Lean_Expr_replaceFVar(v_x_460_, v___x_465_, v___x_469_);
lean_dec_ref(v_x_460_);
v_x_459_ = v_n_464_;
v_x_460_ = v___x_470_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* v___x_472_, lean_object* v_motiveArgs_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_472_, v_motiveArgs_473_, v_x_474_, v_x_475_);
lean_dec_ref(v_motiveArgs_473_);
lean_dec_ref(v___x_472_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* v___x_477_, lean_object* v_motiveArgs_478_, lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v_zero_481_; uint8_t v_isZero_482_; 
v_zero_481_ = lean_unsigned_to_nat(0u);
v_isZero_482_ = lean_nat_dec_eq(v_x_479_, v_zero_481_);
if (v_isZero_482_ == 1)
{
return v_x_480_;
}
else
{
lean_object* v_one_483_; lean_object* v_n_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_one_483_ = lean_unsigned_to_nat(1u);
v_n_484_ = lean_nat_sub(v_x_479_, v_one_483_);
v___x_485_ = lean_array_fget_borrowed(v___x_477_, v_n_484_);
v___x_486_ = l_Lean_Expr_isFVar(v___x_485_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; 
v___x_487_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_477_, v_motiveArgs_478_, v_n_484_, v_x_480_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_488_ = l_Lean_instInhabitedExpr;
v___x_489_ = lean_array_get_borrowed(v___x_488_, v_motiveArgs_478_, v_n_484_);
lean_inc(v___x_485_);
v___x_490_ = l_Lean_Expr_replaceFVar(v_x_480_, v___x_485_, v___x_489_);
lean_dec_ref(v_x_480_);
v___x_491_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_477_, v_motiveArgs_478_, v_n_484_, v___x_490_);
return v___x_491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* v___x_492_, lean_object* v_motiveArgs_493_, lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v___x_492_, v_motiveArgs_493_, v_x_494_, v_x_495_);
lean_dec(v_x_494_);
lean_dec_ref(v_motiveArgs_493_);
lean_dec_ref(v___x_492_);
return v_res_496_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0));
v___x_499_ = l_Lean_stringToMessageData(v___x_498_);
return v___x_499_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2));
v___x_502_ = l_Lean_stringToMessageData(v___x_501_);
return v___x_502_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4));
v___x_505_ = l_Lean_stringToMessageData(v___x_504_);
return v___x_505_;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_506_, lean_object* v_e_507_, lean_object* v_discrs_508_, lean_object* v_toMatcherInfo_509_, lean_object* v_alts_510_, lean_object* v_matcherName_511_, lean_object* v_params_512_, lean_object* v_remaining_513_, lean_object* v_matcherLevels_514_, lean_object* v_motiveArgs_515_, lean_object* v_motiveBody_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v_matcherLevels_581_; lean_object* v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = lean_array_get_size(v_motiveArgs_515_);
v___x_667_ = lean_array_get_size(v_discrs_508_);
v___x_668_ = lean_nat_dec_eq(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_a_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec_ref(v_motiveBody_516_);
lean_dec_ref(v_matcherLevels_514_);
lean_dec_ref(v_params_512_);
lean_dec(v_matcherName_511_);
lean_dec_ref(v_alts_510_);
lean_dec_ref(v_toMatcherInfo_509_);
lean_dec_ref(v_discrs_508_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v___x_669_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_670_ = l_Nat_reprFast(v___x_667_);
v___x_671_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
v___x_672_ = l_Lean_MessageData_ofFormat(v___x_671_);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_669_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_673_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
v___x_676_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_675_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
v_a_677_ = lean_ctor_get(v___x_676_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_676_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_676_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_a_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_a_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
else
{
v___y_626_ = v___y_517_;
v___y_627_ = v___y_518_;
v___y_628_ = v___y_519_;
v___y_629_ = v___y_520_;
goto v___jp_625_;
}
v___jp_522_:
{
lean_object* v___x_538_; 
lean_inc(v___y_537_);
lean_inc_ref(v___y_536_);
lean_inc(v___y_535_);
lean_inc_ref(v___y_534_);
v___x_538_ = lean_infer_type(v___y_525_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v_a_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_a_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_a_539_);
lean_dec_ref_known(v___x_538_, 1);
v___x_540_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_506_);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_528_, v_a_539_, v___x_540_, v___y_523_, v___y_532_, v___x_541_, v___y_534_, v___y_535_, v___y_536_, v___y_537_);
lean_dec_ref(v___x_540_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_555_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_555_ == 0)
{
v___x_545_ = v___x_542_;
v_isShared_546_ = v_isSharedCheck_555_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_542_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_555_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_array_push(v___x_548_, v_e_507_);
v___x_550_ = l_Array_append___redArg(v___x_549_, v___y_530_);
v___x_551_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_551_, 0, v___y_529_);
lean_ctor_set(v___x_551_, 1, v___y_524_);
lean_ctor_set(v___x_551_, 2, v___y_526_);
lean_ctor_set(v___x_551_, 3, v___y_527_);
lean_ctor_set(v___x_551_, 4, v___y_533_);
lean_ctor_set(v___x_551_, 5, v___y_531_);
lean_ctor_set(v___x_551_, 6, v_a_543_);
lean_ctor_set(v___x_551_, 7, v___x_550_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 0, v___x_551_);
v___x_553_ = v___x_545_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
lean_dec_ref(v___y_533_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_524_);
lean_dec_ref(v_e_507_);
v_a_556_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_542_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_542_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
lean_dec_ref(v___y_533_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v_a_564_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_538_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_538_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
v___jp_572_:
{
uint8_t v___x_586_; uint8_t v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; 
v___x_586_ = 0;
v___x_587_ = 1;
v___x_588_ = 1;
v___x_589_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_515_, v___y_575_, v___x_586_, v___x_587_, v___x_586_, v___x_587_, v___x_588_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc_n(v_a_590_, 2);
lean_dec_ref_known(v___x_589_, 1);
lean_inc_ref(v_matcherLevels_581_);
v___x_591_ = lean_array_to_list(v_matcherLevels_581_);
lean_inc(v___y_574_);
v___x_592_ = l_Lean_mkConst(v___y_574_, v___x_591_);
v___x_593_ = l_Lean_mkAppN(v___x_592_, v___y_576_);
v___x_594_ = l_Lean_Expr_app___override(v___x_593_, v_a_590_);
v___x_595_ = l_Lean_mkAppN(v___x_594_, v___y_580_);
lean_inc_ref(v___x_595_);
v___x_596_ = l_Lean_Meta_isTypeCorrect(v___x_595_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; uint8_t v___x_598_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
lean_inc(v_a_597_);
lean_dec_ref_known(v___x_596_, 1);
v___x_598_ = lean_unbox(v_a_597_);
lean_dec(v_a_597_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_608_; 
lean_dec_ref(v___x_595_);
lean_dec(v_a_590_);
lean_dec_ref(v_matcherLevels_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v___x_599_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_600_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_599_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_608_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_608_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_606_; 
if (v_isShared_604_ == 0)
{
v___x_606_ = v___x_603_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_601_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
else
{
v___y_523_ = v___y_573_;
v___y_524_ = v___y_574_;
v___y_525_ = v___x_595_;
v___y_526_ = v_matcherLevels_581_;
v___y_527_ = v___y_576_;
v___y_528_ = v___y_577_;
v___y_529_ = v___y_579_;
v___y_530_ = v___y_578_;
v___y_531_ = v___y_580_;
v___y_532_ = v___x_586_;
v___y_533_ = v_a_590_;
v___y_534_ = v___y_582_;
v___y_535_ = v___y_583_;
v___y_536_ = v___y_584_;
v___y_537_ = v___y_585_;
goto v___jp_522_;
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec_ref(v___x_595_);
lean_dec(v_a_590_);
lean_dec_ref(v_matcherLevels_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v_a_609_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_596_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_596_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec_ref(v_matcherLevels_581_);
lean_dec_ref(v___y_580_);
lean_dec_ref(v___y_579_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v_a_617_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_589_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_589_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
v___jp_625_:
{
lean_object* v___x_630_; 
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
lean_inc_ref(v_e_507_);
v___x_630_ = lean_infer_type(v_e_507_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc_n(v_a_631_, 2);
lean_dec_ref_known(v___x_630_, 1);
v___x_632_ = lean_array_get_size(v_discrs_508_);
v___x_633_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_508_, v_motiveArgs_515_, v___x_632_, v_a_631_);
v___x_634_ = l_Lean_mkArrow(v___x_633_, v_motiveBody_516_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_uElimPos_x3f_635_; 
v_uElimPos_x3f_635_ = lean_ctor_get(v_toMatcherInfo_509_, 3);
if (lean_obj_tag(v_uElimPos_x3f_635_) == 0)
{
lean_object* v_a_636_; 
v_a_636_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v___x_634_, 1);
v___y_573_ = v_alts_510_;
v___y_574_ = v_matcherName_511_;
v___y_575_ = v_a_636_;
v___y_576_ = v_params_512_;
v___y_577_ = v_a_631_;
v___y_578_ = v_remaining_513_;
v___y_579_ = v_toMatcherInfo_509_;
v___y_580_ = v_discrs_508_;
v_matcherLevels_581_ = v_matcherLevels_514_;
v___y_582_ = v___y_626_;
v___y_583_ = v___y_627_;
v___y_584_ = v___y_628_;
v___y_585_ = v___y_629_;
goto v___jp_572_;
}
else
{
lean_object* v_a_637_; lean_object* v_val_638_; lean_object* v___x_639_; 
v_a_637_ = lean_ctor_get(v___x_634_, 0);
lean_inc_n(v_a_637_, 2);
lean_dec_ref_known(v___x_634_, 1);
v_val_638_ = lean_ctor_get(v_uElimPos_x3f_635_, 0);
v___x_639_ = l_Lean_Meta_getLevel(v_a_637_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = lean_array_set(v_matcherLevels_514_, v_val_638_, v_a_640_);
v___y_573_ = v_alts_510_;
v___y_574_ = v_matcherName_511_;
v___y_575_ = v_a_637_;
v___y_576_ = v_params_512_;
v___y_577_ = v_a_631_;
v___y_578_ = v_remaining_513_;
v___y_579_ = v_toMatcherInfo_509_;
v___y_580_ = v_discrs_508_;
v_matcherLevels_581_ = v___x_641_;
v___y_582_ = v___y_626_;
v___y_583_ = v___y_627_;
v___y_584_ = v___y_628_;
v___y_585_ = v___y_629_;
goto v___jp_572_;
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec(v_a_637_);
lean_dec(v_a_631_);
lean_dec_ref(v_matcherLevels_514_);
lean_dec_ref(v_params_512_);
lean_dec(v_matcherName_511_);
lean_dec_ref(v_alts_510_);
lean_dec_ref(v_toMatcherInfo_509_);
lean_dec_ref(v_discrs_508_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v_a_642_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_639_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_639_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec(v_a_631_);
lean_dec_ref(v_matcherLevels_514_);
lean_dec_ref(v_params_512_);
lean_dec(v_matcherName_511_);
lean_dec_ref(v_alts_510_);
lean_dec_ref(v_toMatcherInfo_509_);
lean_dec_ref(v_discrs_508_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v_a_650_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_634_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_634_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_dec_ref(v_motiveBody_516_);
lean_dec_ref(v_matcherLevels_514_);
lean_dec_ref(v_params_512_);
lean_dec(v_matcherName_511_);
lean_dec_ref(v_alts_510_);
lean_dec_ref(v_toMatcherInfo_509_);
lean_dec_ref(v_discrs_508_);
lean_dec_ref(v_e_507_);
lean_dec_ref(v_matcherApp_506_);
v_a_658_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_630_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_630_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_addArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_506_ = stack[0].m_obj;
lean_object* v_e_507_ = stack[1].m_obj;
lean_object* v_discrs_508_ = stack[2].m_obj;
lean_object* v_toMatcherInfo_509_ = stack[3].m_obj;
lean_object* v_alts_510_ = stack[4].m_obj;
lean_object* v_matcherName_511_ = stack[5].m_obj;
lean_object* v_params_512_ = stack[6].m_obj;
lean_object* v_remaining_513_ = stack[7].m_obj;
lean_object* v_matcherLevels_514_ = stack[8].m_obj;
lean_object* v_motiveArgs_515_ = stack[9].m_obj;
lean_object* v_motiveBody_516_ = stack[10].m_obj;
lean_object* v___y_517_ = stack[11].m_obj;
lean_object* v___y_518_ = stack[12].m_obj;
lean_object* v___y_519_ = stack[13].m_obj;
lean_object* v___y_520_ = stack[14].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_506_, v_e_507_, v_discrs_508_, v_toMatcherInfo_509_, v_alts_510_, v_matcherName_511_, v_params_512_, v_remaining_513_, v_matcherLevels_514_, v_motiveArgs_515_, v_motiveBody_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_686_, lean_object* v_e_687_, lean_object* v_discrs_688_, lean_object* v_toMatcherInfo_689_, lean_object* v_alts_690_, lean_object* v_matcherName_691_, lean_object* v_params_692_, lean_object* v_remaining_693_, lean_object* v_matcherLevels_694_, lean_object* v_motiveArgs_695_, lean_object* v_motiveBody_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_686_, v_e_687_, v_discrs_688_, v_toMatcherInfo_689_, v_alts_690_, v_matcherName_691_, v_params_692_, v_remaining_693_, v_matcherLevels_694_, v_motiveArgs_695_, v_motiveBody_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec_ref(v_motiveArgs_695_);
lean_dec_ref(v_remaining_693_);
return v_res_702_;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* v_matcherApp_703_, lean_object* v_e_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_toMatcherInfo_710_; lean_object* v_matcherName_711_; lean_object* v_matcherLevels_712_; lean_object* v_params_713_; lean_object* v_motive_714_; lean_object* v_discrs_715_; lean_object* v_alts_716_; lean_object* v_remaining_717_; lean_object* v___f_718_; uint8_t v___x_719_; lean_object* v___x_720_; 
v_toMatcherInfo_710_ = lean_ctor_get(v_matcherApp_703_, 0);
lean_inc_ref(v_toMatcherInfo_710_);
v_matcherName_711_ = lean_ctor_get(v_matcherApp_703_, 1);
lean_inc(v_matcherName_711_);
v_matcherLevels_712_ = lean_ctor_get(v_matcherApp_703_, 2);
lean_inc_ref(v_matcherLevels_712_);
v_params_713_ = lean_ctor_get(v_matcherApp_703_, 3);
lean_inc_ref(v_params_713_);
v_motive_714_ = lean_ctor_get(v_matcherApp_703_, 4);
lean_inc_ref(v_motive_714_);
v_discrs_715_ = lean_ctor_get(v_matcherApp_703_, 5);
lean_inc_ref(v_discrs_715_);
v_alts_716_ = lean_ctor_get(v_matcherApp_703_, 6);
lean_inc_ref(v_alts_716_);
v_remaining_717_ = lean_ctor_get(v_matcherApp_703_, 7);
lean_inc_ref(v_remaining_717_);
v___f_718_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_718_, 0, v_matcherApp_703_);
lean_closure_set(v___f_718_, 1, v_e_704_);
lean_closure_set(v___f_718_, 2, v_discrs_715_);
lean_closure_set(v___f_718_, 3, v_toMatcherInfo_710_);
lean_closure_set(v___f_718_, 4, v_alts_716_);
lean_closure_set(v___f_718_, 5, v_matcherName_711_);
lean_closure_set(v___f_718_, 6, v_params_713_);
lean_closure_set(v___f_718_, 7, v_remaining_717_);
lean_closure_set(v___f_718_, 8, v_matcherLevels_712_);
v___x_719_ = 0;
v___x_720_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_714_, v___f_718_, v___x_719_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
return v___x_720_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_addArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_703_ = stack[0].m_obj;
lean_object* v_e_704_ = stack[1].m_obj;
lean_object* v_a_705_ = stack[2].m_obj;
lean_object* v_a_706_ = stack[3].m_obj;
lean_object* v_a_707_ = stack[4].m_obj;
lean_object* v_a_708_ = stack[5].m_obj;
lean_object* v_res_721_;
v_res_721_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_703_, v_e_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
stack->m_obj
 = v_res_721_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* v_matcherApp_722_, lean_object* v_e_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_722_, v_e_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
return v_res_729_;
}
}
lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* v_matcherApp_730_, lean_object* v_e_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_730_, v_e_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_746_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_746_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_746_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_a_738_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_742_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_762_; 
v_a_747_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_762_ == 0)
{
v___x_749_ = v___x_737_;
v_isShared_750_ = v_isSharedCheck_762_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_737_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_762_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
uint8_t v___y_752_; uint8_t v___x_760_; 
v___x_760_ = l_Lean_Exception_isInterrupt(v_a_747_);
if (v___x_760_ == 0)
{
uint8_t v___x_761_; 
lean_inc(v_a_747_);
v___x_761_ = l_Lean_Exception_isRuntime(v_a_747_);
v___y_752_ = v___x_761_;
goto v___jp_751_;
}
else
{
v___y_752_ = v___x_760_;
goto v___jp_751_;
}
v___jp_751_:
{
if (v___y_752_ == 0)
{
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_a_747_);
v___x_753_ = lean_box(0);
if (v_isShared_750_ == 0)
{
lean_ctor_set_tag(v___x_749_, 0);
lean_ctor_set(v___x_749_, 0, v___x_753_);
v___x_755_ = v___x_749_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v___x_758_; 
if (v_isShared_750_ == 0)
{
v___x_758_ = v___x_749_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_747_);
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
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_addArg_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_730_ = stack[0].m_obj;
lean_object* v_e_731_ = stack[1].m_obj;
lean_object* v_a_732_ = stack[2].m_obj;
lean_object* v_a_733_ = stack[3].m_obj;
lean_object* v_a_734_ = stack[4].m_obj;
lean_object* v_a_735_ = stack[5].m_obj;
lean_object* v_res_763_;
v_res_763_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_730_, v_e_731_, v_a_732_, v_a_733_, v_a_734_, v_a_735_);
stack->m_obj
 = v_res_763_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* v_matcherApp_764_, lean_object* v_e_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_764_, v_e_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_771_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(lean_object* v_type_772_, lean_object* v_maxFVars_x3f_773_, lean_object* v_k_774_, uint8_t v_cleanupAnnotations_775_, uint8_t v_whnfType_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___f_782_; lean_object* v___x_783_; 
v___f_782_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_782_, 0, v_k_774_);
v___x_783_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_772_, v_maxFVars_x3f_773_, v___f_782_, v_cleanupAnnotations_775_, v_whnfType_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
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
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
v_a_792_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_783_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_783_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_772_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_773_ = stack[1].m_obj;
lean_object* v_k_774_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_775_ = stack[3].m_num;
uint8_t v_whnfType_776_ = stack[4].m_num;
lean_object* v___y_777_ = stack[5].m_obj;
lean_object* v___y_778_ = stack[6].m_obj;
lean_object* v___y_779_ = stack[7].m_obj;
lean_object* v___y_780_ = stack[8].m_obj;
lean_object* v_res_800_;
v_res_800_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_772_, v_maxFVars_x3f_773_, v_k_774_, v_cleanupAnnotations_775_, v_whnfType_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg___boxed(lean_object* v_type_801_, lean_object* v_maxFVars_x3f_802_, lean_object* v_k_803_, lean_object* v_cleanupAnnotations_804_, lean_object* v_whnfType_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_811_; uint8_t v_whnfType_boxed_812_; lean_object* v_res_813_; 
v_cleanupAnnotations_boxed_811_ = lean_unbox(v_cleanupAnnotations_804_);
v_whnfType_boxed_812_ = lean_unbox(v_whnfType_805_);
v_res_813_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_801_, v_maxFVars_x3f_802_, v_k_803_, v_cleanupAnnotations_boxed_811_, v_whnfType_boxed_812_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
return v_res_813_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(lean_object* v_00_u03b1_814_, lean_object* v_type_815_, lean_object* v_maxFVars_x3f_816_, lean_object* v_k_817_, uint8_t v_cleanupAnnotations_818_, uint8_t v_whnfType_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_815_, v_maxFVars_x3f_816_, v_k_817_, v_cleanupAnnotations_818_, v_whnfType_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_825_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_815_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_816_ = stack[2].m_obj;
lean_object* v_k_817_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_818_ = stack[4].m_num;
uint8_t v_whnfType_819_ = stack[5].m_num;
lean_object* v___y_820_ = stack[6].m_obj;
lean_object* v___y_821_ = stack[7].m_obj;
lean_object* v___y_822_ = stack[8].m_obj;
lean_object* v___y_823_ = stack[9].m_obj;
lean_object* v_res_826_;
v_res_826_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(lean_box(0), v_type_815_, v_maxFVars_x3f_816_, v_k_817_, v_cleanupAnnotations_818_, v_whnfType_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* v_00_u03b1_827_, lean_object* v_type_828_, lean_object* v_maxFVars_x3f_829_, lean_object* v_k_830_, lean_object* v_cleanupAnnotations_831_, lean_object* v_whnfType_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_838_; uint8_t v_whnfType_boxed_839_; lean_object* v_res_840_; 
v_cleanupAnnotations_boxed_838_ = lean_unbox(v_cleanupAnnotations_831_);
v_whnfType_boxed_839_ = lean_unbox(v_whnfType_832_);
v_res_840_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_00_u03b1_827_, v_type_828_, v_maxFVars_x3f_829_, v_k_830_, v_cleanupAnnotations_boxed_838_, v_whnfType_boxed_839_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
return v_res_840_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(lean_object* v_type_841_, lean_object* v_k_842_, uint8_t v_cleanupAnnotations_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___f_849_; uint8_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_849_, 0, v_k_842_);
v___x_850_ = 0;
v___x_851_ = lean_box(0);
v___x_852_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_850_, v___x_851_, v_type_841_, v___f_849_, v_cleanupAnnotations_843_, v___x_850_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_860_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_860_ == 0)
{
v___x_855_ = v___x_852_;
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_a_853_);
lean_dec(v___x_852_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_860_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v___x_858_; 
if (v_isShared_856_ == 0)
{
v___x_858_ = v___x_855_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_853_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_852_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_852_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_841_ = stack[0].m_obj;
lean_object* v_k_842_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_843_ = stack[2].m_num;
lean_object* v___y_844_ = stack[3].m_obj;
lean_object* v___y_845_ = stack[4].m_obj;
lean_object* v___y_846_ = stack[5].m_obj;
lean_object* v___y_847_ = stack[6].m_obj;
lean_object* v_res_869_;
v_res_869_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_841_, v_k_842_, v_cleanupAnnotations_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg___boxed(lean_object* v_type_870_, lean_object* v_k_871_, lean_object* v_cleanupAnnotations_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_878_; lean_object* v_res_879_; 
v_cleanupAnnotations_boxed_878_ = lean_unbox(v_cleanupAnnotations_872_);
v_res_879_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_870_, v_k_871_, v_cleanupAnnotations_boxed_878_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
return v_res_879_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(lean_object* v_00_u03b1_880_, lean_object* v_type_881_, lean_object* v_k_882_, uint8_t v_cleanupAnnotations_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_881_, v_k_882_, v_cleanupAnnotations_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_889_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_881_ = stack[1].m_obj;
lean_object* v_k_882_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_883_ = stack[3].m_num;
lean_object* v___y_884_ = stack[4].m_obj;
lean_object* v___y_885_ = stack[5].m_obj;
lean_object* v___y_886_ = stack[6].m_obj;
lean_object* v___y_887_ = stack[7].m_obj;
lean_object* v_res_890_;
v_res_890_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(lean_box(0), v_type_881_, v_k_882_, v_cleanupAnnotations_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
stack->m_obj
 = v_res_890_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___boxed(lean_object* v_00_u03b1_891_, lean_object* v_type_892_, lean_object* v_k_893_, lean_object* v_cleanupAnnotations_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_900_; lean_object* v_res_901_; 
v_cleanupAnnotations_boxed_900_ = lean_unbox(v_cleanupAnnotations_894_);
v_res_901_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(v_00_u03b1_891_, v_type_892_, v_k_893_, v_cleanupAnnotations_boxed_900_, v___y_895_, v___y_896_, v___y_897_, v___y_898_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
return v_res_901_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(size_t v_sz_902_, size_t v_i_903_, lean_object* v_bs_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_){
_start:
{
uint8_t v___x_910_; 
v___x_910_ = lean_usize_dec_lt(v_i_903_, v_sz_902_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; 
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v_bs_904_);
return v___x_911_;
}
else
{
lean_object* v_v_912_; lean_object* v___x_913_; lean_object* v_bs_x27_914_; lean_object* v___x_915_; 
v_v_912_ = lean_array_uget(v_bs_904_, v_i_903_);
v___x_913_ = lean_unsigned_to_nat(0u);
v_bs_x27_914_ = lean_array_uset(v_bs_904_, v_i_903_, v___x_913_);
lean_inc(v___y_908_);
lean_inc_ref(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v___y_905_);
v___x_915_ = lean_infer_type(v_v_912_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v_a_916_; size_t v___x_917_; size_t v___x_918_; lean_object* v___x_919_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc(v_a_916_);
lean_dec_ref_known(v___x_915_, 1);
v___x_917_ = ((size_t)1ULL);
v___x_918_ = lean_usize_add(v_i_903_, v___x_917_);
v___x_919_ = lean_array_uset(v_bs_x27_914_, v_i_903_, v_a_916_);
v_i_903_ = v___x_918_;
v_bs_904_ = v___x_919_;
goto _start;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v_bs_x27_914_);
v_a_921_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_915_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_915_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_902_ = stack[0].m_num;
size_t v_i_903_ = stack[1].m_num;
lean_object* v_bs_904_ = stack[2].m_obj;
lean_object* v___y_905_ = stack[3].m_obj;
lean_object* v___y_906_ = stack[4].m_obj;
lean_object* v___y_907_ = stack[5].m_obj;
lean_object* v___y_908_ = stack[6].m_obj;
lean_object* v_res_929_;
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_902_, v_i_903_, v_bs_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* v_sz_930_, lean_object* v_i_931_, lean_object* v_bs_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_930_);
lean_dec(v_sz_930_);
v_i_boxed_939_ = lean_unbox_usize(v_i_931_);
lean_dec(v_i_931_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_boxed_938_, v_i_boxed_939_, v_bs_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_940_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__0));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(uint8_t v___x_944_, uint8_t v___x_945_, uint8_t v___x_946_, lean_object* v_a_947_, lean_object* v_fvs_948_, lean_object* v_body_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = lean_array_get_size(v_fvs_948_);
v___x_964_ = lean_nat_dec_eq(v___x_963_, v_a_947_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
v___x_965_ = lean_obj_once(&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1, &l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1);
v___x_966_ = l_Nat_reprFast(v_a_947_);
v___x_967_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = l_Lean_MessageData_ofFormat(v___x_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_965_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_971_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
else
{
lean_dec(v_a_947_);
goto v___jp_955_;
}
v___jp_955_:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_956_ = lean_unsigned_to_nat(2u);
v___x_957_ = l_Lean_Expr_getAppNumArgs(v_body_949_);
v___x_958_ = lean_nat_sub(v___x_957_, v___x_956_);
lean_dec(v___x_957_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_sub(v___x_958_, v___x_959_);
lean_dec(v___x_958_);
v___x_961_ = l_Lean_Expr_getRevArg_x21(v_body_949_, v___x_960_);
v___x_962_ = l_Lean_Meta_mkLambdaFVars(v_fvs_948_, v___x_961_, v___x_944_, v___x_945_, v___x_944_, v___x_945_, v___x_946_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
return v___x_962_;
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_944_ = stack[0].m_num;
uint8_t v___x_945_ = stack[1].m_num;
uint8_t v___x_946_ = stack[2].m_num;
lean_object* v_a_947_ = stack[3].m_obj;
lean_object* v_fvs_948_ = stack[4].m_obj;
lean_object* v_body_949_ = stack[5].m_obj;
lean_object* v___y_950_ = stack[6].m_obj;
lean_object* v___y_951_ = stack[7].m_obj;
lean_object* v___y_952_ = stack[8].m_obj;
lean_object* v___y_953_ = stack[9].m_obj;
lean_object* v_res_981_;
v_res_981_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(v___x_944_, v___x_945_, v___x_946_, v_a_947_, v_fvs_948_, v_body_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_);
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed(lean_object* v___x_982_, lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v_a_985_, lean_object* v_fvs_986_, lean_object* v_body_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
uint8_t v___x_4282__boxed_993_; uint8_t v___x_4283__boxed_994_; uint8_t v___x_4284__boxed_995_; lean_object* v_res_996_; 
v___x_4282__boxed_993_ = lean_unbox(v___x_982_);
v___x_4283__boxed_994_ = lean_unbox(v___x_983_);
v___x_4284__boxed_995_ = lean_unbox(v___x_984_);
v_res_996_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(v___x_4282__boxed_993_, v___x_4283__boxed_994_, v___x_4284__boxed_995_, v_a_985_, v_fvs_986_, v_body_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_body_987_);
lean_dec_ref(v_fvs_986_);
return v_res_996_;
}
}
lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* v_as_997_, lean_object* v_bs_998_, lean_object* v_i_999_, lean_object* v_cs_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = lean_array_get_size(v_as_997_);
v___x_1007_ = lean_nat_dec_lt(v_i_999_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
lean_dec(v_i_999_);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v_cs_1000_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1009_ = lean_array_get_size(v_bs_998_);
v___x_1010_ = lean_nat_dec_lt(v_i_999_, v___x_1009_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_dec(v_i_999_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_cs_1000_);
return v___x_1011_;
}
else
{
uint8_t v___x_1012_; uint8_t v___x_1013_; lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___f_1018_; lean_object* v_b_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1012_ = 0;
v___x_1013_ = 1;
v_a_1014_ = lean_array_fget_borrowed(v_as_997_, v_i_999_);
v___x_1015_ = lean_box(v___x_1012_);
v___x_1016_ = lean_box(v___x_1010_);
v___x_1017_ = lean_box(v___x_1013_);
lean_inc_n(v_a_1014_, 2);
v___f_1018_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1018_, 0, v___x_1015_);
lean_closure_set(v___f_1018_, 1, v___x_1016_);
lean_closure_set(v___f_1018_, 2, v___x_1017_);
lean_closure_set(v___f_1018_, 3, v_a_1014_);
v_b_1019_ = lean_array_fget_borrowed(v_bs_998_, v_i_999_);
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_a_1014_);
lean_inc(v_b_1019_);
v___x_1021_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_b_1019_, v___x_1020_, v___f_1018_, v___x_1012_, v___x_1012_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
if (lean_obj_tag(v___x_1021_) == 0)
{
lean_object* v_a_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_a_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_a_1022_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_add(v_i_999_, v___x_1023_);
lean_dec(v_i_999_);
v___x_1025_ = lean_array_push(v_cs_1000_, v_a_1022_);
v_i_999_ = v___x_1024_;
v_cs_1000_ = v___x_1025_;
goto _start;
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_cs_1000_);
lean_dec(v_i_999_);
v_a_1027_ = lean_ctor_get(v___x_1021_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1021_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1021_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1021_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_997_ = stack[0].m_obj;
lean_object* v_bs_998_ = stack[1].m_obj;
lean_object* v_i_999_ = stack[2].m_obj;
lean_object* v_cs_1000_ = stack[3].m_obj;
lean_object* v___y_1001_ = stack[4].m_obj;
lean_object* v___y_1002_ = stack[5].m_obj;
lean_object* v___y_1003_ = stack[6].m_obj;
lean_object* v___y_1004_ = stack[7].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_as_997_, v_bs_998_, v_i_999_, v_cs_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* v_as_1036_, lean_object* v_bs_1037_, lean_object* v_i_1038_, lean_object* v_cs_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_as_1036_, v_bs_1037_, v_i_1038_, v_cs_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec_ref(v_bs_1037_);
lean_dec_ref(v_as_1036_);
return v_res_1045_;
}
}
lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* v_matcherApp_1048_, lean_object* v_altAuxs_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
size_t v_sz_1056_; size_t v___x_1057_; lean_object* v___x_1058_; 
v_sz_1056_ = lean_array_size(v_altAuxs_1049_);
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_1056_, v___x_1057_, v_altAuxs_1049_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_1048_);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_1063_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v___x_1060_, v_a_1059_, v___x_1061_, v___x_1062_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v_a_1059_);
lean_dec_ref(v___x_1060_);
return v___x_1063_;
}
else
{
lean_dec_ref(v_matcherApp_1048_);
return v___x_1058_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_refineThrough___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_1048_ = stack[0].m_obj;
lean_object* v_altAuxs_1049_ = stack[1].m_obj;
lean_object* v_x_1050_ = stack[2].m_obj;
lean_object* v___y_1051_ = stack[3].m_obj;
lean_object* v___y_1052_ = stack[4].m_obj;
lean_object* v___y_1053_ = stack[5].m_obj;
lean_object* v___y_1054_ = stack[6].m_obj;
lean_object* v_res_1064_;
v_res_1064_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1048_, v_altAuxs_1049_, v_x_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
stack->m_obj
 = v_res_1064_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* v_matcherApp_1065_, lean_object* v_altAuxs_1066_, lean_object* v_x_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1065_, v_altAuxs_1066_, v_x_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec_ref(v_x_1067_);
return v_res_1073_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* v_motiveArgs_1074_, lean_object* v___x_1075_, lean_object* v_i_1076_, lean_object* v_a_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_zero_1083_; uint8_t v_isZero_1084_; 
v_zero_1083_ = lean_unsigned_to_nat(0u);
v_isZero_1084_ = lean_nat_dec_eq(v_i_1076_, v_zero_1083_);
if (v_isZero_1084_ == 1)
{
lean_object* v___x_1085_; 
lean_dec(v_i_1076_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v_a_1077_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v_one_1087_; lean_object* v_n_1088_; lean_object* v_motiveArg_1089_; lean_object* v_discr_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1086_ = l_Lean_instInhabitedExpr;
v_one_1087_ = lean_unsigned_to_nat(1u);
v_n_1088_ = lean_nat_sub(v_i_1076_, v_one_1087_);
lean_dec(v_i_1076_);
v_motiveArg_1089_ = lean_array_get_borrowed(v___x_1086_, v_motiveArgs_1074_, v_n_1088_);
v_discr_1090_ = lean_array_fget_borrowed(v___x_1075_, v_n_1088_);
v___x_1091_ = lean_box(0);
lean_inc(v_discr_1090_);
v___x_1092_ = l_Lean_Meta_kabstract(v_a_1077_, v_discr_1090_, v___x_1091_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = lean_expr_instantiate1(v_a_1093_, v_motiveArg_1089_);
lean_dec(v_a_1093_);
v_i_1076_ = v_n_1088_;
v_a_1077_ = v___x_1094_;
goto _start;
}
else
{
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1096_; 
v_a_1096_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1092_, 1);
v_i_1076_ = v_n_1088_;
v_a_1077_ = v_a_1096_;
goto _start;
}
else
{
lean_dec(v_n_1088_);
return v___x_1092_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_motiveArgs_1074_ = stack[0].m_obj;
lean_object* v___x_1075_ = stack[1].m_obj;
lean_object* v_i_1076_ = stack[2].m_obj;
lean_object* v_a_1077_ = stack[3].m_obj;
lean_object* v___y_1078_ = stack[4].m_obj;
lean_object* v___y_1079_ = stack[5].m_obj;
lean_object* v___y_1080_ = stack[6].m_obj;
lean_object* v___y_1081_ = stack[7].m_obj;
lean_object* v_res_1098_;
v_res_1098_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1074_, v___x_1075_, v_i_1076_, v_a_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
stack->m_obj
 = v_res_1098_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* v_motiveArgs_1099_, lean_object* v___x_1100_, lean_object* v_i_1101_, lean_object* v_a_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1099_, v___x_1100_, v_i_1101_, v_a_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_motiveArgs_1099_);
return v_res_1108_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
v___x_1111_ = l_Lean_stringToMessageData(v___x_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1115_, lean_object* v_discrs_1116_, lean_object* v_e_1117_, lean_object* v_toMatcherInfo_1118_, lean_object* v_params_1119_, lean_object* v_matcherName_1120_, lean_object* v_matcherLevels_1121_, lean_object* v_motiveArgs_1122_, lean_object* v___motiveBody_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v_matcherLevels_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; 
v___x_1228_ = lean_array_get_size(v_motiveArgs_1122_);
v___x_1229_ = lean_array_get_size(v_discrs_1116_);
v___x_1230_ = lean_nat_dec_eq(v___x_1228_, v___x_1229_);
if (v___x_1230_ == 0)
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_matcherLevels_1121_);
lean_dec(v_matcherName_1120_);
lean_dec_ref(v_e_1117_);
lean_dec_ref(v___f_1115_);
v___x_1231_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
v___x_1232_ = l_Nat_reprFast(v___x_1229_);
v___x_1233_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
v___x_1234_ = l_Lean_MessageData_ofFormat(v___x_1233_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1231_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_1237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1235_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1237_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1238_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
else
{
v___y_1198_ = v___y_1124_;
v___y_1199_ = v___y_1125_;
v___y_1200_ = v___y_1126_;
v___y_1201_ = v___y_1127_;
goto v___jp_1197_;
}
v___jp_1129_:
{
lean_object* v___x_1137_; 
lean_inc(v___y_1136_);
lean_inc_ref(v___y_1135_);
lean_inc(v___y_1134_);
lean_inc_ref(v___y_1133_);
v___x_1137_ = lean_infer_type(v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_a_1138_, v___y_1131_, v___y_1130_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
return v___x_1139_;
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v___y_1131_);
v_a_1140_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1137_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1137_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
v___jp_1148_:
{
uint8_t v___x_1158_; uint8_t v___x_1159_; uint8_t v___x_1160_; lean_object* v___x_1161_; 
v___x_1158_ = 0;
v___x_1159_ = 1;
v___x_1160_ = 1;
v___x_1161_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1122_, v___y_1152_, v___x_1158_, v___x_1159_, v___x_1158_, v___x_1159_, v___x_1160_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v___x_1161_, 1);
v___x_1163_ = lean_array_to_list(v_matcherLevels_1153_);
v___x_1164_ = l_Lean_mkConst(v___y_1151_, v___x_1163_);
v___x_1165_ = l_Lean_mkAppN(v___x_1164_, v___y_1150_);
v___x_1166_ = l_Lean_Expr_app___override(v___x_1165_, v_a_1162_);
v___x_1167_ = l_Lean_mkAppN(v___x_1166_, v___y_1149_);
lean_inc_ref(v___x_1167_);
v___x_1168_ = l_Lean_Meta_isTypeCorrect(v___x_1167_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; uint8_t v___x_1170_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v___x_1170_ = lean_unbox(v_a_1169_);
lean_dec(v_a_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec_ref(v___x_1167_);
lean_dec_ref(v___f_1115_);
v___x_1171_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
v___x_1172_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1171_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1172_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1172_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
else
{
v___y_1130_ = v___x_1158_;
v___y_1131_ = v___f_1115_;
v___y_1132_ = v___x_1167_;
v___y_1133_ = v___y_1154_;
v___y_1134_ = v___y_1155_;
v___y_1135_ = v___y_1156_;
v___y_1136_ = v___y_1157_;
goto v___jp_1129_;
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec_ref(v___x_1167_);
lean_dec_ref(v___f_1115_);
v_a_1181_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1168_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1168_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_matcherLevels_1153_);
lean_dec(v___y_1151_);
lean_dec_ref(v___f_1115_);
v_a_1189_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1161_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1161_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
v___jp_1197_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = lean_array_get_size(v_discrs_1116_);
v___x_1203_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1122_, v_discrs_1116_, v___x_1202_, v_e_1117_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc_n(v_a_1204_, 2);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1205_ = l_Lean_Meta_mkEq(v_a_1204_, v_a_1204_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_uElimPos_x3f_1206_; 
v_uElimPos_x3f_1206_ = lean_ctor_get(v_toMatcherInfo_1118_, 3);
if (lean_obj_tag(v_uElimPos_x3f_1206_) == 0)
{
lean_object* v_a_1207_; 
v_a_1207_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1207_);
lean_dec_ref_known(v___x_1205_, 1);
v___y_1149_ = v_discrs_1116_;
v___y_1150_ = v_params_1119_;
v___y_1151_ = v_matcherName_1120_;
v___y_1152_ = v_a_1207_;
v_matcherLevels_1153_ = v_matcherLevels_1121_;
v___y_1154_ = v___y_1198_;
v___y_1155_ = v___y_1199_;
v___y_1156_ = v___y_1200_;
v___y_1157_ = v___y_1201_;
goto v___jp_1148_;
}
else
{
lean_object* v_a_1208_; lean_object* v_val_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v_a_1208_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_a_1208_);
lean_dec_ref_known(v___x_1205_, 1);
v_val_1209_ = lean_ctor_get(v_uElimPos_x3f_1206_, 0);
v___x_1210_ = lean_box(0);
v___x_1211_ = lean_array_set(v_matcherLevels_1121_, v_val_1209_, v___x_1210_);
v___y_1149_ = v_discrs_1116_;
v___y_1150_ = v_params_1119_;
v___y_1151_ = v_matcherName_1120_;
v___y_1152_ = v_a_1208_;
v_matcherLevels_1153_ = v___x_1211_;
v___y_1154_ = v___y_1198_;
v___y_1155_ = v___y_1199_;
v___y_1156_ = v___y_1200_;
v___y_1157_ = v___y_1201_;
goto v___jp_1148_;
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v_matcherLevels_1121_);
lean_dec(v_matcherName_1120_);
lean_dec_ref(v___f_1115_);
v_a_1212_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1205_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1205_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec_ref(v_matcherLevels_1121_);
lean_dec(v_matcherName_1120_);
lean_dec_ref(v___f_1115_);
v_a_1220_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1203_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1203_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_refineThrough___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_1115_ = stack[0].m_obj;
lean_object* v_discrs_1116_ = stack[1].m_obj;
lean_object* v_e_1117_ = stack[2].m_obj;
lean_object* v_toMatcherInfo_1118_ = stack[3].m_obj;
lean_object* v_params_1119_ = stack[4].m_obj;
lean_object* v_matcherName_1120_ = stack[5].m_obj;
lean_object* v_matcherLevels_1121_ = stack[6].m_obj;
lean_object* v_motiveArgs_1122_ = stack[7].m_obj;
lean_object* v___motiveBody_1123_ = stack[8].m_obj;
lean_object* v___y_1124_ = stack[9].m_obj;
lean_object* v___y_1125_ = stack[10].m_obj;
lean_object* v___y_1126_ = stack[11].m_obj;
lean_object* v___y_1127_ = stack[12].m_obj;
lean_object* v_res_1247_;
v_res_1247_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1115_, v_discrs_1116_, v_e_1117_, v_toMatcherInfo_1118_, v_params_1119_, v_matcherName_1120_, v_matcherLevels_1121_, v_motiveArgs_1122_, v___motiveBody_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
stack->m_obj
 = v_res_1247_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1248_, lean_object* v_discrs_1249_, lean_object* v_e_1250_, lean_object* v_toMatcherInfo_1251_, lean_object* v_params_1252_, lean_object* v_matcherName_1253_, lean_object* v_matcherLevels_1254_, lean_object* v_motiveArgs_1255_, lean_object* v___motiveBody_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1248_, v_discrs_1249_, v_e_1250_, v_toMatcherInfo_1251_, v_params_1252_, v_matcherName_1253_, v_matcherLevels_1254_, v_motiveArgs_1255_, v___motiveBody_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___motiveBody_1256_);
lean_dec_ref(v_motiveArgs_1255_);
lean_dec_ref(v_params_1252_);
lean_dec_ref(v_toMatcherInfo_1251_);
lean_dec_ref(v_discrs_1249_);
return v_res_1262_;
}
}
lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* v_matcherApp_1263_, lean_object* v_e_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_toMatcherInfo_1270_; lean_object* v_matcherName_1271_; lean_object* v_matcherLevels_1272_; lean_object* v_params_1273_; lean_object* v_motive_1274_; lean_object* v_discrs_1275_; lean_object* v___f_1276_; lean_object* v___f_1277_; uint8_t v___x_1278_; lean_object* v___x_1279_; 
v_toMatcherInfo_1270_ = lean_ctor_get(v_matcherApp_1263_, 0);
lean_inc_ref(v_toMatcherInfo_1270_);
v_matcherName_1271_ = lean_ctor_get(v_matcherApp_1263_, 1);
lean_inc(v_matcherName_1271_);
v_matcherLevels_1272_ = lean_ctor_get(v_matcherApp_1263_, 2);
lean_inc_ref(v_matcherLevels_1272_);
v_params_1273_ = lean_ctor_get(v_matcherApp_1263_, 3);
lean_inc_ref(v_params_1273_);
v_motive_1274_ = lean_ctor_get(v_matcherApp_1263_, 4);
lean_inc_ref(v_motive_1274_);
v_discrs_1275_ = lean_ctor_get(v_matcherApp_1263_, 5);
lean_inc_ref(v_discrs_1275_);
v___f_1276_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1276_, 0, v_matcherApp_1263_);
v___f_1277_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1277_, 0, v___f_1276_);
lean_closure_set(v___f_1277_, 1, v_discrs_1275_);
lean_closure_set(v___f_1277_, 2, v_e_1264_);
lean_closure_set(v___f_1277_, 3, v_toMatcherInfo_1270_);
lean_closure_set(v___f_1277_, 4, v_params_1273_);
lean_closure_set(v___f_1277_, 5, v_matcherName_1271_);
lean_closure_set(v___f_1277_, 6, v_matcherLevels_1272_);
v___x_1278_ = 0;
v___x_1279_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_1274_, v___f_1277_, v___x_1278_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
return v___x_1279_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_refineThrough_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_1263_ = stack[0].m_obj;
lean_object* v_e_1264_ = stack[1].m_obj;
lean_object* v_a_1265_ = stack[2].m_obj;
lean_object* v_a_1266_ = stack[3].m_obj;
lean_object* v_a_1267_ = stack[4].m_obj;
lean_object* v_a_1268_ = stack[5].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1263_, v_e_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* v_matcherApp_1281_, lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1281_, v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
return v_res_1288_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* v_motiveArgs_1289_, lean_object* v___x_1290_, lean_object* v_n_1291_, lean_object* v_i_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1289_, v___x_1290_, v_i_1292_, v_a_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_motiveArgs_1289_ = stack[0].m_obj;
lean_object* v___x_1290_ = stack[1].m_obj;
lean_object* v_n_1291_ = stack[2].m_obj;
lean_object* v_i_1292_ = stack[3].m_obj;
lean_object* v_a_1294_ = stack[5].m_obj;
lean_object* v___y_1295_ = stack[6].m_obj;
lean_object* v___y_1296_ = stack[7].m_obj;
lean_object* v___y_1297_ = stack[8].m_obj;
lean_object* v___y_1298_ = stack[9].m_obj;
lean_object* v_res_1301_;
v_res_1301_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v_motiveArgs_1289_, v___x_1290_, v_n_1291_, v_i_1292_, lean_box(0), v_a_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
stack->m_obj
 = v_res_1301_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* v_motiveArgs_1302_, lean_object* v___x_1303_, lean_object* v_n_1304_, lean_object* v_i_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v_motiveArgs_1302_, v___x_1303_, v_n_1304_, v_i_1305_, v_a_1306_, v_a_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v_n_1304_);
lean_dec_ref(v___x_1303_);
lean_dec_ref(v_motiveArgs_1302_);
return v_res_1313_;
}
}
lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* v_matcherApp_1314_, lean_object* v_e_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v___x_1321_; 
v___x_1321_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1314_, v_e_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1330_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1330_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v_a_1322_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1346_; 
v_a_1331_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1333_ = v___x_1321_;
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1321_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1346_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
uint8_t v___y_1336_; uint8_t v___x_1344_; 
v___x_1344_ = l_Lean_Exception_isInterrupt(v_a_1331_);
if (v___x_1344_ == 0)
{
uint8_t v___x_1345_; 
lean_inc(v_a_1331_);
v___x_1345_ = l_Lean_Exception_isRuntime(v_a_1331_);
v___y_1336_ = v___x_1345_;
goto v___jp_1335_;
}
else
{
v___y_1336_ = v___x_1344_;
goto v___jp_1335_;
}
v___jp_1335_:
{
if (v___y_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1339_; 
lean_dec(v_a_1331_);
v___x_1337_ = lean_box(0);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1337_);
v___x_1339_ = v___x_1333_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
else
{
lean_object* v___x_1342_; 
if (v_isShared_1334_ == 0)
{
v___x_1342_ = v___x_1333_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1331_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_refineThrough_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_1314_ = stack[0].m_obj;
lean_object* v_e_1315_ = stack[1].m_obj;
lean_object* v_a_1316_ = stack[2].m_obj;
lean_object* v_a_1317_ = stack[3].m_obj;
lean_object* v_a_1318_ = stack[4].m_obj;
lean_object* v_a_1319_ = stack[5].m_obj;
lean_object* v_res_1347_;
v_res_1347_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1314_, v_e_1315_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
stack->m_obj
 = v_res_1347_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* v_matcherApp_1348_, lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1348_, v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
return v_res_1355_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1356_, lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_keyedConfig_1363_; uint8_t v_trackZetaDelta_1364_; lean_object* v_zetaDeltaSet_1365_; lean_object* v_localInstances_1366_; lean_object* v_defEqCtx_x3f_1367_; lean_object* v_synthPendingDepth_1368_; lean_object* v_customCanUnfoldPredicate_x3f_1369_; uint8_t v_univApprox_1370_; uint8_t v_inTypeClassResolution_1371_; uint8_t v_cacheInferType_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v_keyedConfig_1363_ = lean_ctor_get(v___y_1358_, 0);
v_trackZetaDelta_1364_ = lean_ctor_get_uint8(v___y_1358_, sizeof(void*)*7);
v_zetaDeltaSet_1365_ = lean_ctor_get(v___y_1358_, 1);
v_localInstances_1366_ = lean_ctor_get(v___y_1358_, 3);
v_defEqCtx_x3f_1367_ = lean_ctor_get(v___y_1358_, 4);
v_synthPendingDepth_1368_ = lean_ctor_get(v___y_1358_, 5);
v_customCanUnfoldPredicate_x3f_1369_ = lean_ctor_get(v___y_1358_, 6);
v_univApprox_1370_ = lean_ctor_get_uint8(v___y_1358_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1371_ = lean_ctor_get_uint8(v___y_1358_, sizeof(void*)*7 + 2);
v_cacheInferType_1372_ = lean_ctor_get_uint8(v___y_1358_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1369_);
lean_inc(v_synthPendingDepth_1368_);
lean_inc(v_defEqCtx_x3f_1367_);
lean_inc_ref(v_localInstances_1366_);
lean_inc(v_zetaDeltaSet_1365_);
lean_inc_ref(v_keyedConfig_1363_);
v___x_1373_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1373_, 0, v_keyedConfig_1363_);
lean_ctor_set(v___x_1373_, 1, v_zetaDeltaSet_1365_);
lean_ctor_set(v___x_1373_, 2, v_lctx_1356_);
lean_ctor_set(v___x_1373_, 3, v_localInstances_1366_);
lean_ctor_set(v___x_1373_, 4, v_defEqCtx_x3f_1367_);
lean_ctor_set(v___x_1373_, 5, v_synthPendingDepth_1368_);
lean_ctor_set(v___x_1373_, 6, v_customCanUnfoldPredicate_x3f_1369_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7, v_trackZetaDelta_1364_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7 + 1, v_univApprox_1370_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*7 + 3, v_cacheInferType_1372_);
lean_inc(v___y_1361_);
lean_inc_ref(v___y_1360_);
lean_inc(v___y_1359_);
v___x_1374_ = lean_apply_5(v_x_1357_, v___x_1373_, v___y_1359_, v___y_1360_, v___y_1361_, lean_box(0));
return v___x_1374_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1356_ = stack[0].m_obj;
lean_object* v_x_1357_ = stack[1].m_obj;
lean_object* v___y_1358_ = stack[2].m_obj;
lean_object* v___y_1359_ = stack[3].m_obj;
lean_object* v___y_1360_ = stack[4].m_obj;
lean_object* v___y_1361_ = stack[5].m_obj;
lean_object* v_res_1375_;
v_res_1375_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1356_, v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
stack->m_obj
 = v_res_1375_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1376_, lean_object* v_x_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1376_, v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
return v_res_1383_;
}
}
lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1384_, lean_object* v_lctx_1385_, lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1385_, v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_1385_ = stack[1].m_obj;
lean_object* v_x_1386_ = stack[2].m_obj;
lean_object* v___y_1387_ = stack[3].m_obj;
lean_object* v___y_1388_ = stack[4].m_obj;
lean_object* v___y_1389_ = stack[5].m_obj;
lean_object* v___y_1390_ = stack[6].m_obj;
lean_object* v_res_1393_;
v_res_1393_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_box(0), v_lctx_1385_, v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
stack->m_obj
 = v_res_1393_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1394_, lean_object* v_lctx_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1394_, v_lctx_1395_, v_x_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1402_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1403_, size_t v_i_1404_, size_t v_stop_1405_, lean_object* v_b_1406_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_usize_dec_eq(v_i_1404_, v_stop_1405_);
if (v___x_1407_ == 0)
{
lean_object* v___x_1408_; lean_object* v_fst_1409_; lean_object* v_snd_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; size_t v___x_1413_; size_t v___x_1414_; 
v___x_1408_ = lean_array_uget_borrowed(v_as_1403_, v_i_1404_);
v_fst_1409_ = lean_ctor_get(v___x_1408_, 0);
v_snd_1410_ = lean_ctor_get(v___x_1408_, 1);
v___x_1411_ = l_Lean_Expr_fvarId_x21(v_fst_1409_);
lean_inc(v_snd_1410_);
v___x_1412_ = l_Lean_LocalContext_setUserName(v_b_1406_, v___x_1411_, v_snd_1410_);
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1404_, v___x_1413_);
v_i_1404_ = v___x_1414_;
v_b_1406_ = v___x_1412_;
goto _start;
}
else
{
return v_b_1406_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1403_ = stack[0].m_obj;
size_t v_i_1404_ = stack[1].m_num;
size_t v_stop_1405_ = stack[2].m_num;
lean_object* v_b_1406_ = stack[3].m_obj;
lean_object* v_res_1416_;
v_res_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1403_, v_i_1404_, v_stop_1405_, v_b_1406_);
stack->m_obj
 = v_res_1416_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1417_, lean_object* v_i_1418_, lean_object* v_stop_1419_, lean_object* v_b_1420_){
_start:
{
size_t v_i_boxed_1421_; size_t v_stop_boxed_1422_; lean_object* v_res_1423_; 
v_i_boxed_1421_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_stop_boxed_1422_ = lean_unbox_usize(v_stop_1419_);
lean_dec(v_stop_1419_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1417_, v_i_boxed_1421_, v_stop_boxed_1422_, v_b_1420_);
lean_dec_ref(v_as_1417_);
return v_res_1423_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1424_, lean_object* v_names_1425_, lean_object* v_k_1426_, lean_object* v_a_1427_, lean_object* v_a_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
lean_object* v_lctx_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v_lctx_1432_ = lean_ctor_get(v_a_1427_, 2);
v___x_1433_ = l_Array_zip___redArg(v_fvars_1424_, v_names_1425_);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_array_get_size(v___x_1433_);
v___x_1436_ = lean_nat_dec_lt(v___x_1434_, v___x_1435_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_dec_ref(v___x_1433_);
lean_inc_ref(v_lctx_1432_);
v___x_1437_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1432_, v_k_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1437_;
}
else
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_le(v___x_1435_, v___x_1435_);
if (v___x_1438_ == 0)
{
if (v___x_1436_ == 0)
{
lean_object* v___x_1439_; 
lean_dec_ref(v___x_1433_);
lean_inc_ref(v_lctx_1432_);
v___x_1439_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1432_, v_k_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1439_;
}
else
{
size_t v___x_1440_; size_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1440_ = ((size_t)0ULL);
v___x_1441_ = lean_usize_of_nat(v___x_1435_);
lean_inc_ref(v_lctx_1432_);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1433_, v___x_1440_, v___x_1441_, v_lctx_1432_);
lean_dec_ref(v___x_1433_);
v___x_1443_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1442_, v_k_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1443_;
}
}
else
{
size_t v___x_1444_; size_t v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1444_ = ((size_t)0ULL);
v___x_1445_ = lean_usize_of_nat(v___x_1435_);
lean_inc_ref(v_lctx_1432_);
v___x_1446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1433_, v___x_1444_, v___x_1445_, v_lctx_1432_);
lean_dec_ref(v___x_1433_);
v___x_1447_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1446_, v_k_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
return v___x_1447_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1424_ = stack[0].m_obj;
lean_object* v_names_1425_ = stack[1].m_obj;
lean_object* v_k_1426_ = stack[2].m_obj;
lean_object* v_a_1427_ = stack[3].m_obj;
lean_object* v_a_1428_ = stack[4].m_obj;
lean_object* v_a_1429_ = stack[5].m_obj;
lean_object* v_a_1430_ = stack[6].m_obj;
lean_object* v_res_1448_;
v_res_1448_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1424_, v_names_1425_, v_k_1426_, v_a_1427_, v_a_1428_, v_a_1429_, v_a_1430_);
stack->m_obj
 = v_res_1448_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* v_fvars_1449_, lean_object* v_names_1450_, lean_object* v_k_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1449_, v_names_1450_, v_k_1451_, v_a_1452_, v_a_1453_, v_a_1454_, v_a_1455_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec(v_a_1453_);
lean_dec_ref(v_a_1452_);
lean_dec_ref(v_names_1450_);
lean_dec_ref(v_fvars_1449_);
return v_res_1457_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* v_00_u03b1_1458_, lean_object* v_fvars_1459_, lean_object* v_names_1460_, lean_object* v_k_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1459_, v_names_1460_, v_k_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1459_ = stack[1].m_obj;
lean_object* v_names_1460_ = stack[2].m_obj;
lean_object* v_k_1461_ = stack[3].m_obj;
lean_object* v_a_1462_ = stack[4].m_obj;
lean_object* v_a_1463_ = stack[5].m_obj;
lean_object* v_a_1464_ = stack[6].m_obj;
lean_object* v_a_1465_ = stack[7].m_obj;
lean_object* v_res_1468_;
v_res_1468_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_box(0), v_fvars_1459_, v_names_1460_, v_k_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_);
stack->m_obj
 = v_res_1468_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_fvars_1470_, lean_object* v_names_1471_, lean_object* v_k_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(v_00_u03b1_1469_, v_fvars_1470_, v_names_1471_, v_k_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_);
lean_dec(v_a_1476_);
lean_dec_ref(v_a_1475_);
lean_dec(v_a_1474_);
lean_dec_ref(v_a_1473_);
lean_dec_ref(v_names_1471_);
lean_dec_ref(v_fvars_1470_);
return v_res_1478_;
}
}
lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* v_k_1479_, lean_object* v_fvars_1480_, lean_object* v_names_1481_, lean_object* v_runInBase_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = lean_apply_2(v_runInBase_1482_, lean_box(0), v_k_1479_);
v___x_1489_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1480_, v_names_1481_, v___x_1488_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
return v___x_1489_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1479_ = stack[0].m_obj;
lean_object* v_fvars_1480_ = stack[1].m_obj;
lean_object* v_names_1481_ = stack[2].m_obj;
lean_object* v_runInBase_1482_ = stack[3].m_obj;
lean_object* v___y_1483_ = stack[4].m_obj;
lean_object* v___y_1484_ = stack[5].m_obj;
lean_object* v___y_1485_ = stack[6].m_obj;
lean_object* v___y_1486_ = stack[7].m_obj;
lean_object* v_res_1490_;
v_res_1490_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1479_, v_fvars_1480_, v_names_1481_, v_runInBase_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
stack->m_obj
 = v_res_1490_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* v_k_1491_, lean_object* v_fvars_1492_, lean_object* v_names_1493_, lean_object* v_runInBase_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1491_, v_fvars_1492_, v_names_1493_, v_runInBase_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec_ref(v_names_1493_);
lean_dec_ref(v_fvars_1492_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* v_inst_1501_, lean_object* v_inst_1502_, lean_object* v_fvars_1503_, lean_object* v_names_1504_, lean_object* v_k_1505_){
_start:
{
lean_object* v_toBind_1506_; lean_object* v_liftWith_1507_; lean_object* v_restoreM_1508_; lean_object* v___f_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_toBind_1506_ = lean_ctor_get(v_inst_1502_, 1);
lean_inc(v_toBind_1506_);
lean_dec_ref(v_inst_1502_);
v_liftWith_1507_ = lean_ctor_get(v_inst_1501_, 0);
lean_inc(v_liftWith_1507_);
v_restoreM_1508_ = lean_ctor_get(v_inst_1501_, 1);
lean_inc(v_restoreM_1508_);
lean_dec_ref(v_inst_1501_);
v___f_1509_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1509_, 0, v_k_1505_);
lean_closure_set(v___f_1509_, 1, v_fvars_1503_);
lean_closure_set(v___f_1509_, 2, v_names_1504_);
v___x_1510_ = lean_apply_2(v_liftWith_1507_, lean_box(0), v___f_1509_);
v___x_1511_ = lean_apply_1(v_restoreM_1508_, lean_box(0));
v___x_1512_ = lean_apply_4(v_toBind_1506_, lean_box(0), lean_box(0), v___x_1510_, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* v_n_1513_, lean_object* v_inst_1514_, lean_object* v_inst_1515_, lean_object* v_00_u03b1_1516_, lean_object* v_fvars_1517_, lean_object* v_names_1518_, lean_object* v_k_1519_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_1514_, v_inst_1515_, v_fvars_1517_, v_names_1518_, v_k_1519_);
return v___x_1520_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* v_k_1521_, lean_object* v_runInBase_1522_, lean_object* v_ys_1523_, lean_object* v_args_1524_, lean_object* v___mask_1525_, lean_object* v___bodyType_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_apply_2(v_k_1521_, v_ys_1523_, v_args_1524_);
lean_inc(v___y_1530_);
lean_inc_ref(v___y_1529_);
lean_inc(v___y_1528_);
lean_inc_ref(v___y_1527_);
v___x_1533_ = lean_apply_7(v_runInBase_1522_, lean_box(0), v___x_1532_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, lean_box(0));
return v___x_1533_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1521_ = stack[0].m_obj;
lean_object* v_runInBase_1522_ = stack[1].m_obj;
lean_object* v_ys_1523_ = stack[2].m_obj;
lean_object* v_args_1524_ = stack[3].m_obj;
lean_object* v___mask_1525_ = stack[4].m_obj;
lean_object* v___bodyType_1526_ = stack[5].m_obj;
lean_object* v___y_1527_ = stack[6].m_obj;
lean_object* v___y_1528_ = stack[7].m_obj;
lean_object* v___y_1529_ = stack[8].m_obj;
lean_object* v___y_1530_ = stack[9].m_obj;
lean_object* v_res_1534_;
v_res_1534_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1521_, v_runInBase_1522_, v_ys_1523_, v_args_1524_, v___mask_1525_, v___bodyType_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
stack->m_obj
 = v_res_1534_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* v_k_1535_, lean_object* v_runInBase_1536_, lean_object* v_ys_1537_, lean_object* v_args_1538_, lean_object* v___mask_1539_, lean_object* v___bodyType_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1535_, v_runInBase_1536_, v_ys_1537_, v_args_1538_, v___mask_1539_, v___bodyType_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec_ref(v___bodyType_1540_);
lean_dec_ref(v___mask_1539_);
return v_res_1546_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* v_k_1547_, lean_object* v_origAltType_1548_, lean_object* v_altInfo_1549_, lean_object* v_runInBase_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___f_1556_; lean_object* v___x_1557_; 
v___f_1556_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1556_, 0, v_k_1547_);
lean_closure_set(v___f_1556_, 1, v_runInBase_1550_);
v___x_1557_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_1548_, v_altInfo_1549_, v___f_1556_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1557_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1547_ = stack[0].m_obj;
lean_object* v_origAltType_1548_ = stack[1].m_obj;
lean_object* v_altInfo_1549_ = stack[2].m_obj;
lean_object* v_runInBase_1550_ = stack[3].m_obj;
lean_object* v___y_1551_ = stack[4].m_obj;
lean_object* v___y_1552_ = stack[5].m_obj;
lean_object* v___y_1553_ = stack[6].m_obj;
lean_object* v___y_1554_ = stack[7].m_obj;
lean_object* v_res_1558_;
v_res_1558_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1547_, v_origAltType_1548_, v_altInfo_1549_, v_runInBase_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
stack->m_obj
 = v_res_1558_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* v_k_1559_, lean_object* v_origAltType_1560_, lean_object* v_altInfo_1561_, lean_object* v_runInBase_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1559_, v_origAltType_1560_, v_altInfo_1561_, v_runInBase_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_origAltType_1571_, lean_object* v_altInfo_1572_, lean_object* v_k_1573_){
_start:
{
lean_object* v_toBind_1574_; lean_object* v_liftWith_1575_; lean_object* v_restoreM_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_toBind_1574_ = lean_ctor_get(v_inst_1569_, 1);
lean_inc(v_toBind_1574_);
lean_dec_ref(v_inst_1569_);
v_liftWith_1575_ = lean_ctor_get(v_inst_1570_, 0);
lean_inc(v_liftWith_1575_);
v_restoreM_1576_ = lean_ctor_get(v_inst_1570_, 1);
lean_inc(v_restoreM_1576_);
lean_dec_ref(v_inst_1570_);
v___f_1577_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1577_, 0, v_k_1573_);
lean_closure_set(v___f_1577_, 1, v_origAltType_1571_);
lean_closure_set(v___f_1577_, 2, v_altInfo_1572_);
v___x_1578_ = lean_apply_2(v_liftWith_1575_, lean_box(0), v___f_1577_);
v___x_1579_ = lean_apply_1(v_restoreM_1576_, lean_box(0));
v___x_1580_ = lean_apply_4(v_toBind_1574_, lean_box(0), lean_box(0), v___x_1578_, v___x_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* v_n_1581_, lean_object* v_inst_1582_, lean_object* v_inst_1583_, lean_object* v_00_u03b1_1584_, lean_object* v_origAltType_1585_, lean_object* v_altInfo_1586_, lean_object* v_k_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_1582_, v_inst_1583_, v_origAltType_1585_, v_altInfo_1586_, v_k_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object* v_fvars_1589_){
_start:
{
lean_object* v_args_1590_; lean_object* v_discrEqs_1591_; lean_object* v___x_1592_; 
v_args_1590_ = lean_ctor_get(v_fvars_1589_, 0);
lean_inc_ref(v_args_1590_);
v_discrEqs_1591_ = lean_ctor_get(v_fvars_1589_, 3);
lean_inc_ref(v_discrEqs_1591_);
lean_dec_ref(v_fvars_1589_);
v___x_1592_ = l_Array_append___redArg(v_args_1590_, v_discrEqs_1591_);
lean_dec_ref(v_discrEqs_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object* v_fvars_1593_){
_start:
{
lean_object* v_fields_1594_; lean_object* v_overlaps_1595_; lean_object* v_discrEqs_1596_; lean_object* v_extraEqs_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_fields_1594_ = lean_ctor_get(v_fvars_1593_, 1);
lean_inc_ref(v_fields_1594_);
v_overlaps_1595_ = lean_ctor_get(v_fvars_1593_, 2);
lean_inc_ref(v_overlaps_1595_);
v_discrEqs_1596_ = lean_ctor_get(v_fvars_1593_, 3);
lean_inc_ref(v_discrEqs_1596_);
v_extraEqs_1597_ = lean_ctor_get(v_fvars_1593_, 4);
lean_inc_ref(v_extraEqs_1597_);
lean_dec_ref(v_fvars_1593_);
v___x_1598_ = l_Array_append___redArg(v_fields_1594_, v_overlaps_1595_);
lean_dec_ref(v_overlaps_1595_);
v___x_1599_ = l_Array_append___redArg(v___x_1598_, v_discrEqs_1596_);
lean_dec_ref(v_discrEqs_1596_);
v___x_1600_ = l_Array_append___redArg(v___x_1599_, v_extraEqs_1597_);
lean_dec_ref(v_extraEqs_1597_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1601_, lean_object* v_inst_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_1605_ = l_Lean_throwError___redArg(v_inst_1601_, v_inst_1602_, v___x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_x_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1606_, v_inst_1607_, v_x_1608_);
lean_dec_ref(v_x_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1610_, lean_object* v_x_1611_){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1612_ = l_Lean_Expr_fvarId_x21(v_x_1611_);
v___x_1613_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1613_, 0, v___x_1612_);
v___x_1614_ = lean_apply_2(v_inst_1610_, lean_box(0), v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1615_, v_x_1616_);
lean_dec_ref(v_x_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1618_, lean_object* v___f_1619_, lean_object* v_xs_1620_, lean_object* v_x_1621_){
_start:
{
size_t v_sz_1622_; size_t v___x_1623_; lean_object* v___x_1624_; 
v_sz_1622_ = lean_array_size(v_xs_1620_);
v___x_1623_ = ((size_t)0ULL);
v___x_1624_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1618_, v___f_1619_, v_sz_1622_, v___x_1623_, v_xs_1620_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1625_, lean_object* v___f_1626_, lean_object* v_xs_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1625_, v___f_1626_, v_xs_1627_, v_x_1628_);
lean_dec_ref(v_x_1628_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_fst_1630_, lean_object* v_fst_1631_, lean_object* v___x_1632_, lean_object* v___x_1633_, lean_object* v_toPure_1634_, lean_object* v_____do__lift_1635_){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1636_ = lean_array_push(v_fst_1630_, v_____do__lift_1635_);
v___x_1637_ = lean_nat_add(v_fst_1631_, v___x_1632_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___x_1633_);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1636_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
v___x_1641_ = lean_apply_2(v_toPure_1634_, lean_box(0), v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object* v_fst_1642_, lean_object* v_fst_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v_toPure_1646_, lean_object* v_____do__lift_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__3(v_fst_1642_, v_fst_1643_, v___x_1644_, v___x_1645_, v_toPure_1646_, v_____do__lift_1647_);
lean_dec(v___x_1644_);
lean_dec(v_fst_1643_);
return v_res_1648_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(uint8_t v_val_1649_, lean_object* v_a_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
if (v_val_1649_ == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Meta_mkEqRefl(v_a_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_Meta_mkHEqRefl(v_a_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1657_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_val_1649_ = stack[0].m_num;
lean_object* v_a_1650_ = stack[1].m_obj;
lean_object* v___y_1651_ = stack[2].m_obj;
lean_object* v___y_1652_ = stack[3].m_obj;
lean_object* v___y_1653_ = stack[4].m_obj;
lean_object* v___y_1654_ = stack[5].m_obj;
lean_object* v_res_1658_;
v_res_1658_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(v_val_1649_, v_a_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
stack->m_obj
 = v_res_1658_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object* v_val_1659_, lean_object* v_a_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
uint8_t v_val_12231__boxed_1666_; lean_object* v_res_1667_; 
v_val_12231__boxed_1666_ = lean_unbox(v_val_1659_);
v_res_1667_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(v_val_12231__boxed_1666_, v_a_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec_ref(v___y_1661_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_toPure_1668_, lean_object* v_inst_1669_, lean_object* v_toBind_1670_, lean_object* v_a_1671_, lean_object* v_x_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v_snd_1674_; lean_object* v_snd_1675_; lean_object* v_fst_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1724_; 
v_snd_1674_ = lean_ctor_get(v___y_1673_, 1);
lean_inc(v_snd_1674_);
v_snd_1675_ = lean_ctor_get(v_snd_1674_, 1);
lean_inc(v_snd_1675_);
v_fst_1676_ = lean_ctor_get(v___y_1673_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___y_1673_);
if (v_isSharedCheck_1724_ == 0)
{
lean_object* v_unused_1725_; 
v_unused_1725_ = lean_ctor_get(v___y_1673_, 1);
lean_dec(v_unused_1725_);
v___x_1678_ = v___y_1673_;
v_isShared_1679_ = v_isSharedCheck_1724_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_fst_1676_);
lean_dec(v___y_1673_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1724_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v_fst_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1722_; 
v_fst_1680_ = lean_ctor_get(v_snd_1674_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_snd_1674_);
if (v_isSharedCheck_1722_ == 0)
{
lean_object* v_unused_1723_; 
v_unused_1723_ = lean_ctor_get(v_snd_1674_, 1);
lean_dec(v_unused_1723_);
v___x_1682_ = v_snd_1674_;
v_isShared_1683_ = v_isSharedCheck_1722_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_fst_1680_);
lean_dec(v_snd_1674_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1722_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v_array_1684_; lean_object* v_start_1685_; lean_object* v_stop_1686_; uint8_t v___x_1687_; 
v_array_1684_ = lean_ctor_get(v_snd_1675_, 0);
v_start_1685_ = lean_ctor_get(v_snd_1675_, 1);
v_stop_1686_ = lean_ctor_get(v_snd_1675_, 2);
v___x_1687_ = lean_nat_dec_lt(v_start_1685_, v_stop_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1689_; 
lean_dec_ref(v_a_1671_);
lean_dec(v_toBind_1670_);
lean_dec(v_inst_1669_);
if (v_isShared_1683_ == 0)
{
v___x_1689_ = v___x_1682_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_fst_1680_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_snd_1675_);
v___x_1689_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1691_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v___x_1689_);
v___x_1691_ = v___x_1678_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
v___x_1693_ = lean_apply_2(v_toPure_1668_, lean_box(0), v___x_1692_);
return v___x_1693_;
}
}
}
else
{
lean_object* v___x_1697_; uint8_t v_isShared_1698_; uint8_t v_isSharedCheck_1718_; 
lean_inc(v_stop_1686_);
lean_inc(v_start_1685_);
lean_inc_ref(v_array_1684_);
v_isSharedCheck_1718_ = !lean_is_exclusive(v_snd_1675_);
if (v_isSharedCheck_1718_ == 0)
{
lean_object* v_unused_1719_; lean_object* v_unused_1720_; lean_object* v_unused_1721_; 
v_unused_1719_ = lean_ctor_get(v_snd_1675_, 2);
lean_dec(v_unused_1719_);
v_unused_1720_ = lean_ctor_get(v_snd_1675_, 1);
lean_dec(v_unused_1720_);
v_unused_1721_ = lean_ctor_get(v_snd_1675_, 0);
lean_dec(v_unused_1721_);
v___x_1697_ = v_snd_1675_;
v_isShared_1698_ = v_isSharedCheck_1718_;
goto v_resetjp_1696_;
}
else
{
lean_dec(v_snd_1675_);
v___x_1697_ = lean_box(0);
v_isShared_1698_ = v_isSharedCheck_1718_;
goto v_resetjp_1696_;
}
v_resetjp_1696_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1703_; 
v___x_1699_ = lean_array_fget(v_array_1684_, v_start_1685_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_add(v_start_1685_, v___x_1700_);
lean_dec(v_start_1685_);
if (v_isShared_1698_ == 0)
{
lean_ctor_set(v___x_1697_, 1, v___x_1701_);
v___x_1703_ = v___x_1697_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_array_1684_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1701_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_stop_1686_);
v___x_1703_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v___x_1705_; 
lean_dec_ref(v_a_1671_);
lean_dec(v_toBind_1670_);
lean_dec(v_inst_1669_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 1, v___x_1703_);
v___x_1705_ = v___x_1682_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_fst_1680_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v___x_1705_);
v___x_1707_ = v___x_1678_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_fst_1676_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
v___x_1709_ = lean_apply_2(v_toPure_1668_, lean_box(0), v___x_1708_);
return v___x_1709_;
}
}
}
else
{
lean_object* v_val_1712_; lean_object* v___f_1713_; lean_object* v___f_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
lean_del_object(v___x_1682_);
lean_del_object(v___x_1678_);
v_val_1712_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_val_1712_);
lean_dec_ref_known(v___x_1699_, 1);
v___f_1713_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_1713_, 0, v_fst_1676_);
lean_closure_set(v___f_1713_, 1, v_fst_1680_);
lean_closure_set(v___f_1713_, 2, v___x_1700_);
lean_closure_set(v___f_1713_, 3, v___x_1703_);
lean_closure_set(v___f_1713_, 4, v_toPure_1668_);
v___f_1714_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed), 7, 2);
lean_closure_set(v___f_1714_, 0, v_val_1712_);
lean_closure_set(v___f_1714_, 1, v_a_1671_);
v___x_1715_ = lean_apply_2(v_inst_1669_, lean_box(0), v___f_1714_);
v___x_1716_ = lean_apply_4(v_toBind_1670_, lean_box(0), lean_box(0), v___x_1715_, v___f_1713_);
return v___x_1716_;
}
}
}
}
}
}
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object* v_heq_1726_, lean_object* v_fst_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_mkArrow(v_heq_1726_, v_fst_1727_, v___y_1730_, v___y_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_heq_1726_ = stack[0].m_obj;
lean_object* v_fst_1727_ = stack[1].m_obj;
lean_object* v___y_1728_ = stack[2].m_obj;
lean_object* v___y_1729_ = stack[3].m_obj;
lean_object* v___y_1730_ = stack[4].m_obj;
lean_object* v___y_1731_ = stack[5].m_obj;
lean_object* v_res_1734_;
v_res_1734_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_heq_1726_, v_fst_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
stack->m_obj
 = v_res_1734_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_heq_1735_, lean_object* v_fst_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_heq_1735_, v_fst_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_heq_1745_, lean_object* v_fst_1746_, lean_object* v_fst_1747_, lean_object* v___x_1748_, lean_object* v___x_1749_, lean_object* v_toPure_1750_, lean_object* v_____x_1751_){
_start:
{
uint8_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1752_ = l_Lean_Expr_isHEq(v_heq_1745_);
v___x_1753_ = lean_box(v___x_1752_);
v___x_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v___x_1755_ = lean_array_push(v_fst_1746_, v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_1757_ = lean_array_push(v_fst_1747_, v___x_1756_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1748_);
lean_ctor_set(v___x_1758_, 1, v___x_1749_);
v___x_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1757_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
v___x_1760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1760_, 0, v___x_1755_);
lean_ctor_set(v___x_1760_, 1, v___x_1759_);
v___x_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1761_, 0, v_____x_1751_);
lean_ctor_set(v___x_1761_, 1, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
v___x_1763_ = lean_apply_2(v_toPure_1750_, lean_box(0), v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object* v_heq_1764_, lean_object* v_fst_1765_, lean_object* v_fst_1766_, lean_object* v___x_1767_, lean_object* v___x_1768_, lean_object* v_toPure_1769_, lean_object* v_____x_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__7(v_heq_1764_, v_fst_1765_, v_fst_1766_, v___x_1767_, v___x_1768_, v_toPure_1769_, v_____x_1770_);
lean_dec_ref(v_heq_1764_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_fst_1772_, lean_object* v_fst_1773_, lean_object* v_fst_1774_, lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v_toPure_1777_, lean_object* v_inst_1778_, lean_object* v_toBind_1779_, lean_object* v_heq_1780_){
_start:
{
lean_object* v___f_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_inc_ref(v_heq_1780_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1781_, 0, v_heq_1780_);
lean_closure_set(v___f_1781_, 1, v_fst_1772_);
v___f_1782_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_1782_, 0, v_heq_1780_);
lean_closure_set(v___f_1782_, 1, v_fst_1773_);
lean_closure_set(v___f_1782_, 2, v_fst_1774_);
lean_closure_set(v___f_1782_, 3, v___x_1775_);
lean_closure_set(v___f_1782_, 4, v___x_1776_);
lean_closure_set(v___f_1782_, 5, v_toPure_1777_);
v___x_1783_ = lean_apply_2(v_inst_1778_, lean_box(0), v___f_1781_);
v___x_1784_ = lean_apply_4(v_toBind_1779_, lean_box(0), lean_box(0), v___x_1783_, v___f_1782_);
return v___x_1784_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v___x_1785_, lean_object* v_a_1786_, lean_object* v_inst_1787_, lean_object* v_toBind_1788_, lean_object* v___f_1789_, lean_object* v_fst_1790_, lean_object* v_fst_1791_, lean_object* v___x_1792_, lean_object* v___x_1793_, lean_object* v___x_1794_, lean_object* v_fst_1795_, lean_object* v_toPure_1796_, uint8_t v_____do__lift_1797_){
_start:
{
if (v_____do__lift_1797_ == 0)
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
lean_dec(v_toPure_1796_);
lean_dec(v_fst_1795_);
lean_dec_ref(v___x_1794_);
lean_dec_ref(v___x_1793_);
lean_dec(v___x_1792_);
lean_dec(v_fst_1791_);
lean_dec(v_fst_1790_);
v___x_1798_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1798_, 0, v___x_1785_);
lean_closure_set(v___x_1798_, 1, v_a_1786_);
v___x_1799_ = lean_apply_2(v_inst_1787_, lean_box(0), v___x_1798_);
v___x_1800_ = lean_apply_4(v_toBind_1788_, lean_box(0), lean_box(0), v___x_1799_, v___f_1789_);
return v___x_1800_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
lean_dec(v___f_1789_);
lean_dec(v_toBind_1788_);
lean_dec(v_inst_1787_);
lean_dec_ref(v_a_1786_);
lean_dec_ref(v___x_1785_);
v___x_1801_ = lean_box(0);
v___x_1802_ = lean_array_push(v_fst_1790_, v___x_1801_);
v___x_1803_ = lean_array_push(v_fst_1791_, v___x_1792_);
v___x_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1793_);
lean_ctor_set(v___x_1804_, 1, v___x_1794_);
v___x_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1803_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1802_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v_fst_1795_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___x_1809_ = lean_apply_2(v_toPure_1796_, lean_box(0), v___x_1808_);
return v___x_1809_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1785_ = stack[0].m_obj;
lean_object* v_a_1786_ = stack[1].m_obj;
lean_object* v_inst_1787_ = stack[2].m_obj;
lean_object* v_toBind_1788_ = stack[3].m_obj;
lean_object* v___f_1789_ = stack[4].m_obj;
lean_object* v_fst_1790_ = stack[5].m_obj;
lean_object* v_fst_1791_ = stack[6].m_obj;
lean_object* v___x_1792_ = stack[7].m_obj;
lean_object* v___x_1793_ = stack[8].m_obj;
lean_object* v___x_1794_ = stack[9].m_obj;
lean_object* v_fst_1795_ = stack[10].m_obj;
lean_object* v_toPure_1796_ = stack[11].m_obj;
uint8_t v_____do__lift_1797_ = stack[12].m_num;
lean_object* v_res_1810_;
v_res_1810_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v___x_1785_, v_a_1786_, v_inst_1787_, v_toBind_1788_, v___f_1789_, v_fst_1790_, v_fst_1791_, v___x_1792_, v___x_1793_, v___x_1794_, v_fst_1795_, v_toPure_1796_, v_____do__lift_1797_);
stack->m_obj
 = v_res_1810_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v___x_1811_, lean_object* v_a_1812_, lean_object* v_inst_1813_, lean_object* v_toBind_1814_, lean_object* v___f_1815_, lean_object* v_fst_1816_, lean_object* v_fst_1817_, lean_object* v___x_1818_, lean_object* v___x_1819_, lean_object* v___x_1820_, lean_object* v_fst_1821_, lean_object* v_toPure_1822_, lean_object* v_____do__lift_1823_){
_start:
{
uint8_t v_____do__lift_12525__boxed_1824_; lean_object* v_res_1825_; 
v_____do__lift_12525__boxed_1824_ = lean_unbox(v_____do__lift_1823_);
v_res_1825_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v___x_1811_, v_a_1812_, v_inst_1813_, v_toBind_1814_, v___f_1815_, v_fst_1816_, v_fst_1817_, v___x_1818_, v___x_1819_, v___x_1820_, v_fst_1821_, v_toPure_1822_, v_____do__lift_12525__boxed_1824_);
return v_res_1825_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_toPure_1826_, uint8_t v_addEqualities_1827_, lean_object* v_inst_1828_, lean_object* v_toBind_1829_, lean_object* v_a_1830_, lean_object* v_x_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_snd_1833_; lean_object* v_snd_1834_; lean_object* v_snd_1835_; lean_object* v_snd_1836_; lean_object* v_fst_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1943_; 
v_snd_1833_ = lean_ctor_get(v___y_1832_, 1);
lean_inc(v_snd_1833_);
v_snd_1834_ = lean_ctor_get(v_snd_1833_, 1);
lean_inc(v_snd_1834_);
v_snd_1835_ = lean_ctor_get(v_snd_1834_, 1);
lean_inc(v_snd_1835_);
v_snd_1836_ = lean_ctor_get(v_snd_1835_, 1);
lean_inc(v_snd_1836_);
v_fst_1837_ = lean_ctor_get(v___y_1832_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___y_1832_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v___y_1832_, 1);
lean_dec(v_unused_1944_);
v___x_1839_ = v___y_1832_;
v_isShared_1840_ = v_isSharedCheck_1943_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_fst_1837_);
lean_dec(v___y_1832_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1943_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v_fst_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1941_; 
v_fst_1841_ = lean_ctor_get(v_snd_1833_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_snd_1833_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v_snd_1833_, 1);
lean_dec(v_unused_1942_);
v___x_1843_ = v_snd_1833_;
v_isShared_1844_ = v_isSharedCheck_1941_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_fst_1841_);
lean_dec(v_snd_1833_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1941_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_fst_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1939_; 
v_fst_1845_ = lean_ctor_get(v_snd_1834_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_snd_1834_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v_snd_1834_, 1);
lean_dec(v_unused_1940_);
v___x_1847_ = v_snd_1834_;
v_isShared_1848_ = v_isSharedCheck_1939_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_fst_1845_);
lean_dec(v_snd_1834_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1939_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_fst_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1937_; 
v_fst_1849_ = lean_ctor_get(v_snd_1835_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_snd_1835_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_snd_1835_, 1);
lean_dec(v_unused_1938_);
v___x_1851_ = v_snd_1835_;
v_isShared_1852_ = v_isSharedCheck_1937_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_fst_1849_);
lean_dec(v_snd_1835_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1937_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_array_1853_; lean_object* v_start_1854_; lean_object* v_stop_1855_; uint8_t v___x_1856_; 
v_array_1853_ = lean_ctor_get(v_snd_1836_, 0);
v_start_1854_ = lean_ctor_get(v_snd_1836_, 1);
v_stop_1855_ = lean_ctor_get(v_snd_1836_, 2);
v___x_1856_ = lean_nat_dec_lt(v_start_1854_, v_stop_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref(v_a_1830_);
lean_dec(v_toBind_1829_);
lean_dec(v_inst_1828_);
if (v_isShared_1852_ == 0)
{
v___x_1858_ = v___x_1851_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_fst_1849_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_snd_1836_);
v___x_1858_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1860_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1858_);
v___x_1860_ = v___x_1847_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_fst_1845_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1862_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1860_);
v___x_1862_ = v___x_1843_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_fst_1841_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1864_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1862_);
v___x_1864_ = v___x_1839_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_fst_1837_);
lean_ctor_set(v_reuseFailAlloc_1867_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
v___x_1866_ = lean_apply_2(v_toPure_1826_, lean_box(0), v___x_1865_);
return v___x_1866_;
}
}
}
}
}
else
{
lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1933_; 
lean_inc(v_stop_1855_);
lean_inc(v_start_1854_);
lean_inc_ref(v_array_1853_);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_snd_1836_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; lean_object* v_unused_1935_; lean_object* v_unused_1936_; 
v_unused_1934_ = lean_ctor_get(v_snd_1836_, 2);
lean_dec(v_unused_1934_);
v_unused_1935_ = lean_ctor_get(v_snd_1836_, 1);
lean_dec(v_unused_1935_);
v_unused_1936_ = lean_ctor_get(v_snd_1836_, 0);
lean_dec(v_unused_1936_);
v___x_1872_ = v_snd_1836_;
v_isShared_1873_ = v_isSharedCheck_1933_;
goto v_resetjp_1871_;
}
else
{
lean_dec(v_snd_1836_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1933_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v_array_1874_; lean_object* v_start_1875_; lean_object* v_stop_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v_array_1874_ = lean_ctor_get(v_fst_1849_, 0);
v_start_1875_ = lean_ctor_get(v_fst_1849_, 1);
v_stop_1876_ = lean_ctor_get(v_fst_1849_, 2);
v___x_1877_ = lean_array_fget(v_array_1853_, v_start_1854_);
v___x_1878_ = lean_unsigned_to_nat(1u);
v___x_1879_ = lean_nat_add(v_start_1854_, v___x_1878_);
lean_dec(v_start_1854_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1879_);
v___x_1881_ = v___x_1872_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_array_1853_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1932_, 2, v_stop_1855_);
v___x_1881_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
uint8_t v___x_1882_; 
v___x_1882_ = lean_nat_dec_lt(v_start_1875_, v_stop_1876_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1884_; 
lean_dec(v___x_1877_);
lean_dec_ref(v_a_1830_);
lean_dec(v_toBind_1829_);
lean_dec(v_inst_1828_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v___x_1881_);
v___x_1884_ = v___x_1851_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_fst_1849_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1881_);
v___x_1884_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1884_);
v___x_1886_ = v___x_1847_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_fst_1845_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
lean_object* v___x_1888_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1886_);
v___x_1888_ = v___x_1843_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_fst_1841_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1886_);
v___x_1888_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1888_);
v___x_1890_ = v___x_1839_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_fst_1837_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
v___x_1892_ = lean_apply_2(v_toPure_1826_, lean_box(0), v___x_1891_);
return v___x_1892_;
}
}
}
}
}
else
{
lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1928_; 
lean_inc(v_stop_1876_);
lean_inc(v_start_1875_);
lean_inc_ref(v_array_1874_);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_fst_1849_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; lean_object* v_unused_1930_; lean_object* v_unused_1931_; 
v_unused_1929_ = lean_ctor_get(v_fst_1849_, 2);
lean_dec(v_unused_1929_);
v_unused_1930_ = lean_ctor_get(v_fst_1849_, 1);
lean_dec(v_unused_1930_);
v_unused_1931_ = lean_ctor_get(v_fst_1849_, 0);
lean_dec(v_unused_1931_);
v___x_1898_ = v_fst_1849_;
v_isShared_1899_ = v_isSharedCheck_1928_;
goto v_resetjp_1897_;
}
else
{
lean_dec(v_fst_1849_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1928_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1900_ = lean_array_fget(v_array_1874_, v_start_1875_);
v___x_1901_ = lean_nat_add(v_start_1875_, v___x_1878_);
lean_dec(v_start_1875_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v___x_1901_);
v___x_1903_ = v___x_1898_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_array_1874_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_stop_1876_);
v___x_1903_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
if (v_addEqualities_1827_ == 0)
{
lean_dec(v___x_1900_);
lean_dec_ref(v_a_1830_);
lean_dec(v_toBind_1829_);
lean_dec(v_inst_1828_);
goto v___jp_1904_;
}
else
{
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___f_1922_; lean_object* v___f_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
lean_del_object(v___x_1851_);
lean_del_object(v___x_1847_);
lean_del_object(v___x_1843_);
lean_del_object(v___x_1839_);
lean_inc_n(v_toBind_1829_, 2);
lean_inc_n(v_inst_1828_, 2);
lean_inc(v_toPure_1826_);
lean_inc_ref(v___x_1881_);
lean_inc_ref(v___x_1903_);
lean_inc(v_fst_1845_);
lean_inc(v_fst_1841_);
lean_inc(v_fst_1837_);
v___f_1922_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8), 9, 8);
lean_closure_set(v___f_1922_, 0, v_fst_1837_);
lean_closure_set(v___f_1922_, 1, v_fst_1841_);
lean_closure_set(v___f_1922_, 2, v_fst_1845_);
lean_closure_set(v___f_1922_, 3, v___x_1903_);
lean_closure_set(v___f_1922_, 4, v___x_1881_);
lean_closure_set(v___f_1922_, 5, v_toPure_1826_);
lean_closure_set(v___f_1922_, 6, v_inst_1828_);
lean_closure_set(v___f_1922_, 7, v_toBind_1829_);
lean_inc_ref(v_a_1830_);
v___f_1923_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 13, 12);
lean_closure_set(v___f_1923_, 0, v___x_1900_);
lean_closure_set(v___f_1923_, 1, v_a_1830_);
lean_closure_set(v___f_1923_, 2, v_inst_1828_);
lean_closure_set(v___f_1923_, 3, v_toBind_1829_);
lean_closure_set(v___f_1923_, 4, v___f_1922_);
lean_closure_set(v___f_1923_, 5, v_fst_1841_);
lean_closure_set(v___f_1923_, 6, v_fst_1845_);
lean_closure_set(v___f_1923_, 7, v___x_1877_);
lean_closure_set(v___f_1923_, 8, v___x_1903_);
lean_closure_set(v___f_1923_, 9, v___x_1881_);
lean_closure_set(v___f_1923_, 10, v_fst_1837_);
lean_closure_set(v___f_1923_, 11, v_toPure_1826_);
v___x_1924_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1924_, 0, v_a_1830_);
v___x_1925_ = lean_apply_2(v_inst_1828_, lean_box(0), v___x_1924_);
v___x_1926_ = lean_apply_4(v_toBind_1829_, lean_box(0), lean_box(0), v___x_1925_, v___f_1923_);
return v___x_1926_;
}
else
{
lean_dec(v___x_1900_);
lean_dec_ref(v_a_1830_);
lean_dec(v_toBind_1829_);
lean_dec(v_inst_1828_);
goto v___jp_1904_;
}
}
v___jp_1904_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1905_ = lean_box(0);
v___x_1906_ = lean_array_push(v_fst_1841_, v___x_1905_);
v___x_1907_ = lean_array_push(v_fst_1845_, v___x_1877_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v___x_1881_);
lean_ctor_set(v___x_1851_, 0, v___x_1903_);
v___x_1909_ = v___x_1851_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1881_);
v___x_1909_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1911_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1909_);
lean_ctor_set(v___x_1847_, 0, v___x_1907_);
v___x_1911_ = v___x_1847_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1913_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 1, v___x_1911_);
lean_ctor_set(v___x_1843_, 0, v___x_1906_);
v___x_1913_ = v___x_1843_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1915_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v___x_1913_);
v___x_1915_ = v___x_1839_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_fst_1837_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
v___x_1917_ = lean_apply_2(v_toPure_1826_, lean_box(0), v___x_1916_);
return v___x_1917_;
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
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_1826_ = stack[0].m_obj;
uint8_t v_addEqualities_1827_ = stack[1].m_num;
lean_object* v_inst_1828_ = stack[2].m_obj;
lean_object* v_toBind_1829_ = stack[3].m_obj;
lean_object* v_a_1830_ = stack[4].m_obj;
lean_object* v___y_1832_ = stack[6].m_obj;
lean_object* v_res_1945_;
v_res_1945_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(v_toPure_1826_, v_addEqualities_1827_, v_inst_1828_, v_toBind_1829_, v_a_1830_, lean_box(0), v___y_1832_);
stack->m_obj
 = v_res_1945_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object* v_toPure_1946_, lean_object* v_addEqualities_1947_, lean_object* v_inst_1948_, lean_object* v_toBind_1949_, lean_object* v_a_1950_, lean_object* v_x_1951_, lean_object* v___y_1952_){
_start:
{
uint8_t v_addEqualities_boxed_1953_; lean_object* v_res_1954_; 
v_addEqualities_boxed_1953_ = lean_unbox(v_addEqualities_1947_);
v_res_1954_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(v_toPure_1946_, v_addEqualities_boxed_1953_, v_inst_1948_, v_toBind_1949_, v_a_1950_, v_x_1951_, v___y_1952_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v_toPure_1955_, lean_object* v_____do__lift_1956_){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_apply_2(v_toPure_1955_, lean_box(0), v_____do__lift_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1958_, lean_object* v_____do__lift_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = lean_apply_2(v_toPure_1958_, lean_box(0), v_____do__lift_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1961_, lean_object* v_fst_1962_, lean_object* v_____do__lift_1963_, lean_object* v_toPure_1964_, lean_object* v_____do__lift_1965_){
_start:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1966_, 0, v_fst_1961_);
lean_ctor_set(v___x_1966_, 1, v_fst_1962_);
v___x_1967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_____do__lift_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v_____do__lift_1963_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_apply_2(v_toPure_1964_, lean_box(0), v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1970_, lean_object* v_fst_1971_, lean_object* v_toPure_1972_, lean_object* v_fst_1973_, lean_object* v_inst_1974_, lean_object* v_toBind_1975_, lean_object* v_____do__lift_1976_){
_start:
{
lean_object* v___f_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___f_1977_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1977_, 0, v_fst_1970_);
lean_closure_set(v___f_1977_, 1, v_fst_1971_);
lean_closure_set(v___f_1977_, 2, v_____do__lift_1976_);
lean_closure_set(v___f_1977_, 3, v_toPure_1972_);
v___x_1978_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1978_, 0, v_fst_1973_);
v___x_1979_ = lean_apply_2(v_inst_1974_, lean_box(0), v___x_1978_);
v___x_1980_ = lean_apply_4(v_toBind_1975_, lean_box(0), lean_box(0), v___x_1979_, v___f_1977_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1981_, lean_object* v_inst_1982_, lean_object* v_toBind_1983_, lean_object* v_motiveArgs_1984_, lean_object* v_____s_1985_){
_start:
{
lean_object* v_snd_1986_; lean_object* v_snd_1987_; lean_object* v_fst_1988_; lean_object* v_fst_1989_; lean_object* v_fst_1990_; lean_object* v___f_1991_; uint8_t v___x_1992_; uint8_t v___x_1993_; uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v_snd_1986_ = lean_ctor_get(v_____s_1985_, 1);
lean_inc(v_snd_1986_);
v_snd_1987_ = lean_ctor_get(v_snd_1986_, 1);
lean_inc(v_snd_1987_);
v_fst_1988_ = lean_ctor_get(v_____s_1985_, 0);
lean_inc_n(v_fst_1988_, 2);
lean_dec_ref(v_____s_1985_);
v_fst_1989_ = lean_ctor_get(v_snd_1986_, 0);
lean_inc(v_fst_1989_);
lean_dec(v_snd_1986_);
v_fst_1990_ = lean_ctor_get(v_snd_1987_, 0);
lean_inc(v_fst_1990_);
lean_dec(v_snd_1987_);
lean_inc(v_toBind_1983_);
lean_inc(v_inst_1982_);
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1991_, 0, v_fst_1989_);
lean_closure_set(v___f_1991_, 1, v_fst_1990_);
lean_closure_set(v___f_1991_, 2, v_toPure_1981_);
lean_closure_set(v___f_1991_, 3, v_fst_1988_);
lean_closure_set(v___f_1991_, 4, v_inst_1982_);
lean_closure_set(v___f_1991_, 5, v_toBind_1983_);
v___x_1992_ = 0;
v___x_1993_ = 1;
v___x_1994_ = 1;
v___x_1995_ = lean_box(v___x_1992_);
v___x_1996_ = lean_box(v___x_1993_);
v___x_1997_ = lean_box(v___x_1992_);
v___x_1998_ = lean_box(v___x_1993_);
v___x_1999_ = lean_box(v___x_1994_);
v___x_2000_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2000_, 0, v_motiveArgs_1984_);
lean_closure_set(v___x_2000_, 1, v_fst_1988_);
lean_closure_set(v___x_2000_, 2, v___x_1995_);
lean_closure_set(v___x_2000_, 3, v___x_1996_);
lean_closure_set(v___x_2000_, 4, v___x_1997_);
lean_closure_set(v___x_2000_, 5, v___x_1998_);
lean_closure_set(v___x_2000_, 6, v___x_1999_);
v___x_2001_ = lean_apply_2(v_inst_1982_, lean_box(0), v___x_2000_);
v___x_2002_ = lean_apply_4(v_toBind_1983_, lean_box(0), lean_box(0), v___x_2001_, v___f_1991_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_2005_, lean_object* v_discrs_x27_2006_, lean_object* v_motiveArgs_2007_, lean_object* v_inst_2008_, lean_object* v___f_2009_, lean_object* v_toBind_2010_, lean_object* v___f_2011_, lean_object* v_motiveBody_x27_2012_){
_start:
{
lean_object* v_discrInfos_2013_; lean_object* v___x_2014_; lean_object* v_addHEqualities_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; size_t v_sz_2024_; size_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_discrInfos_2013_ = lean_ctor_get(v_toMatcherInfo_2005_, 4);
lean_inc_ref(v_discrInfos_2013_);
lean_dec_ref(v_toMatcherInfo_2005_);
v___x_2014_ = lean_unsigned_to_nat(0u);
v_addHEqualities_2015_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_2016_ = lean_array_get_size(v_discrs_x27_2006_);
v___x_2017_ = l_Array_toSubarray___redArg(v_discrs_x27_2006_, v___x_2014_, v___x_2016_);
v___x_2018_ = lean_array_get_size(v_discrInfos_2013_);
v___x_2019_ = l_Array_toSubarray___redArg(v_discrInfos_2013_, v___x_2014_, v___x_2018_);
v___x_2020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2017_);
lean_ctor_set(v___x_2020_, 1, v___x_2019_);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v_addHEqualities_2015_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_addHEqualities_2015_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_motiveBody_x27_2012_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v_sz_2024_ = lean_array_size(v_motiveArgs_2007_);
v___x_2025_ = ((size_t)0ULL);
v___x_2026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_2008_, v_motiveArgs_2007_, v___f_2009_, v_sz_2024_, v___x_2025_, v___x_2023_);
v___x_2027_ = lean_apply_4(v_toBind_2010_, lean_box(0), lean_box(0), v___x_2026_, v___f_2011_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_2028_, lean_object* v_motiveArgs_2029_, lean_object* v_motiveBody_2030_, lean_object* v_toBind_2031_, lean_object* v___f_2032_, lean_object* v_____r_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_apply_2(v_onMotive_2028_, v_motiveArgs_2029_, v_motiveBody_2030_);
v___x_2035_ = lean_apply_4(v_toBind_2031_, lean_box(0), lean_box(0), v___x_2034_, v___f_2032_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_2036_, lean_object* v_____r_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_apply_1(v___f_2036_, v_____r_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_2039_, lean_object* v_inst_2040_, lean_object* v_toBind_2041_, lean_object* v_toMatcherInfo_2042_, lean_object* v_discrs_x27_2043_, lean_object* v_inst_2044_, lean_object* v___f_2045_, lean_object* v_onMotive_2046_, lean_object* v_discrs_2047_, lean_object* v_inst_2048_, lean_object* v_motiveArgs_2049_, lean_object* v_motiveBody_2050_){
_start:
{
lean_object* v___f_2051_; lean_object* v___f_2052_; lean_object* v___f_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; 
lean_inc_ref_n(v_motiveArgs_2049_, 3);
lean_inc_n(v_toBind_2041_, 3);
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2051_, 0, v_toPure_2039_);
lean_closure_set(v___f_2051_, 1, v_inst_2040_);
lean_closure_set(v___f_2051_, 2, v_toBind_2041_);
lean_closure_set(v___f_2051_, 3, v_motiveArgs_2049_);
lean_inc_ref(v_inst_2044_);
v___f_2052_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2052_, 0, v_toMatcherInfo_2042_);
lean_closure_set(v___f_2052_, 1, v_discrs_x27_2043_);
lean_closure_set(v___f_2052_, 2, v_motiveArgs_2049_);
lean_closure_set(v___f_2052_, 3, v_inst_2044_);
lean_closure_set(v___f_2052_, 4, v___f_2045_);
lean_closure_set(v___f_2052_, 5, v_toBind_2041_);
lean_closure_set(v___f_2052_, 6, v___f_2051_);
lean_inc_ref(v___f_2052_);
lean_inc_ref(v_motiveBody_2050_);
lean_inc(v_onMotive_2046_);
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2053_, 0, v_onMotive_2046_);
lean_closure_set(v___f_2053_, 1, v_motiveArgs_2049_);
lean_closure_set(v___f_2053_, 2, v_motiveBody_2050_);
lean_closure_set(v___f_2053_, 3, v_toBind_2041_);
lean_closure_set(v___f_2053_, 4, v___f_2052_);
v___x_2054_ = lean_array_get_size(v_motiveArgs_2049_);
v___x_2055_ = lean_array_get_size(v_discrs_2047_);
v___x_2056_ = lean_nat_dec_eq(v___x_2054_, v___x_2055_);
if (v___x_2056_ == 0)
{
lean_object* v___f_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec_ref(v___f_2052_);
lean_dec_ref(v_motiveBody_2050_);
lean_dec_ref(v_motiveArgs_2049_);
lean_dec(v_onMotive_2046_);
v___f_2057_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2057_, 0, v___f_2053_);
v___x_2058_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2059_ = l_Nat_reprFast(v___x_2055_);
v___x_2060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
v___x_2061_ = l_Lean_MessageData_ofFormat(v___x_2060_);
v___x_2062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2058_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2062_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = l_Lean_throwError___redArg(v_inst_2044_, v_inst_2048_, v___x_2064_);
v___x_2066_ = lean_apply_4(v_toBind_2041_, lean_box(0), lean_box(0), v___x_2065_, v___f_2057_);
return v___x_2066_;
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
lean_dec_ref(v___f_2053_);
lean_dec_ref(v_inst_2048_);
lean_dec_ref(v_inst_2044_);
v___x_2067_ = lean_box(0);
v___x_2068_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2046_, v_motiveArgs_2049_, v_motiveBody_2050_, v_toBind_2041_, v___f_2052_, v___x_2067_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2069_, lean_object* v_inst_2070_, lean_object* v_toBind_2071_, lean_object* v_toMatcherInfo_2072_, lean_object* v_discrs_x27_2073_, lean_object* v_inst_2074_, lean_object* v___f_2075_, lean_object* v_onMotive_2076_, lean_object* v_discrs_2077_, lean_object* v_inst_2078_, lean_object* v_motiveArgs_2079_, lean_object* v_motiveBody_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2069_, v_inst_2070_, v_toBind_2071_, v_toMatcherInfo_2072_, v_discrs_x27_2073_, v_inst_2074_, v___f_2075_, v_onMotive_2076_, v_discrs_2077_, v_inst_2078_, v_motiveArgs_2079_, v_motiveBody_2080_);
lean_dec_ref(v_discrs_2077_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2082_, lean_object* v_numParams_2083_, lean_object* v_numDiscrs_2084_, lean_object* v_altInfos_2085_, lean_object* v_uElimPos_x3f_2086_, lean_object* v_snd_2087_, lean_object* v_overlaps_2088_, lean_object* v_matcherName_2089_, lean_object* v_matcherLevels_2090_, lean_object* v_params_x27_2091_, lean_object* v_fst_2092_, lean_object* v_discrs_x27_2093_, lean_object* v_fst_2094_, lean_object* v_toPure_2095_, lean_object* v_____do__lift_2096_){
_start:
{
lean_object* v_remaining_x27_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_remaining_x27_2097_ = l_Array_append___redArg(v_fst_2082_, v_____do__lift_2096_);
v___x_2098_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2098_, 0, v_numParams_2083_);
lean_ctor_set(v___x_2098_, 1, v_numDiscrs_2084_);
lean_ctor_set(v___x_2098_, 2, v_altInfos_2085_);
lean_ctor_set(v___x_2098_, 3, v_uElimPos_x3f_2086_);
lean_ctor_set(v___x_2098_, 4, v_snd_2087_);
lean_ctor_set(v___x_2098_, 5, v_overlaps_2088_);
v___x_2099_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v_matcherName_2089_);
lean_ctor_set(v___x_2099_, 2, v_matcherLevels_2090_);
lean_ctor_set(v___x_2099_, 3, v_params_x27_2091_);
lean_ctor_set(v___x_2099_, 4, v_fst_2092_);
lean_ctor_set(v___x_2099_, 5, v_discrs_x27_2093_);
lean_ctor_set(v___x_2099_, 6, v_fst_2094_);
lean_ctor_set(v___x_2099_, 7, v_remaining_x27_2097_);
v___x_2100_ = lean_apply_2(v_toPure_2095_, lean_box(0), v___x_2099_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2101_, lean_object* v_numParams_2102_, lean_object* v_numDiscrs_2103_, lean_object* v_altInfos_2104_, lean_object* v_uElimPos_x3f_2105_, lean_object* v_snd_2106_, lean_object* v_overlaps_2107_, lean_object* v_matcherName_2108_, lean_object* v_matcherLevels_2109_, lean_object* v_params_x27_2110_, lean_object* v_fst_2111_, lean_object* v_discrs_x27_2112_, lean_object* v_fst_2113_, lean_object* v_toPure_2114_, lean_object* v_____do__lift_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2101_, v_numParams_2102_, v_numDiscrs_2103_, v_altInfos_2104_, v_uElimPos_x3f_2105_, v_snd_2106_, v_overlaps_2107_, v_matcherName_2108_, v_matcherLevels_2109_, v_params_x27_2110_, v_fst_2111_, v_discrs_x27_2112_, v_fst_2113_, v_toPure_2114_, v_____do__lift_2115_);
lean_dec_ref(v_____do__lift_2115_);
return v_res_2116_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2117_, lean_object* v_numParams_2118_, lean_object* v_numDiscrs_2119_, lean_object* v_altInfos_2120_, lean_object* v_uElimPos_x3f_2121_, lean_object* v_snd_2122_, lean_object* v_overlaps_2123_, lean_object* v_matcherName_2124_, lean_object* v_matcherLevels_2125_, lean_object* v_params_x27_2126_, lean_object* v_fst_2127_, lean_object* v_discrs_x27_2128_, lean_object* v_toPure_2129_, lean_object* v_onRemaining_2130_, lean_object* v_remaining_2131_, lean_object* v_toBind_2132_, lean_object* v_____s_2133_){
_start:
{
lean_object* v_fst_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_fst_2134_ = lean_ctor_get(v_____s_2133_, 0);
lean_inc(v_fst_2134_);
lean_dec_ref(v_____s_2133_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2135_, 0, v_fst_2117_);
lean_closure_set(v___f_2135_, 1, v_numParams_2118_);
lean_closure_set(v___f_2135_, 2, v_numDiscrs_2119_);
lean_closure_set(v___f_2135_, 3, v_altInfos_2120_);
lean_closure_set(v___f_2135_, 4, v_uElimPos_x3f_2121_);
lean_closure_set(v___f_2135_, 5, v_snd_2122_);
lean_closure_set(v___f_2135_, 6, v_overlaps_2123_);
lean_closure_set(v___f_2135_, 7, v_matcherName_2124_);
lean_closure_set(v___f_2135_, 8, v_matcherLevels_2125_);
lean_closure_set(v___f_2135_, 9, v_params_x27_2126_);
lean_closure_set(v___f_2135_, 10, v_fst_2127_);
lean_closure_set(v___f_2135_, 11, v_discrs_x27_2128_);
lean_closure_set(v___f_2135_, 12, v_fst_2134_);
lean_closure_set(v___f_2135_, 13, v_toPure_2129_);
v___x_2136_ = lean_apply_1(v_onRemaining_2130_, v_remaining_2131_);
v___x_2137_ = lean_apply_4(v_toBind_2132_, lean_box(0), lean_box(0), v___x_2136_, v___f_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2117_ = stack[0].m_obj;
lean_object* v_numParams_2118_ = stack[1].m_obj;
lean_object* v_numDiscrs_2119_ = stack[2].m_obj;
lean_object* v_altInfos_2120_ = stack[3].m_obj;
lean_object* v_uElimPos_x3f_2121_ = stack[4].m_obj;
lean_object* v_snd_2122_ = stack[5].m_obj;
lean_object* v_overlaps_2123_ = stack[6].m_obj;
lean_object* v_matcherName_2124_ = stack[7].m_obj;
lean_object* v_matcherLevels_2125_ = stack[8].m_obj;
lean_object* v_params_x27_2126_ = stack[9].m_obj;
lean_object* v_fst_2127_ = stack[10].m_obj;
lean_object* v_discrs_x27_2128_ = stack[11].m_obj;
lean_object* v_toPure_2129_ = stack[12].m_obj;
lean_object* v_onRemaining_2130_ = stack[13].m_obj;
lean_object* v_remaining_2131_ = stack[14].m_obj;
lean_object* v_toBind_2132_ = stack[15].m_obj;
lean_object* v_____s_2133_ = stack[16].m_obj;
lean_object* v_res_2138_;
v_res_2138_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2117_, v_numParams_2118_, v_numDiscrs_2119_, v_altInfos_2120_, v_uElimPos_x3f_2121_, v_snd_2122_, v_overlaps_2123_, v_matcherName_2124_, v_matcherLevels_2125_, v_params_x27_2126_, v_fst_2127_, v_discrs_x27_2128_, v_toPure_2129_, v_onRemaining_2130_, v_remaining_2131_, v_toBind_2132_, v_____s_2133_);
stack->m_obj
 = v_res_2138_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2139_ = _args[0];
lean_object* v_numParams_2140_ = _args[1];
lean_object* v_numDiscrs_2141_ = _args[2];
lean_object* v_altInfos_2142_ = _args[3];
lean_object* v_uElimPos_x3f_2143_ = _args[4];
lean_object* v_snd_2144_ = _args[5];
lean_object* v_overlaps_2145_ = _args[6];
lean_object* v_matcherName_2146_ = _args[7];
lean_object* v_matcherLevels_2147_ = _args[8];
lean_object* v_params_x27_2148_ = _args[9];
lean_object* v_fst_2149_ = _args[10];
lean_object* v_discrs_x27_2150_ = _args[11];
lean_object* v_toPure_2151_ = _args[12];
lean_object* v_onRemaining_2152_ = _args[13];
lean_object* v_remaining_2153_ = _args[14];
lean_object* v_toBind_2154_ = _args[15];
lean_object* v_____s_2155_ = _args[16];
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2139_, v_numParams_2140_, v_numDiscrs_2141_, v_altInfos_2142_, v_uElimPos_x3f_2143_, v_snd_2144_, v_overlaps_2145_, v_matcherName_2146_, v_matcherLevels_2147_, v_params_x27_2148_, v_fst_2149_, v_discrs_x27_2150_, v_toPure_2151_, v_onRemaining_2152_, v_remaining_2153_, v_toBind_2154_, v_____s_2155_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2157_, lean_object* v_next_2158_, lean_object* v_G_2159_, lean_object* v_____do__lift_2160_){
_start:
{
if (lean_obj_tag(v_____do__lift_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
lean_dec(v_G_2159_);
v_a_2161_ = lean_ctor_get(v_____do__lift_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v_____do__lift_2160_, 1);
v___x_2162_ = lean_apply_2(v_toPure_2157_, lean_box(0), v_a_2161_);
return v___x_2162_;
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_toPure_2157_);
v_a_2163_ = lean_ctor_get(v_____do__lift_2160_, 0);
lean_inc(v_a_2163_);
lean_dec_ref_known(v_____do__lift_2160_, 1);
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_nat_add(v_next_2158_, v___x_2164_);
v___x_2166_ = lean_apply_4(v_G_2159_, v___x_2165_, v_a_2163_, lean_box(0), lean_box(0));
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2167_, lean_object* v_next_2168_, lean_object* v_G_2169_, lean_object* v_____do__lift_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2167_, v_next_2168_, v_G_2169_, v_____do__lift_2170_);
lean_dec(v_next_2168_);
return v_res_2171_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2172_, lean_object* v_ys4_2173_, uint8_t v___x_2174_, uint8_t v___x_2175_, lean_object* v_inst_2176_, lean_object* v_alt_x27_2177_){
_start:
{
lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2178_ = l_Array_append___redArg(v_xs_2172_, v_ys4_2173_);
v___x_2179_ = 1;
v___x_2180_ = lean_box(v___x_2174_);
v___x_2181_ = lean_box(v___x_2175_);
v___x_2182_ = lean_box(v___x_2174_);
v___x_2183_ = lean_box(v___x_2175_);
v___x_2184_ = lean_box(v___x_2179_);
v___x_2185_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2185_, 0, v___x_2178_);
lean_closure_set(v___x_2185_, 1, v_alt_x27_2177_);
lean_closure_set(v___x_2185_, 2, v___x_2180_);
lean_closure_set(v___x_2185_, 3, v___x_2181_);
lean_closure_set(v___x_2185_, 4, v___x_2182_);
lean_closure_set(v___x_2185_, 5, v___x_2183_);
lean_closure_set(v___x_2185_, 6, v___x_2184_);
v___x_2186_ = lean_apply_2(v_inst_2176_, lean_box(0), v___x_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2172_ = stack[0].m_obj;
lean_object* v_ys4_2173_ = stack[1].m_obj;
uint8_t v___x_2174_ = stack[2].m_num;
uint8_t v___x_2175_ = stack[3].m_num;
lean_object* v_inst_2176_ = stack[4].m_obj;
lean_object* v_alt_x27_2177_ = stack[5].m_obj;
lean_object* v_res_2187_;
v_res_2187_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2172_, v_ys4_2173_, v___x_2174_, v___x_2175_, v_inst_2176_, v_alt_x27_2177_);
stack->m_obj
 = v_res_2187_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2188_, lean_object* v_ys4_2189_, lean_object* v___x_2190_, lean_object* v___x_2191_, lean_object* v_inst_2192_, lean_object* v_alt_x27_2193_){
_start:
{
uint8_t v___x_13213__boxed_2194_; uint8_t v___x_13214__boxed_2195_; lean_object* v_res_2196_; 
v___x_13213__boxed_2194_ = lean_unbox(v___x_2190_);
v___x_13214__boxed_2195_ = lean_unbox(v___x_2191_);
v_res_2196_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2188_, v_ys4_2189_, v___x_13213__boxed_2194_, v___x_13214__boxed_2195_, v_inst_2192_, v_alt_x27_2193_);
lean_dec_ref(v_ys4_2189_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_xs_2197_, lean_object* v_remaining_x27_2198_, lean_object* v_ys4_2199_, lean_object* v_onAlt_2200_, lean_object* v_next_2201_, lean_object* v_altType_2202_, lean_object* v_toBind_2203_, lean_object* v___f_2204_, lean_object* v_alt_2205_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_inc_ref(v_remaining_x27_2198_);
lean_inc_ref(v_xs_2197_);
v___x_2206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2206_, 0, v_xs_2197_);
lean_ctor_set(v___x_2206_, 1, v_xs_2197_);
lean_ctor_set(v___x_2206_, 2, v_remaining_x27_2198_);
lean_ctor_set(v___x_2206_, 3, v_remaining_x27_2198_);
lean_ctor_set(v___x_2206_, 4, v_ys4_2199_);
v___x_2207_ = lean_apply_4(v_onAlt_2200_, v_next_2201_, v_altType_2202_, v___x_2206_, v_alt_2205_);
v___x_2208_ = lean_apply_4(v_toBind_2203_, lean_box(0), lean_box(0), v___x_2207_, v___f_2204_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2209_, lean_object* v_xs_2210_, lean_object* v_inst_2211_, lean_object* v_toBind_2212_, lean_object* v___f_2213_, lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_names_2216_){
_start:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_inc_ref(v_xs_2210_);
v___x_2217_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2217_, 0, v___x_2209_);
lean_closure_set(v___x_2217_, 1, v_xs_2210_);
v___x_2218_ = lean_apply_2(v_inst_2211_, lean_box(0), v___x_2217_);
v___x_2219_ = lean_apply_4(v_toBind_2212_, lean_box(0), lean_box(0), v___x_2218_, v___f_2213_);
v___x_2220_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2214_, v_inst_2215_, v_xs_2210_, v_names_2216_, v___x_2219_);
return v___x_2220_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2221_, uint8_t v___x_2222_, uint8_t v___x_2223_, lean_object* v_inst_2224_, lean_object* v_remaining_x27_2225_, lean_object* v_onAlt_2226_, lean_object* v_next_2227_, lean_object* v_toBind_2228_, lean_object* v___x_2229_, lean_object* v_inst_2230_, lean_object* v_inst_2231_, lean_object* v___f_2232_, lean_object* v_ys4_2233_, lean_object* v_altType_2234_){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___f_2237_; lean_object* v___f_2238_; lean_object* v___f_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2235_ = lean_box(v___x_2222_);
v___x_2236_ = lean_box(v___x_2223_);
lean_inc(v_inst_2224_);
lean_inc_ref(v_ys4_2233_);
lean_inc_ref_n(v_xs_2221_, 2);
v___f_2237_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2237_, 0, v_xs_2221_);
lean_closure_set(v___f_2237_, 1, v_ys4_2233_);
lean_closure_set(v___f_2237_, 2, v___x_2235_);
lean_closure_set(v___f_2237_, 3, v___x_2236_);
lean_closure_set(v___f_2237_, 4, v_inst_2224_);
lean_inc_n(v_toBind_2228_, 2);
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 9, 8);
lean_closure_set(v___f_2238_, 0, v_xs_2221_);
lean_closure_set(v___f_2238_, 1, v_remaining_x27_2225_);
lean_closure_set(v___f_2238_, 2, v_ys4_2233_);
lean_closure_set(v___f_2238_, 3, v_onAlt_2226_);
lean_closure_set(v___f_2238_, 4, v_next_2227_);
lean_closure_set(v___f_2238_, 5, v_altType_2234_);
lean_closure_set(v___f_2238_, 6, v_toBind_2228_);
lean_closure_set(v___f_2238_, 7, v___f_2237_);
lean_inc_ref(v_inst_2231_);
lean_inc_ref(v_inst_2230_);
lean_inc_ref(v___x_2229_);
v___f_2239_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2239_, 0, v___x_2229_);
lean_closure_set(v___f_2239_, 1, v_xs_2221_);
lean_closure_set(v___f_2239_, 2, v_inst_2224_);
lean_closure_set(v___f_2239_, 3, v_toBind_2228_);
lean_closure_set(v___f_2239_, 4, v___f_2238_);
lean_closure_set(v___f_2239_, 5, v_inst_2230_);
lean_closure_set(v___f_2239_, 6, v_inst_2231_);
v___x_2240_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2230_, v_inst_2231_, v___x_2229_, v___f_2232_, v___x_2222_);
v___x_2241_ = lean_apply_4(v_toBind_2228_, lean_box(0), lean_box(0), v___x_2240_, v___f_2239_);
return v___x_2241_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__26_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_2221_ = stack[0].m_obj;
uint8_t v___x_2222_ = stack[1].m_num;
uint8_t v___x_2223_ = stack[2].m_num;
lean_object* v_inst_2224_ = stack[3].m_obj;
lean_object* v_remaining_x27_2225_ = stack[4].m_obj;
lean_object* v_onAlt_2226_ = stack[5].m_obj;
lean_object* v_next_2227_ = stack[6].m_obj;
lean_object* v_toBind_2228_ = stack[7].m_obj;
lean_object* v___x_2229_ = stack[8].m_obj;
lean_object* v_inst_2230_ = stack[9].m_obj;
lean_object* v_inst_2231_ = stack[10].m_obj;
lean_object* v___f_2232_ = stack[11].m_obj;
lean_object* v_ys4_2233_ = stack[12].m_obj;
lean_object* v_altType_2234_ = stack[13].m_obj;
lean_object* v_res_2242_;
v_res_2242_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2221_, v___x_2222_, v___x_2223_, v_inst_2224_, v_remaining_x27_2225_, v_onAlt_2226_, v_next_2227_, v_toBind_2228_, v___x_2229_, v_inst_2230_, v_inst_2231_, v___f_2232_, v_ys4_2233_, v_altType_2234_);
stack->m_obj
 = v_res_2242_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2243_, lean_object* v___x_2244_, lean_object* v___x_2245_, lean_object* v_inst_2246_, lean_object* v_remaining_x27_2247_, lean_object* v_onAlt_2248_, lean_object* v_next_2249_, lean_object* v_toBind_2250_, lean_object* v___x_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v___f_2254_, lean_object* v_ys4_2255_, lean_object* v_altType_2256_){
_start:
{
uint8_t v___x_13294__boxed_2257_; uint8_t v___x_13295__boxed_2258_; lean_object* v_res_2259_; 
v___x_13294__boxed_2257_ = lean_unbox(v___x_2244_);
v___x_13295__boxed_2258_ = lean_unbox(v___x_2245_);
v_res_2259_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2243_, v___x_13294__boxed_2257_, v___x_13295__boxed_2258_, v_inst_2246_, v_remaining_x27_2247_, v_onAlt_2248_, v_next_2249_, v_toBind_2250_, v___x_2251_, v_inst_2252_, v_inst_2253_, v___f_2254_, v_ys4_2255_, v_altType_2256_);
return v_res_2259_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2260_, uint8_t v___x_2261_, lean_object* v_inst_2262_, lean_object* v_remaining_x27_2263_, lean_object* v_onAlt_2264_, lean_object* v_next_2265_, lean_object* v_toBind_2266_, lean_object* v___x_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v___f_2270_, lean_object* v_fst_2271_, lean_object* v_xs_2272_, lean_object* v_altType_2273_){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2274_ = lean_box(v___x_2260_);
v___x_2275_ = lean_box(v___x_2261_);
lean_inc_ref(v_inst_2269_);
lean_inc_ref(v_inst_2268_);
v___f_2276_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 14, 12);
lean_closure_set(v___f_2276_, 0, v_xs_2272_);
lean_closure_set(v___f_2276_, 1, v___x_2274_);
lean_closure_set(v___f_2276_, 2, v___x_2275_);
lean_closure_set(v___f_2276_, 3, v_inst_2262_);
lean_closure_set(v___f_2276_, 4, v_remaining_x27_2263_);
lean_closure_set(v___f_2276_, 5, v_onAlt_2264_);
lean_closure_set(v___f_2276_, 6, v_next_2265_);
lean_closure_set(v___f_2276_, 7, v_toBind_2266_);
lean_closure_set(v___f_2276_, 8, v___x_2267_);
lean_closure_set(v___f_2276_, 9, v_inst_2268_);
lean_closure_set(v___f_2276_, 10, v_inst_2269_);
lean_closure_set(v___f_2276_, 11, v___f_2270_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v_fst_2271_);
v___x_2278_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2268_, v_inst_2269_, v_altType_2273_, v___x_2277_, v___f_2276_, v___x_2260_, v___x_2260_);
return v___x_2278_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__27_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_2260_ = stack[0].m_num;
uint8_t v___x_2261_ = stack[1].m_num;
lean_object* v_inst_2262_ = stack[2].m_obj;
lean_object* v_remaining_x27_2263_ = stack[3].m_obj;
lean_object* v_onAlt_2264_ = stack[4].m_obj;
lean_object* v_next_2265_ = stack[5].m_obj;
lean_object* v_toBind_2266_ = stack[6].m_obj;
lean_object* v___x_2267_ = stack[7].m_obj;
lean_object* v_inst_2268_ = stack[8].m_obj;
lean_object* v_inst_2269_ = stack[9].m_obj;
lean_object* v___f_2270_ = stack[10].m_obj;
lean_object* v_fst_2271_ = stack[11].m_obj;
lean_object* v_xs_2272_ = stack[12].m_obj;
lean_object* v_altType_2273_ = stack[13].m_obj;
lean_object* v_res_2279_;
v_res_2279_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_2260_, v___x_2261_, v_inst_2262_, v_remaining_x27_2263_, v_onAlt_2264_, v_next_2265_, v_toBind_2266_, v___x_2267_, v_inst_2268_, v_inst_2269_, v___f_2270_, v_fst_2271_, v_xs_2272_, v_altType_2273_);
stack->m_obj
 = v_res_2279_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2280_, lean_object* v___x_2281_, lean_object* v_inst_2282_, lean_object* v_remaining_x27_2283_, lean_object* v_onAlt_2284_, lean_object* v_next_2285_, lean_object* v_toBind_2286_, lean_object* v___x_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v___f_2290_, lean_object* v_fst_2291_, lean_object* v_xs_2292_, lean_object* v_altType_2293_){
_start:
{
uint8_t v___x_13350__boxed_2294_; uint8_t v___x_13351__boxed_2295_; lean_object* v_res_2296_; 
v___x_13350__boxed_2294_ = lean_unbox(v___x_2280_);
v___x_13351__boxed_2295_ = lean_unbox(v___x_2281_);
v_res_2296_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_13350__boxed_2294_, v___x_13351__boxed_2295_, v_inst_2282_, v_remaining_x27_2283_, v_onAlt_2284_, v_next_2285_, v_toBind_2286_, v___x_2287_, v_inst_2288_, v_inst_2289_, v___f_2290_, v_fst_2291_, v_xs_2292_, v_altType_2293_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_fst_2297_, lean_object* v___x_2298_, lean_object* v___x_2299_, lean_object* v___x_2300_, lean_object* v_toPure_2301_, lean_object* v_alt_x27_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2303_ = lean_array_push(v_fst_2297_, v_alt_x27_2302_);
v___x_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2298_);
lean_ctor_set(v___x_2304_, 1, v___x_2299_);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2300_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2303_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
v___x_2308_ = lean_apply_2(v_toPure_2301_, lean_box(0), v___x_2307_);
return v___x_2308_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2309_, lean_object* v_toPure_2310_, lean_object* v_toBind_2311_, lean_object* v___f_2312_, uint8_t v___x_2313_, uint8_t v___x_2314_, lean_object* v_inst_2315_, lean_object* v_remaining_x27_2316_, lean_object* v_onAlt_2317_, lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v___f_2320_, lean_object* v_fst_2321_, lean_object* v_next_2322_, lean_object* v_acc_2323_, lean_object* v_h_2324_, lean_object* v_G_2325_){
_start:
{
uint8_t v___x_2326_; 
v___x_2326_ = lean_nat_dec_lt(v_next_2322_, v___x_2309_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_dec(v_G_2325_);
lean_dec(v_next_2322_);
lean_dec(v_fst_2321_);
lean_dec(v___f_2320_);
lean_dec_ref(v_inst_2319_);
lean_dec_ref(v_inst_2318_);
lean_dec(v_onAlt_2317_);
lean_dec_ref(v_remaining_x27_2316_);
lean_dec(v_inst_2315_);
lean_dec(v___f_2312_);
lean_dec(v_toBind_2311_);
v___x_2327_ = lean_apply_2(v_toPure_2310_, lean_box(0), v_acc_2323_);
return v___x_2327_;
}
else
{
lean_object* v_snd_2328_; lean_object* v_snd_2329_; lean_object* v_snd_2330_; lean_object* v_fst_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2441_; 
v_snd_2328_ = lean_ctor_get(v_acc_2323_, 1);
lean_inc(v_snd_2328_);
v_snd_2329_ = lean_ctor_get(v_snd_2328_, 1);
lean_inc(v_snd_2329_);
v_snd_2330_ = lean_ctor_get(v_snd_2329_, 1);
lean_inc(v_snd_2330_);
v_fst_2331_ = lean_ctor_get(v_acc_2323_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v_acc_2323_);
if (v_isSharedCheck_2441_ == 0)
{
lean_object* v_unused_2442_; 
v_unused_2442_ = lean_ctor_get(v_acc_2323_, 1);
lean_dec(v_unused_2442_);
v___x_2333_ = v_acc_2323_;
v_isShared_2334_ = v_isSharedCheck_2441_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_fst_2331_);
lean_dec(v_acc_2323_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2441_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_fst_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2439_; 
v_fst_2335_ = lean_ctor_get(v_snd_2328_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v_snd_2328_);
if (v_isSharedCheck_2439_ == 0)
{
lean_object* v_unused_2440_; 
v_unused_2440_ = lean_ctor_get(v_snd_2328_, 1);
lean_dec(v_unused_2440_);
v___x_2337_ = v_snd_2328_;
v_isShared_2338_ = v_isSharedCheck_2439_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_fst_2335_);
lean_dec(v_snd_2328_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2439_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_fst_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2437_; 
v_fst_2339_ = lean_ctor_get(v_snd_2329_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_snd_2329_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; 
v_unused_2438_ = lean_ctor_get(v_snd_2329_, 1);
lean_dec(v_unused_2438_);
v___x_2341_ = v_snd_2329_;
v_isShared_2342_ = v_isSharedCheck_2437_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_fst_2339_);
lean_dec(v_snd_2329_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2437_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v_array_2343_; lean_object* v_start_2344_; lean_object* v_stop_2345_; lean_object* v___f_2346_; lean_object* v___y_2348_; uint8_t v___x_2351_; 
v_array_2343_ = lean_ctor_get(v_snd_2330_, 0);
v_start_2344_ = lean_ctor_get(v_snd_2330_, 1);
v_stop_2345_ = lean_ctor_get(v_snd_2330_, 2);
lean_inc(v_next_2322_);
lean_inc(v_toPure_2310_);
v___f_2346_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2346_, 0, v_toPure_2310_);
lean_closure_set(v___f_2346_, 1, v_next_2322_);
lean_closure_set(v___f_2346_, 2, v_G_2325_);
v___x_2351_ = lean_nat_dec_lt(v_start_2344_, v_stop_2345_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v_next_2322_);
lean_dec(v_fst_2321_);
lean_dec(v___f_2320_);
lean_dec_ref(v_inst_2319_);
lean_dec_ref(v_inst_2318_);
lean_dec(v_onAlt_2317_);
lean_dec_ref(v_remaining_x27_2316_);
lean_dec(v_inst_2315_);
if (v_isShared_2342_ == 0)
{
v___x_2353_ = v___x_2341_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_fst_2339_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_snd_2330_);
v___x_2353_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2353_);
v___x_2355_ = v___x_2337_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_fst_2335_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2355_);
v___x_2357_ = v___x_2333_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_fst_2331_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
v___x_2359_ = lean_apply_2(v_toPure_2310_, lean_box(0), v___x_2358_);
v___y_2348_ = v___x_2359_;
goto v___jp_2347_;
}
}
}
}
else
{
lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2433_; 
lean_inc(v_stop_2345_);
lean_inc(v_start_2344_);
lean_inc_ref(v_array_2343_);
v_isSharedCheck_2433_ = !lean_is_exclusive(v_snd_2330_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; lean_object* v_unused_2436_; 
v_unused_2434_ = lean_ctor_get(v_snd_2330_, 2);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v_snd_2330_, 1);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_snd_2330_, 0);
lean_dec(v_unused_2436_);
v___x_2364_ = v_snd_2330_;
v_isShared_2365_ = v_isSharedCheck_2433_;
goto v_resetjp_2363_;
}
else
{
lean_dec(v_snd_2330_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2433_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_array_2366_; lean_object* v_start_2367_; lean_object* v_stop_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2373_; 
v_array_2366_ = lean_ctor_get(v_fst_2339_, 0);
v_start_2367_ = lean_ctor_get(v_fst_2339_, 1);
v_stop_2368_ = lean_ctor_get(v_fst_2339_, 2);
v___x_2369_ = lean_array_fget(v_array_2343_, v_start_2344_);
v___x_2370_ = lean_unsigned_to_nat(1u);
v___x_2371_ = lean_nat_add(v_start_2344_, v___x_2370_);
lean_dec(v_start_2344_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v___x_2371_);
v___x_2373_ = v___x_2364_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_array_2343_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_stop_2345_);
v___x_2373_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
uint8_t v___x_2374_; 
v___x_2374_ = lean_nat_dec_lt(v_start_2367_, v_stop_2368_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2376_; 
lean_dec(v___x_2369_);
lean_dec(v_next_2322_);
lean_dec(v_fst_2321_);
lean_dec(v___f_2320_);
lean_dec_ref(v_inst_2319_);
lean_dec_ref(v_inst_2318_);
lean_dec(v_onAlt_2317_);
lean_dec_ref(v_remaining_x27_2316_);
lean_dec(v_inst_2315_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2373_);
v___x_2376_ = v___x_2341_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_fst_2339_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v___x_2373_);
v___x_2376_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2378_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2376_);
v___x_2378_ = v___x_2337_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_fst_2335_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2376_);
v___x_2378_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
lean_object* v___x_2380_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2378_);
v___x_2380_ = v___x_2333_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_fst_2331_);
lean_ctor_set(v_reuseFailAlloc_2383_, 1, v___x_2378_);
v___x_2380_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
v___x_2382_ = lean_apply_2(v_toPure_2310_, lean_box(0), v___x_2381_);
v___y_2348_ = v___x_2382_;
goto v___jp_2347_;
}
}
}
}
else
{
lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2428_; 
lean_inc(v_stop_2368_);
lean_inc(v_start_2367_);
lean_inc_ref(v_array_2366_);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_fst_2339_);
if (v_isSharedCheck_2428_ == 0)
{
lean_object* v_unused_2429_; lean_object* v_unused_2430_; lean_object* v_unused_2431_; 
v_unused_2429_ = lean_ctor_get(v_fst_2339_, 2);
lean_dec(v_unused_2429_);
v_unused_2430_ = lean_ctor_get(v_fst_2339_, 1);
lean_dec(v_unused_2430_);
v_unused_2431_ = lean_ctor_get(v_fst_2339_, 0);
lean_dec(v_unused_2431_);
v___x_2387_ = v_fst_2339_;
v_isShared_2388_ = v_isSharedCheck_2428_;
goto v_resetjp_2386_;
}
else
{
lean_dec(v_fst_2339_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2428_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v_array_2389_; lean_object* v_start_2390_; lean_object* v_stop_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2395_; 
v_array_2389_ = lean_ctor_get(v_fst_2335_, 0);
v_start_2390_ = lean_ctor_get(v_fst_2335_, 1);
v_stop_2391_ = lean_ctor_get(v_fst_2335_, 2);
v___x_2392_ = lean_array_fget(v_array_2366_, v_start_2367_);
v___x_2393_ = lean_nat_add(v_start_2367_, v___x_2370_);
lean_dec(v_start_2367_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___x_2393_);
v___x_2395_ = v___x_2387_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_array_2366_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_stop_2368_);
v___x_2395_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
uint8_t v___x_2396_; 
v___x_2396_ = lean_nat_dec_lt(v_start_2390_, v_stop_2391_);
if (v___x_2396_ == 0)
{
lean_object* v___x_2398_; 
lean_dec(v___x_2392_);
lean_dec(v___x_2369_);
lean_dec(v_next_2322_);
lean_dec(v_fst_2321_);
lean_dec(v___f_2320_);
lean_dec_ref(v_inst_2319_);
lean_dec_ref(v_inst_2318_);
lean_dec(v_onAlt_2317_);
lean_dec_ref(v_remaining_x27_2316_);
lean_dec(v_inst_2315_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2373_);
lean_ctor_set(v___x_2341_, 0, v___x_2395_);
v___x_2398_ = v___x_2341_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___x_2373_);
v___x_2398_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2400_; 
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2398_);
v___x_2400_ = v___x_2337_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_fst_2335_);
lean_ctor_set(v_reuseFailAlloc_2406_, 1, v___x_2398_);
v___x_2400_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2402_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_2400_);
v___x_2402_ = v___x_2333_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_fst_2331_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2402_);
v___x_2404_ = lean_apply_2(v_toPure_2310_, lean_box(0), v___x_2403_);
v___y_2348_ = v___x_2404_;
goto v___jp_2347_;
}
}
}
}
else
{
lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2423_; 
lean_inc(v_stop_2391_);
lean_inc(v_start_2390_);
lean_inc_ref(v_array_2389_);
lean_del_object(v___x_2341_);
lean_del_object(v___x_2337_);
lean_del_object(v___x_2333_);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_fst_2335_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; lean_object* v_unused_2425_; lean_object* v_unused_2426_; 
v_unused_2424_ = lean_ctor_get(v_fst_2335_, 2);
lean_dec(v_unused_2424_);
v_unused_2425_ = lean_ctor_get(v_fst_2335_, 1);
lean_dec(v_unused_2425_);
v_unused_2426_ = lean_ctor_get(v_fst_2335_, 0);
lean_dec(v_unused_2426_);
v___x_2409_ = v_fst_2335_;
v_isShared_2410_ = v_isSharedCheck_2423_;
goto v_resetjp_2408_;
}
else
{
lean_dec(v_fst_2335_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2423_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___f_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
v___x_2411_ = lean_array_fget_borrowed(v_array_2389_, v_start_2390_);
v___x_2412_ = lean_box(v___x_2313_);
v___x_2413_ = lean_box(v___x_2314_);
lean_inc_ref(v_inst_2319_);
lean_inc_ref(v_inst_2318_);
lean_inc(v___x_2411_);
lean_inc(v_toBind_2311_);
v___f_2414_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 14, 12);
lean_closure_set(v___f_2414_, 0, v___x_2412_);
lean_closure_set(v___f_2414_, 1, v___x_2413_);
lean_closure_set(v___f_2414_, 2, v_inst_2315_);
lean_closure_set(v___f_2414_, 3, v_remaining_x27_2316_);
lean_closure_set(v___f_2414_, 4, v_onAlt_2317_);
lean_closure_set(v___f_2414_, 5, v_next_2322_);
lean_closure_set(v___f_2414_, 6, v_toBind_2311_);
lean_closure_set(v___f_2414_, 7, v___x_2411_);
lean_closure_set(v___f_2414_, 8, v_inst_2318_);
lean_closure_set(v___f_2414_, 9, v_inst_2319_);
lean_closure_set(v___f_2414_, 10, v___f_2320_);
lean_closure_set(v___f_2414_, 11, v_fst_2321_);
v___x_2415_ = lean_nat_add(v_start_2390_, v___x_2370_);
lean_dec(v_start_2390_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 1, v___x_2415_);
v___x_2417_ = v___x_2409_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_array_2389_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2422_, 2, v_stop_2391_);
v___x_2417_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___f_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___f_2418_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2418_, 0, v_fst_2331_);
lean_closure_set(v___f_2418_, 1, v___x_2395_);
lean_closure_set(v___f_2418_, 2, v___x_2373_);
lean_closure_set(v___f_2418_, 3, v___x_2417_);
lean_closure_set(v___f_2418_, 4, v_toPure_2310_);
v___x_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2392_);
v___x_2420_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2318_, v_inst_2319_, v___x_2369_, v___x_2419_, v___f_2414_, v___x_2313_, v___x_2313_);
lean_inc(v_toBind_2311_);
v___x_2421_ = lean_apply_4(v_toBind_2311_, lean_box(0), lean_box(0), v___x_2420_, v___f_2418_);
v___y_2348_ = v___x_2421_;
goto v___jp_2347_;
}
}
}
}
}
}
}
}
}
v___jp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_inc(v_toBind_2311_);
v___x_2349_ = lean_apply_4(v_toBind_2311_, lean_box(0), lean_box(0), v___y_2348_, v___f_2312_);
v___x_2350_ = lean_apply_4(v_toBind_2311_, lean_box(0), lean_box(0), v___x_2349_, v___f_2346_);
return v___x_2350_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__29_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2309_ = stack[0].m_obj;
lean_object* v_toPure_2310_ = stack[1].m_obj;
lean_object* v_toBind_2311_ = stack[2].m_obj;
lean_object* v___f_2312_ = stack[3].m_obj;
uint8_t v___x_2313_ = stack[4].m_num;
uint8_t v___x_2314_ = stack[5].m_num;
lean_object* v_inst_2315_ = stack[6].m_obj;
lean_object* v_remaining_x27_2316_ = stack[7].m_obj;
lean_object* v_onAlt_2317_ = stack[8].m_obj;
lean_object* v_inst_2318_ = stack[9].m_obj;
lean_object* v_inst_2319_ = stack[10].m_obj;
lean_object* v___f_2320_ = stack[11].m_obj;
lean_object* v_fst_2321_ = stack[12].m_obj;
lean_object* v_next_2322_ = stack[13].m_obj;
lean_object* v_acc_2323_ = stack[14].m_obj;
lean_object* v_G_2325_ = stack[16].m_obj;
lean_object* v_res_2443_;
v_res_2443_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2309_, v_toPure_2310_, v_toBind_2311_, v___f_2312_, v___x_2313_, v___x_2314_, v_inst_2315_, v_remaining_x27_2316_, v_onAlt_2317_, v_inst_2318_, v_inst_2319_, v___f_2320_, v_fst_2321_, v_next_2322_, v_acc_2323_, lean_box(0), v_G_2325_);
stack->m_obj
 = v_res_2443_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_2444_ = _args[0];
lean_object* v_toPure_2445_ = _args[1];
lean_object* v_toBind_2446_ = _args[2];
lean_object* v___f_2447_ = _args[3];
lean_object* v___x_2448_ = _args[4];
lean_object* v___x_2449_ = _args[5];
lean_object* v_inst_2450_ = _args[6];
lean_object* v_remaining_x27_2451_ = _args[7];
lean_object* v_onAlt_2452_ = _args[8];
lean_object* v_inst_2453_ = _args[9];
lean_object* v_inst_2454_ = _args[10];
lean_object* v___f_2455_ = _args[11];
lean_object* v_fst_2456_ = _args[12];
lean_object* v_next_2457_ = _args[13];
lean_object* v_acc_2458_ = _args[14];
lean_object* v_h_2459_ = _args[15];
lean_object* v_G_2460_ = _args[16];
_start:
{
uint8_t v___x_13429__boxed_2461_; uint8_t v___x_13430__boxed_2462_; lean_object* v_res_2463_; 
v___x_13429__boxed_2461_ = lean_unbox(v___x_2448_);
v___x_13430__boxed_2462_ = lean_unbox(v___x_2449_);
v_res_2463_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2444_, v_toPure_2445_, v_toBind_2446_, v___f_2447_, v___x_13429__boxed_2461_, v___x_13430__boxed_2462_, v_inst_2450_, v_remaining_x27_2451_, v_onAlt_2452_, v_inst_2453_, v_inst_2454_, v___f_2455_, v_fst_2456_, v_next_2457_, v_acc_2458_, v_h_2459_, v_G_2460_);
lean_dec(v___x_2444_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_matcherApp_2464_, lean_object* v_alts_2465_, lean_object* v___x_2466_, lean_object* v___x_2467_, lean_object* v_remaining_x27_2468_, lean_object* v___f_2469_, lean_object* v_toBind_2470_, lean_object* v___f_2471_, lean_object* v_altTypes_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2473_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2464_);
v___x_2474_ = lean_array_get_size(v___x_2473_);
v___x_2475_ = lean_array_get_size(v_altTypes_2472_);
lean_inc_n(v___x_2466_, 3);
v___x_2476_ = l_Array_toSubarray___redArg(v_alts_2465_, v___x_2466_, v___x_2467_);
v___x_2477_ = l_Array_toSubarray___redArg(v___x_2473_, v___x_2466_, v___x_2474_);
v___x_2478_ = l_Array_toSubarray___redArg(v_altTypes_2472_, v___x_2466_, v___x_2475_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2476_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v_remaining_x27_2468_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2469_, v___x_2466_, v___x_2481_, lean_box(0));
v___x_2483_ = lean_apply_4(v_toBind_2470_, lean_box(0), lean_box(0), v___x_2482_, v___f_2471_);
return v___x_2483_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2484_, lean_object* v_toPure_2485_, lean_object* v_toBind_2486_, lean_object* v___f_2487_, uint8_t v___x_2488_, uint8_t v___x_2489_, lean_object* v_inst_2490_, lean_object* v_remaining_x27_2491_, lean_object* v_onAlt_2492_, lean_object* v_inst_2493_, lean_object* v_inst_2494_, lean_object* v___f_2495_, lean_object* v_fst_2496_, lean_object* v_matcherApp_2497_, lean_object* v___x_2498_, lean_object* v___f_2499_, lean_object* v_aux_2500_, lean_object* v_____r_2501_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___f_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2502_ = lean_array_get_size(v_alts_2484_);
v___x_2503_ = lean_box(v___x_2488_);
v___x_2504_ = lean_box(v___x_2489_);
lean_inc_ref(v_remaining_x27_2491_);
lean_inc(v_inst_2490_);
lean_inc_n(v_toBind_2486_, 2);
v___f_2505_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 17, 13);
lean_closure_set(v___f_2505_, 0, v___x_2502_);
lean_closure_set(v___f_2505_, 1, v_toPure_2485_);
lean_closure_set(v___f_2505_, 2, v_toBind_2486_);
lean_closure_set(v___f_2505_, 3, v___f_2487_);
lean_closure_set(v___f_2505_, 4, v___x_2503_);
lean_closure_set(v___f_2505_, 5, v___x_2504_);
lean_closure_set(v___f_2505_, 6, v_inst_2490_);
lean_closure_set(v___f_2505_, 7, v_remaining_x27_2491_);
lean_closure_set(v___f_2505_, 8, v_onAlt_2492_);
lean_closure_set(v___f_2505_, 9, v_inst_2493_);
lean_closure_set(v___f_2505_, 10, v_inst_2494_);
lean_closure_set(v___f_2505_, 11, v___f_2495_);
lean_closure_set(v___f_2505_, 12, v_fst_2496_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2506_, 0, v_matcherApp_2497_);
lean_closure_set(v___f_2506_, 1, v_alts_2484_);
lean_closure_set(v___f_2506_, 2, v___x_2498_);
lean_closure_set(v___f_2506_, 3, v___x_2502_);
lean_closure_set(v___f_2506_, 4, v_remaining_x27_2491_);
lean_closure_set(v___f_2506_, 5, v___f_2505_);
lean_closure_set(v___f_2506_, 6, v_toBind_2486_);
lean_closure_set(v___f_2506_, 7, v___f_2499_);
v___x_2507_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2507_, 0, v___x_2502_);
lean_closure_set(v___x_2507_, 1, v_aux_2500_);
v___x_2508_ = lean_apply_2(v_inst_2490_, lean_box(0), v___x_2507_);
v___x_2509_ = lean_apply_4(v_toBind_2486_, lean_box(0), lean_box(0), v___x_2508_, v___f_2506_);
return v___x_2509_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_2484_ = stack[0].m_obj;
lean_object* v_toPure_2485_ = stack[1].m_obj;
lean_object* v_toBind_2486_ = stack[2].m_obj;
lean_object* v___f_2487_ = stack[3].m_obj;
uint8_t v___x_2488_ = stack[4].m_num;
uint8_t v___x_2489_ = stack[5].m_num;
lean_object* v_inst_2490_ = stack[6].m_obj;
lean_object* v_remaining_x27_2491_ = stack[7].m_obj;
lean_object* v_onAlt_2492_ = stack[8].m_obj;
lean_object* v_inst_2493_ = stack[9].m_obj;
lean_object* v_inst_2494_ = stack[10].m_obj;
lean_object* v___f_2495_ = stack[11].m_obj;
lean_object* v_fst_2496_ = stack[12].m_obj;
lean_object* v_matcherApp_2497_ = stack[13].m_obj;
lean_object* v___x_2498_ = stack[14].m_obj;
lean_object* v___f_2499_ = stack[15].m_obj;
lean_object* v_aux_2500_ = stack[16].m_obj;
lean_object* v_____r_2501_ = stack[17].m_obj;
lean_object* v_res_2510_;
v_res_2510_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2484_, v_toPure_2485_, v_toBind_2486_, v___f_2487_, v___x_2488_, v___x_2489_, v_inst_2490_, v_remaining_x27_2491_, v_onAlt_2492_, v_inst_2493_, v_inst_2494_, v___f_2495_, v_fst_2496_, v_matcherApp_2497_, v___x_2498_, v___f_2499_, v_aux_2500_, v_____r_2501_);
stack->m_obj
 = v_res_2510_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_alts_2511_ = _args[0];
lean_object* v_toPure_2512_ = _args[1];
lean_object* v_toBind_2513_ = _args[2];
lean_object* v___f_2514_ = _args[3];
lean_object* v___x_2515_ = _args[4];
lean_object* v___x_2516_ = _args[5];
lean_object* v_inst_2517_ = _args[6];
lean_object* v_remaining_x27_2518_ = _args[7];
lean_object* v_onAlt_2519_ = _args[8];
lean_object* v_inst_2520_ = _args[9];
lean_object* v_inst_2521_ = _args[10];
lean_object* v___f_2522_ = _args[11];
lean_object* v_fst_2523_ = _args[12];
lean_object* v_matcherApp_2524_ = _args[13];
lean_object* v___x_2525_ = _args[14];
lean_object* v___f_2526_ = _args[15];
lean_object* v_aux_2527_ = _args[16];
lean_object* v_____r_2528_ = _args[17];
_start:
{
uint8_t v___x_13819__boxed_2529_; uint8_t v___x_13820__boxed_2530_; lean_object* v_res_2531_; 
v___x_13819__boxed_2529_ = lean_unbox(v___x_2515_);
v___x_13820__boxed_2530_ = lean_unbox(v___x_2516_);
v_res_2531_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2511_, v_toPure_2512_, v_toBind_2513_, v___f_2514_, v___x_13819__boxed_2529_, v___x_13820__boxed_2530_, v_inst_2517_, v_remaining_x27_2518_, v_onAlt_2519_, v_inst_2520_, v_inst_2521_, v___f_2522_, v_fst_2523_, v_matcherApp_2524_, v___x_2525_, v___f_2526_, v_aux_2527_, v_____r_2528_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v___x_2532_, lean_object* v_e_2533_){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = l_Lean_indentD(v_e_2533_);
v___x_2535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2535_, 0, v___x_2532_);
lean_ctor_set(v___x_2535_, 1, v___x_2534_);
return v___x_2535_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v___x_2536_, lean_object* v___f_2537_, lean_object* v_runInBase_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_apply_2(v_runInBase_2538_, lean_box(0), v___x_2536_);
v___x_2545_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2544_, v___f_2537_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
return v___x_2545_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__33_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2536_ = stack[0].m_obj;
lean_object* v___f_2537_ = stack[1].m_obj;
lean_object* v_runInBase_2538_ = stack[2].m_obj;
lean_object* v___y_2539_ = stack[3].m_obj;
lean_object* v___y_2540_ = stack[4].m_obj;
lean_object* v___y_2541_ = stack[5].m_obj;
lean_object* v___y_2542_ = stack[6].m_obj;
lean_object* v_res_2546_;
v_res_2546_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2536_, v___f_2537_, v_runInBase_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_);
stack->m_obj
 = v_res_2546_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object* v___x_2547_, lean_object* v___f_2548_, lean_object* v_runInBase_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2547_, v___f_2548_, v_runInBase_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
lean_dec(v___y_2551_);
lean_dec_ref(v___y_2550_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v_toPure_2556_, lean_object* v_next_2557_, lean_object* v_G_2558_, lean_object* v_____do__lift_2559_){
_start:
{
if (lean_obj_tag(v_____do__lift_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2561_; 
lean_dec(v_G_2558_);
v_a_2560_ = lean_ctor_get(v_____do__lift_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v_____do__lift_2559_, 1);
v___x_2561_ = lean_apply_2(v_toPure_2556_, lean_box(0), v_a_2560_);
return v___x_2561_;
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_toPure_2556_);
v_a_2562_ = lean_ctor_get(v_____do__lift_2559_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v_____do__lift_2559_, 1);
v___x_2563_ = lean_unsigned_to_nat(1u);
v___x_2564_ = lean_nat_add(v_next_2557_, v___x_2563_);
v___x_2565_ = lean_apply_4(v_G_2558_, v___x_2564_, v_a_2562_, lean_box(0), lean_box(0));
return v___x_2565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v_toPure_2566_, lean_object* v_next_2567_, lean_object* v_G_2568_, lean_object* v_____do__lift_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v_toPure_2566_, v_next_2567_, v_G_2568_, v_____do__lift_2569_);
lean_dec(v_next_2567_);
return v_res_2570_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5(void){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2579_ = lean_box(0);
v___x_2580_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4));
v___x_2581_ = l_Lean_mkConst(v___x_2580_, v___x_2579_);
return v___x_2581_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2582_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5);
v___x_2583_ = lean_unsigned_to_nat(2u);
v___x_2584_ = lean_mk_empty_array_with_capacity(v___x_2583_);
v___x_2585_ = lean_array_push(v___x_2584_, v___x_2582_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v___x_2586_, lean_object* v_toPure_2587_, lean_object* v_inst_2588_, lean_object* v_alt_x27_2589_){
_start:
{
uint8_t v_hasUnitThunk_2590_; 
v_hasUnitThunk_2590_ = lean_ctor_get_uint8(v___x_2586_, sizeof(void*)*2);
if (v_hasUnitThunk_2590_ == 0)
{
lean_object* v___x_2591_; 
lean_dec(v_inst_2588_);
v___x_2591_ = lean_apply_2(v_toPure_2587_, lean_box(0), v_alt_x27_2589_);
return v___x_2591_;
}
else
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec(v_toPure_2587_);
v___x_2592_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_2593_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_2594_ = lean_array_push(v___x_2593_, v_alt_x27_2589_);
v___x_2595_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2595_, 0, v___x_2592_);
lean_closure_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_apply_2(v_inst_2588_, lean_box(0), v___x_2595_);
return v___x_2596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v___x_2597_, lean_object* v_toPure_2598_, lean_object* v_inst_2599_, lean_object* v_alt_x27_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v___x_2597_, v_toPure_2598_, v_inst_2599_, v_alt_x27_2600_);
lean_dec_ref(v___x_2597_);
return v_res_2601_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v_ys_2602_, lean_object* v_ys2_2603_, lean_object* v_ys3_2604_, lean_object* v_ys4_2605_, uint8_t v___x_2606_, uint8_t v_useSplitter_2607_, lean_object* v_inst_2608_, lean_object* v_alt_x27_2609_){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; uint8_t v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2610_ = l_Array_append___redArg(v_ys_2602_, v_ys2_2603_);
v___x_2611_ = l_Array_append___redArg(v___x_2610_, v_ys3_2604_);
v___x_2612_ = l_Array_append___redArg(v___x_2611_, v_ys4_2605_);
v___x_2613_ = 1;
v___x_2614_ = lean_box(v___x_2606_);
v___x_2615_ = lean_box(v_useSplitter_2607_);
v___x_2616_ = lean_box(v___x_2606_);
v___x_2617_ = lean_box(v_useSplitter_2607_);
v___x_2618_ = lean_box(v___x_2613_);
v___x_2619_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2619_, 0, v___x_2612_);
lean_closure_set(v___x_2619_, 1, v_alt_x27_2609_);
lean_closure_set(v___x_2619_, 2, v___x_2614_);
lean_closure_set(v___x_2619_, 3, v___x_2615_);
lean_closure_set(v___x_2619_, 4, v___x_2616_);
lean_closure_set(v___x_2619_, 5, v___x_2617_);
lean_closure_set(v___x_2619_, 6, v___x_2618_);
v___x_2620_ = lean_apply_2(v_inst_2608_, lean_box(0), v___x_2619_);
return v___x_2620_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__36_0interp(lean_interpreter_value* stack)
{
lean_object* v_ys_2602_ = stack[0].m_obj;
lean_object* v_ys2_2603_ = stack[1].m_obj;
lean_object* v_ys3_2604_ = stack[2].m_obj;
lean_object* v_ys4_2605_ = stack[3].m_obj;
uint8_t v___x_2606_ = stack[4].m_num;
uint8_t v_useSplitter_2607_ = stack[5].m_num;
lean_object* v_inst_2608_ = stack[6].m_obj;
lean_object* v_alt_x27_2609_ = stack[7].m_obj;
lean_object* v_res_2621_;
v_res_2621_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2602_, v_ys2_2603_, v_ys3_2604_, v_ys4_2605_, v___x_2606_, v_useSplitter_2607_, v_inst_2608_, v_alt_x27_2609_);
stack->m_obj
 = v_res_2621_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v_ys_2622_, lean_object* v_ys2_2623_, lean_object* v_ys3_2624_, lean_object* v_ys4_2625_, lean_object* v___x_2626_, lean_object* v_useSplitter_2627_, lean_object* v_inst_2628_, lean_object* v_alt_x27_2629_){
_start:
{
uint8_t v___x_14053__boxed_2630_; uint8_t v_useSplitter_boxed_2631_; lean_object* v_res_2632_; 
v___x_14053__boxed_2630_ = lean_unbox(v___x_2626_);
v_useSplitter_boxed_2631_ = lean_unbox(v_useSplitter_2627_);
v_res_2632_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2622_, v_ys2_2623_, v_ys3_2624_, v_ys4_2625_, v___x_14053__boxed_2630_, v_useSplitter_boxed_2631_, v_inst_2628_, v_alt_x27_2629_);
lean_dec_ref(v_ys4_2625_);
lean_dec_ref(v_ys3_2624_);
lean_dec_ref(v_ys2_2623_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_args_2633_, lean_object* v_ys_2634_, lean_object* v_ys2_2635_, lean_object* v_ys3_2636_, lean_object* v_ys4_2637_, lean_object* v_onAlt_2638_, lean_object* v_next_2639_, lean_object* v_altType_2640_, lean_object* v_toBind_2641_, lean_object* v___f_2642_, lean_object* v_alt_2643_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2644_, 0, v_args_2633_);
lean_ctor_set(v___x_2644_, 1, v_ys_2634_);
lean_ctor_set(v___x_2644_, 2, v_ys2_2635_);
lean_ctor_set(v___x_2644_, 3, v_ys3_2636_);
lean_ctor_set(v___x_2644_, 4, v_ys4_2637_);
v___x_2645_ = lean_apply_4(v_onAlt_2638_, v_next_2639_, v_altType_2640_, v___x_2644_, v_alt_2643_);
v___x_2646_ = lean_apply_4(v_toBind_2641_, lean_box(0), lean_box(0), v___x_2645_, v___f_2642_);
return v___x_2646_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_toMonadExceptOf_2647_, lean_object* v_ys_2648_, lean_object* v_ys2_2649_, lean_object* v_ys3_2650_, uint8_t v___x_2651_, uint8_t v_useSplitter_2652_, lean_object* v_inst_2653_, lean_object* v_args_2654_, lean_object* v_onAlt_2655_, lean_object* v_next_2656_, lean_object* v_toBind_2657_, lean_object* v___x_2658_, lean_object* v___f_2659_, lean_object* v_ys4_2660_, lean_object* v_altType_2661_){
_start:
{
lean_object* v_tryCatch_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___f_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_tryCatch_2662_ = lean_ctor_get(v_toMonadExceptOf_2647_, 1);
lean_inc(v_tryCatch_2662_);
lean_dec_ref(v_toMonadExceptOf_2647_);
v___x_2663_ = lean_box(v___x_2651_);
v___x_2664_ = lean_box(v_useSplitter_2652_);
lean_inc(v_inst_2653_);
lean_inc_ref(v_ys4_2660_);
lean_inc_ref_n(v_ys3_2650_, 2);
lean_inc_ref(v_ys2_2649_);
lean_inc_ref(v_ys_2648_);
v___f_2665_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2665_, 0, v_ys_2648_);
lean_closure_set(v___f_2665_, 1, v_ys2_2649_);
lean_closure_set(v___f_2665_, 2, v_ys3_2650_);
lean_closure_set(v___f_2665_, 3, v_ys4_2660_);
lean_closure_set(v___f_2665_, 4, v___x_2663_);
lean_closure_set(v___f_2665_, 5, v___x_2664_);
lean_closure_set(v___f_2665_, 6, v_inst_2653_);
lean_inc(v_toBind_2657_);
lean_inc_ref(v_args_2654_);
v___f_2666_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 11, 10);
lean_closure_set(v___f_2666_, 0, v_args_2654_);
lean_closure_set(v___f_2666_, 1, v_ys_2648_);
lean_closure_set(v___f_2666_, 2, v_ys2_2649_);
lean_closure_set(v___f_2666_, 3, v_ys3_2650_);
lean_closure_set(v___f_2666_, 4, v_ys4_2660_);
lean_closure_set(v___f_2666_, 5, v_onAlt_2655_);
lean_closure_set(v___f_2666_, 6, v_next_2656_);
lean_closure_set(v___f_2666_, 7, v_altType_2661_);
lean_closure_set(v___f_2666_, 8, v_toBind_2657_);
lean_closure_set(v___f_2666_, 9, v___f_2665_);
v___x_2667_ = l_Array_append___redArg(v_args_2654_, v_ys3_2650_);
lean_dec_ref(v_ys3_2650_);
v___x_2668_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2668_, 0, v___x_2658_);
lean_closure_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = lean_apply_2(v_inst_2653_, lean_box(0), v___x_2668_);
v___x_2670_ = lean_apply_3(v_tryCatch_2662_, lean_box(0), v___x_2669_, v___f_2659_);
v___x_2671_ = lean_apply_4(v_toBind_2657_, lean_box(0), lean_box(0), v___x_2670_, v___f_2666_);
return v___x_2671_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__38_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadExceptOf_2647_ = stack[0].m_obj;
lean_object* v_ys_2648_ = stack[1].m_obj;
lean_object* v_ys2_2649_ = stack[2].m_obj;
lean_object* v_ys3_2650_ = stack[3].m_obj;
uint8_t v___x_2651_ = stack[4].m_num;
uint8_t v_useSplitter_2652_ = stack[5].m_num;
lean_object* v_inst_2653_ = stack[6].m_obj;
lean_object* v_args_2654_ = stack[7].m_obj;
lean_object* v_onAlt_2655_ = stack[8].m_obj;
lean_object* v_next_2656_ = stack[9].m_obj;
lean_object* v_toBind_2657_ = stack[10].m_obj;
lean_object* v___x_2658_ = stack[11].m_obj;
lean_object* v___f_2659_ = stack[12].m_obj;
lean_object* v_ys4_2660_ = stack[13].m_obj;
lean_object* v_altType_2661_ = stack[14].m_obj;
lean_object* v_res_2672_;
v_res_2672_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_toMonadExceptOf_2647_, v_ys_2648_, v_ys2_2649_, v_ys3_2650_, v___x_2651_, v_useSplitter_2652_, v_inst_2653_, v_args_2654_, v_onAlt_2655_, v_next_2656_, v_toBind_2657_, v___x_2658_, v___f_2659_, v_ys4_2660_, v_altType_2661_);
stack->m_obj
 = v_res_2672_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_toMonadExceptOf_2673_, lean_object* v_ys_2674_, lean_object* v_ys2_2675_, lean_object* v_ys3_2676_, lean_object* v___x_2677_, lean_object* v_useSplitter_2678_, lean_object* v_inst_2679_, lean_object* v_args_2680_, lean_object* v_onAlt_2681_, lean_object* v_next_2682_, lean_object* v_toBind_2683_, lean_object* v___x_2684_, lean_object* v___f_2685_, lean_object* v_ys4_2686_, lean_object* v_altType_2687_){
_start:
{
uint8_t v___x_14108__boxed_2688_; uint8_t v_useSplitter_boxed_2689_; lean_object* v_res_2690_; 
v___x_14108__boxed_2688_ = lean_unbox(v___x_2677_);
v_useSplitter_boxed_2689_ = lean_unbox(v_useSplitter_2678_);
v_res_2690_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_toMonadExceptOf_2673_, v_ys_2674_, v_ys2_2675_, v_ys3_2676_, v___x_14108__boxed_2688_, v_useSplitter_boxed_2689_, v_inst_2679_, v_args_2680_, v_onAlt_2681_, v_next_2682_, v_toBind_2683_, v___x_2684_, v___f_2685_, v_ys4_2686_, v_altType_2687_);
return v_res_2690_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_toMonadExceptOf_2691_, lean_object* v_ys_2692_, lean_object* v_ys2_2693_, uint8_t v___x_2694_, uint8_t v_useSplitter_2695_, lean_object* v_inst_2696_, lean_object* v_args_2697_, lean_object* v_onAlt_2698_, lean_object* v_next_2699_, lean_object* v_toBind_2700_, lean_object* v___x_2701_, lean_object* v___f_2702_, lean_object* v_fst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_ys3_2706_, lean_object* v_altType_2707_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___f_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2708_ = lean_box(v___x_2694_);
v___x_2709_ = lean_box(v_useSplitter_2695_);
v___f_2710_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2710_, 0, v_toMonadExceptOf_2691_);
lean_closure_set(v___f_2710_, 1, v_ys_2692_);
lean_closure_set(v___f_2710_, 2, v_ys2_2693_);
lean_closure_set(v___f_2710_, 3, v_ys3_2706_);
lean_closure_set(v___f_2710_, 4, v___x_2708_);
lean_closure_set(v___f_2710_, 5, v___x_2709_);
lean_closure_set(v___f_2710_, 6, v_inst_2696_);
lean_closure_set(v___f_2710_, 7, v_args_2697_);
lean_closure_set(v___f_2710_, 8, v_onAlt_2698_);
lean_closure_set(v___f_2710_, 9, v_next_2699_);
lean_closure_set(v___f_2710_, 10, v_toBind_2700_);
lean_closure_set(v___f_2710_, 11, v___x_2701_);
lean_closure_set(v___f_2710_, 12, v___f_2702_);
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_fst_2703_);
v___x_2712_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2704_, v_inst_2705_, v_altType_2707_, v___x_2711_, v___f_2710_, v___x_2694_, v___x_2694_);
return v___x_2712_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__39_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadExceptOf_2691_ = stack[0].m_obj;
lean_object* v_ys_2692_ = stack[1].m_obj;
lean_object* v_ys2_2693_ = stack[2].m_obj;
uint8_t v___x_2694_ = stack[3].m_num;
uint8_t v_useSplitter_2695_ = stack[4].m_num;
lean_object* v_inst_2696_ = stack[5].m_obj;
lean_object* v_args_2697_ = stack[6].m_obj;
lean_object* v_onAlt_2698_ = stack[7].m_obj;
lean_object* v_next_2699_ = stack[8].m_obj;
lean_object* v_toBind_2700_ = stack[9].m_obj;
lean_object* v___x_2701_ = stack[10].m_obj;
lean_object* v___f_2702_ = stack[11].m_obj;
lean_object* v_fst_2703_ = stack[12].m_obj;
lean_object* v_inst_2704_ = stack[13].m_obj;
lean_object* v_inst_2705_ = stack[14].m_obj;
lean_object* v_ys3_2706_ = stack[15].m_obj;
lean_object* v_altType_2707_ = stack[16].m_obj;
lean_object* v_res_2713_;
v_res_2713_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_toMonadExceptOf_2691_, v_ys_2692_, v_ys2_2693_, v___x_2694_, v_useSplitter_2695_, v_inst_2696_, v_args_2697_, v_onAlt_2698_, v_next_2699_, v_toBind_2700_, v___x_2701_, v___f_2702_, v_fst_2703_, v_inst_2704_, v_inst_2705_, v_ys3_2706_, v_altType_2707_);
stack->m_obj
 = v_res_2713_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2714_ = _args[0];
lean_object* v_ys_2715_ = _args[1];
lean_object* v_ys2_2716_ = _args[2];
lean_object* v___x_2717_ = _args[3];
lean_object* v_useSplitter_2718_ = _args[4];
lean_object* v_inst_2719_ = _args[5];
lean_object* v_args_2720_ = _args[6];
lean_object* v_onAlt_2721_ = _args[7];
lean_object* v_next_2722_ = _args[8];
lean_object* v_toBind_2723_ = _args[9];
lean_object* v___x_2724_ = _args[10];
lean_object* v___f_2725_ = _args[11];
lean_object* v_fst_2726_ = _args[12];
lean_object* v_inst_2727_ = _args[13];
lean_object* v_inst_2728_ = _args[14];
lean_object* v_ys3_2729_ = _args[15];
lean_object* v_altType_2730_ = _args[16];
_start:
{
uint8_t v___x_14155__boxed_2731_; uint8_t v_useSplitter_boxed_2732_; lean_object* v_res_2733_; 
v___x_14155__boxed_2731_ = lean_unbox(v___x_2717_);
v_useSplitter_boxed_2732_ = lean_unbox(v_useSplitter_2718_);
v_res_2733_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_toMonadExceptOf_2714_, v_ys_2715_, v_ys2_2716_, v___x_14155__boxed_2731_, v_useSplitter_boxed_2732_, v_inst_2719_, v_args_2720_, v_onAlt_2721_, v_next_2722_, v_toBind_2723_, v___x_2724_, v___f_2725_, v_fst_2726_, v_inst_2727_, v_inst_2728_, v_ys3_2729_, v_altType_2730_);
return v_res_2733_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_toMonadExceptOf_2734_, lean_object* v_ys_2735_, uint8_t v___x_2736_, uint8_t v_useSplitter_2737_, lean_object* v_inst_2738_, lean_object* v_args_2739_, lean_object* v_onAlt_2740_, lean_object* v_next_2741_, lean_object* v_toBind_2742_, lean_object* v___x_2743_, lean_object* v___f_2744_, lean_object* v_fst_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_, lean_object* v_numDiscrEqs_2748_, lean_object* v_ys2_2749_, lean_object* v_altType_2750_){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___f_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2751_ = lean_box(v___x_2736_);
v___x_2752_ = lean_box(v_useSplitter_2737_);
lean_inc_ref(v_inst_2747_);
lean_inc_ref(v_inst_2746_);
v___f_2753_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2753_, 0, v_toMonadExceptOf_2734_);
lean_closure_set(v___f_2753_, 1, v_ys_2735_);
lean_closure_set(v___f_2753_, 2, v_ys2_2749_);
lean_closure_set(v___f_2753_, 3, v___x_2751_);
lean_closure_set(v___f_2753_, 4, v___x_2752_);
lean_closure_set(v___f_2753_, 5, v_inst_2738_);
lean_closure_set(v___f_2753_, 6, v_args_2739_);
lean_closure_set(v___f_2753_, 7, v_onAlt_2740_);
lean_closure_set(v___f_2753_, 8, v_next_2741_);
lean_closure_set(v___f_2753_, 9, v_toBind_2742_);
lean_closure_set(v___f_2753_, 10, v___x_2743_);
lean_closure_set(v___f_2753_, 11, v___f_2744_);
lean_closure_set(v___f_2753_, 12, v_fst_2745_);
lean_closure_set(v___f_2753_, 13, v_inst_2746_);
lean_closure_set(v___f_2753_, 14, v_inst_2747_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_numDiscrEqs_2748_);
v___x_2755_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2746_, v_inst_2747_, v_altType_2750_, v___x_2754_, v___f_2753_, v___x_2736_, v___x_2736_);
return v___x_2755_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__40_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMonadExceptOf_2734_ = stack[0].m_obj;
lean_object* v_ys_2735_ = stack[1].m_obj;
uint8_t v___x_2736_ = stack[2].m_num;
uint8_t v_useSplitter_2737_ = stack[3].m_num;
lean_object* v_inst_2738_ = stack[4].m_obj;
lean_object* v_args_2739_ = stack[5].m_obj;
lean_object* v_onAlt_2740_ = stack[6].m_obj;
lean_object* v_next_2741_ = stack[7].m_obj;
lean_object* v_toBind_2742_ = stack[8].m_obj;
lean_object* v___x_2743_ = stack[9].m_obj;
lean_object* v___f_2744_ = stack[10].m_obj;
lean_object* v_fst_2745_ = stack[11].m_obj;
lean_object* v_inst_2746_ = stack[12].m_obj;
lean_object* v_inst_2747_ = stack[13].m_obj;
lean_object* v_numDiscrEqs_2748_ = stack[14].m_obj;
lean_object* v_ys2_2749_ = stack[15].m_obj;
lean_object* v_altType_2750_ = stack[16].m_obj;
lean_object* v_res_2756_;
v_res_2756_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_toMonadExceptOf_2734_, v_ys_2735_, v___x_2736_, v_useSplitter_2737_, v_inst_2738_, v_args_2739_, v_onAlt_2740_, v_next_2741_, v_toBind_2742_, v___x_2743_, v___f_2744_, v_fst_2745_, v_inst_2746_, v_inst_2747_, v_numDiscrEqs_2748_, v_ys2_2749_, v_altType_2750_);
stack->m_obj
 = v_res_2756_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2757_ = _args[0];
lean_object* v_ys_2758_ = _args[1];
lean_object* v___x_2759_ = _args[2];
lean_object* v_useSplitter_2760_ = _args[3];
lean_object* v_inst_2761_ = _args[4];
lean_object* v_args_2762_ = _args[5];
lean_object* v_onAlt_2763_ = _args[6];
lean_object* v_next_2764_ = _args[7];
lean_object* v_toBind_2765_ = _args[8];
lean_object* v___x_2766_ = _args[9];
lean_object* v___f_2767_ = _args[10];
lean_object* v_fst_2768_ = _args[11];
lean_object* v_inst_2769_ = _args[12];
lean_object* v_inst_2770_ = _args[13];
lean_object* v_numDiscrEqs_2771_ = _args[14];
lean_object* v_ys2_2772_ = _args[15];
lean_object* v_altType_2773_ = _args[16];
_start:
{
uint8_t v___x_14200__boxed_2774_; uint8_t v_useSplitter_boxed_2775_; lean_object* v_res_2776_; 
v___x_14200__boxed_2774_ = lean_unbox(v___x_2759_);
v_useSplitter_boxed_2775_ = lean_unbox(v_useSplitter_2760_);
v_res_2776_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_toMonadExceptOf_2757_, v_ys_2758_, v___x_14200__boxed_2774_, v_useSplitter_boxed_2775_, v_inst_2761_, v_args_2762_, v_onAlt_2763_, v_next_2764_, v_toBind_2765_, v___x_2766_, v___f_2767_, v_fst_2768_, v_inst_2769_, v_inst_2770_, v_numDiscrEqs_2771_, v_ys2_2772_, v_altType_2773_);
return v_res_2776_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_, lean_object* v___f_2780_, uint8_t v___x_2781_, lean_object* v_toBind_2782_, lean_object* v___f_2783_, lean_object* v_altType_2784_){
_start:
{
lean_object* v_numOverlaps_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_numOverlaps_2785_ = lean_ctor_get(v___x_2777_, 1);
lean_inc(v_numOverlaps_2785_);
v___x_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2786_, 0, v_numOverlaps_2785_);
v___x_2787_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2778_, v_inst_2779_, v_altType_2784_, v___x_2786_, v___f_2780_, v___x_2781_, v___x_2781_);
v___x_2788_ = lean_apply_4(v_toBind_2782_, lean_box(0), lean_box(0), v___x_2787_, v___f_2783_);
return v___x_2788_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__41_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2777_ = stack[0].m_obj;
lean_object* v_inst_2778_ = stack[1].m_obj;
lean_object* v_inst_2779_ = stack[2].m_obj;
lean_object* v___f_2780_ = stack[3].m_obj;
uint8_t v___x_2781_ = stack[4].m_num;
lean_object* v_toBind_2782_ = stack[5].m_obj;
lean_object* v___f_2783_ = stack[6].m_obj;
lean_object* v_altType_2784_ = stack[7].m_obj;
lean_object* v_res_2789_;
v_res_2789_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2777_, v_inst_2778_, v_inst_2779_, v___f_2780_, v___x_2781_, v_toBind_2782_, v___f_2783_, v_altType_2784_);
stack->m_obj
 = v_res_2789_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2790_, lean_object* v_inst_2791_, lean_object* v_inst_2792_, lean_object* v___f_2793_, lean_object* v___x_2794_, lean_object* v_toBind_2795_, lean_object* v___f_2796_, lean_object* v_altType_2797_){
_start:
{
uint8_t v___x_14249__boxed_2798_; lean_object* v_res_2799_; 
v___x_14249__boxed_2798_ = lean_unbox(v___x_2794_);
v_res_2799_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2790_, v_inst_2791_, v_inst_2792_, v___f_2793_, v___x_14249__boxed_2798_, v_toBind_2795_, v___f_2796_, v_altType_2797_);
lean_dec_ref(v___x_2790_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2800_, lean_object* v_altType_2801_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_apply_1(v___f_2800_, v_altType_2801_);
return v___x_2802_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2807_ = lean_box(0);
v___x_2808_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2809_ = l_Lean_mkConst(v___x_2808_, v___x_2807_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* v___x_2810_, lean_object* v_toPure_2811_, lean_object* v_toBind_2812_, lean_object* v___f_2813_, lean_object* v___x_2814_, lean_object* v_inst_2815_, lean_object* v___f_2816_, lean_object* v_altType_2817_){
_start:
{
uint8_t v_hasUnitThunk_2818_; 
v_hasUnitThunk_2818_ = lean_ctor_get_uint8(v___x_2810_, sizeof(void*)*2);
if (v_hasUnitThunk_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec(v___f_2816_);
lean_dec(v_inst_2815_);
v___x_2819_ = lean_apply_2(v_toPure_2811_, lean_box(0), v_altType_2817_);
v___x_2820_ = lean_apply_4(v_toBind_2812_, lean_box(0), lean_box(0), v___x_2819_, v___f_2813_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
lean_dec(v___f_2813_);
lean_dec(v_toPure_2811_);
v___x_2821_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2822_ = lean_mk_empty_array_with_capacity(v___x_2814_);
v___x_2823_ = lean_array_push(v___x_2822_, v___x_2821_);
v___x_2824_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2824_, 0, v_altType_2817_);
lean_closure_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_apply_2(v_inst_2815_, lean_box(0), v___x_2824_);
v___x_2826_ = lean_apply_4(v_toBind_2812_, lean_box(0), lean_box(0), v___x_2825_, v___f_2816_);
return v___x_2826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v___x_2827_, lean_object* v_toPure_2828_, lean_object* v_toBind_2829_, lean_object* v___f_2830_, lean_object* v___x_2831_, lean_object* v_inst_2832_, lean_object* v___f_2833_, lean_object* v_altType_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v___x_2827_, v_toPure_2828_, v_toBind_2829_, v___f_2830_, v___x_2831_, v_inst_2832_, v___f_2833_, v_altType_2834_);
lean_dec(v___x_2831_);
lean_dec_ref(v___x_2827_);
return v_res_2835_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2839_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2840_ = lean_unsigned_to_nat(8u);
v___x_2841_ = lean_unsigned_to_nat(363u);
v___x_2842_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2843_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2844_ = l_mkPanicMessageWithDecl(v___x_2843_, v___x_2842_, v___x_2841_, v___x_2840_, v___x_2839_);
return v___x_2844_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2845_, lean_object* v___x_2846_, lean_object* v_toMonadExceptOf_2847_, uint8_t v___x_2848_, uint8_t v_useSplitter_2849_, lean_object* v_inst_2850_, lean_object* v_onAlt_2851_, lean_object* v_next_2852_, lean_object* v_toBind_2853_, lean_object* v___x_2854_, lean_object* v___f_2855_, lean_object* v_fst_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_numDiscrEqs_2859_, lean_object* v___f_2860_, lean_object* v___x_2861_, lean_object* v_toPure_2862_, lean_object* v___x_2863_, lean_object* v___x_2864_, lean_object* v_ys_2865_, lean_object* v_args_2866_){
_start:
{
lean_object* v_numFields_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_numFields_2867_ = lean_ctor_get(v___x_2845_, 0);
v___x_2868_ = lean_array_get_size(v_ys_2865_);
v___x_2869_ = lean_nat_dec_eq(v___x_2868_, v_numFields_2867_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec_ref(v_args_2866_);
lean_dec_ref(v_ys_2865_);
lean_dec_ref(v___x_2864_);
lean_dec(v___x_2863_);
lean_dec(v_toPure_2862_);
lean_dec_ref(v___x_2861_);
lean_dec(v___f_2860_);
lean_dec(v_numDiscrEqs_2859_);
lean_dec_ref(v_inst_2858_);
lean_dec_ref(v_inst_2857_);
lean_dec(v_fst_2856_);
lean_dec(v___f_2855_);
lean_dec_ref(v___x_2854_);
lean_dec(v_toBind_2853_);
lean_dec(v_next_2852_);
lean_dec(v_onAlt_2851_);
lean_dec(v_inst_2850_);
lean_dec_ref(v_toMonadExceptOf_2847_);
lean_dec_ref(v___x_2845_);
v___x_2870_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2871_ = l_panic___redArg(v___x_2846_, v___x_2870_);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; lean_object* v___f_2877_; lean_object* v___f_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2872_ = lean_box(v___x_2848_);
v___x_2873_ = lean_box(v_useSplitter_2849_);
lean_inc_ref(v_inst_2858_);
lean_inc_ref(v_inst_2857_);
lean_inc_n(v_toBind_2853_, 3);
lean_inc_n(v_inst_2850_, 2);
lean_inc_ref(v_ys_2865_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2874_, 0, v_toMonadExceptOf_2847_);
lean_closure_set(v___f_2874_, 1, v_ys_2865_);
lean_closure_set(v___f_2874_, 2, v___x_2872_);
lean_closure_set(v___f_2874_, 3, v___x_2873_);
lean_closure_set(v___f_2874_, 4, v_inst_2850_);
lean_closure_set(v___f_2874_, 5, v_args_2866_);
lean_closure_set(v___f_2874_, 6, v_onAlt_2851_);
lean_closure_set(v___f_2874_, 7, v_next_2852_);
lean_closure_set(v___f_2874_, 8, v_toBind_2853_);
lean_closure_set(v___f_2874_, 9, v___x_2854_);
lean_closure_set(v___f_2874_, 10, v___f_2855_);
lean_closure_set(v___f_2874_, 11, v_fst_2856_);
lean_closure_set(v___f_2874_, 12, v_inst_2857_);
lean_closure_set(v___f_2874_, 13, v_inst_2858_);
lean_closure_set(v___f_2874_, 14, v_numDiscrEqs_2859_);
v___x_2875_ = lean_box(v___x_2848_);
v___f_2876_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2876_, 0, v___x_2845_);
lean_closure_set(v___f_2876_, 1, v_inst_2857_);
lean_closure_set(v___f_2876_, 2, v_inst_2858_);
lean_closure_set(v___f_2876_, 3, v___f_2874_);
lean_closure_set(v___f_2876_, 4, v___x_2875_);
lean_closure_set(v___f_2876_, 5, v_toBind_2853_);
lean_closure_set(v___f_2876_, 6, v___f_2860_);
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2877_, 0, v___f_2876_);
lean_inc_ref(v___f_2877_);
v___f_2878_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2878_, 0, v___x_2861_);
lean_closure_set(v___f_2878_, 1, v_toPure_2862_);
lean_closure_set(v___f_2878_, 2, v_toBind_2853_);
lean_closure_set(v___f_2878_, 3, v___f_2877_);
lean_closure_set(v___f_2878_, 4, v___x_2863_);
lean_closure_set(v___f_2878_, 5, v_inst_2850_);
lean_closure_set(v___f_2878_, 6, v___f_2877_);
v___x_2879_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2879_, 0, v___x_2864_);
lean_closure_set(v___x_2879_, 1, v_ys_2865_);
v___x_2880_ = lean_apply_2(v_inst_2850_, lean_box(0), v___x_2879_);
v___x_2881_ = lean_apply_4(v_toBind_2853_, lean_box(0), lean_box(0), v___x_2880_, v___f_2878_);
return v___x_2881_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__43_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2845_ = stack[0].m_obj;
lean_object* v___x_2846_ = stack[1].m_obj;
lean_object* v_toMonadExceptOf_2847_ = stack[2].m_obj;
uint8_t v___x_2848_ = stack[3].m_num;
uint8_t v_useSplitter_2849_ = stack[4].m_num;
lean_object* v_inst_2850_ = stack[5].m_obj;
lean_object* v_onAlt_2851_ = stack[6].m_obj;
lean_object* v_next_2852_ = stack[7].m_obj;
lean_object* v_toBind_2853_ = stack[8].m_obj;
lean_object* v___x_2854_ = stack[9].m_obj;
lean_object* v___f_2855_ = stack[10].m_obj;
lean_object* v_fst_2856_ = stack[11].m_obj;
lean_object* v_inst_2857_ = stack[12].m_obj;
lean_object* v_inst_2858_ = stack[13].m_obj;
lean_object* v_numDiscrEqs_2859_ = stack[14].m_obj;
lean_object* v___f_2860_ = stack[15].m_obj;
lean_object* v___x_2861_ = stack[16].m_obj;
lean_object* v_toPure_2862_ = stack[17].m_obj;
lean_object* v___x_2863_ = stack[18].m_obj;
lean_object* v___x_2864_ = stack[19].m_obj;
lean_object* v_ys_2865_ = stack[20].m_obj;
lean_object* v_args_2866_ = stack[21].m_obj;
lean_object* v_res_2882_;
v_res_2882_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2845_, v___x_2846_, v_toMonadExceptOf_2847_, v___x_2848_, v_useSplitter_2849_, v_inst_2850_, v_onAlt_2851_, v_next_2852_, v_toBind_2853_, v___x_2854_, v___f_2855_, v_fst_2856_, v_inst_2857_, v_inst_2858_, v_numDiscrEqs_2859_, v___f_2860_, v___x_2861_, v_toPure_2862_, v___x_2863_, v___x_2864_, v_ys_2865_, v_args_2866_);
stack->m_obj
 = v_res_2882_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2883_ = _args[0];
lean_object* v___x_2884_ = _args[1];
lean_object* v_toMonadExceptOf_2885_ = _args[2];
lean_object* v___x_2886_ = _args[3];
lean_object* v_useSplitter_2887_ = _args[4];
lean_object* v_inst_2888_ = _args[5];
lean_object* v_onAlt_2889_ = _args[6];
lean_object* v_next_2890_ = _args[7];
lean_object* v_toBind_2891_ = _args[8];
lean_object* v___x_2892_ = _args[9];
lean_object* v___f_2893_ = _args[10];
lean_object* v_fst_2894_ = _args[11];
lean_object* v_inst_2895_ = _args[12];
lean_object* v_inst_2896_ = _args[13];
lean_object* v_numDiscrEqs_2897_ = _args[14];
lean_object* v___f_2898_ = _args[15];
lean_object* v___x_2899_ = _args[16];
lean_object* v_toPure_2900_ = _args[17];
lean_object* v___x_2901_ = _args[18];
lean_object* v___x_2902_ = _args[19];
lean_object* v_ys_2903_ = _args[20];
lean_object* v_args_2904_ = _args[21];
_start:
{
uint8_t v___x_14388__boxed_2905_; uint8_t v_useSplitter_boxed_2906_; lean_object* v_res_2907_; 
v___x_14388__boxed_2905_ = lean_unbox(v___x_2886_);
v_useSplitter_boxed_2906_ = lean_unbox(v_useSplitter_2887_);
v_res_2907_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2883_, v___x_2884_, v_toMonadExceptOf_2885_, v___x_14388__boxed_2905_, v_useSplitter_boxed_2906_, v_inst_2888_, v_onAlt_2889_, v_next_2890_, v_toBind_2891_, v___x_2892_, v___f_2893_, v_fst_2894_, v_inst_2895_, v_inst_2896_, v_numDiscrEqs_2897_, v___f_2898_, v___x_2899_, v_toPure_2900_, v___x_2901_, v___x_2902_, v_ys_2903_, v_args_2904_);
lean_dec(v___x_2884_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v_fst_2908_, lean_object* v___x_2909_, lean_object* v___x_2910_, lean_object* v___x_2911_, lean_object* v___x_2912_, lean_object* v___x_2913_, lean_object* v_toPure_2914_, lean_object* v_alt_x27_2915_){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2916_ = lean_array_push(v_fst_2908_, v_alt_x27_2915_);
v___x_2917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2909_);
lean_ctor_set(v___x_2917_, 1, v___x_2910_);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2911_);
lean_ctor_set(v___x_2918_, 1, v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2912_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2913_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2916_);
lean_ctor_set(v___x_2921_, 1, v___x_2920_);
v___x_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2921_);
v___x_2923_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_2922_);
return v___x_2923_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2925_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0));
v___x_2926_ = lean_unsigned_to_nat(6u);
v___x_2927_ = lean_unsigned_to_nat(361u);
v___x_2928_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2929_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2930_ = l_mkPanicMessageWithDecl(v___x_2929_, v___x_2928_, v___x_2927_, v___x_2926_, v___x_2925_);
return v___x_2930_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2931_, lean_object* v_toPure_2932_, lean_object* v_toBind_2933_, lean_object* v___f_2934_, lean_object* v___x_2935_, lean_object* v___x_2936_, lean_object* v_inst_2937_, lean_object* v___x_2938_, lean_object* v_toMonadExceptOf_2939_, uint8_t v___x_2940_, uint8_t v_useSplitter_2941_, lean_object* v_onAlt_2942_, lean_object* v___f_2943_, lean_object* v_fst_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_numDiscrEqs_2947_, lean_object* v_next_2948_, lean_object* v_acc_2949_, lean_object* v_h_2950_, lean_object* v_G_2951_){
_start:
{
uint8_t v___x_2952_; 
v___x_2952_ = lean_nat_dec_lt(v_next_2948_, v___x_2931_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; 
lean_dec(v_G_2951_);
lean_dec(v_next_2948_);
lean_dec(v_numDiscrEqs_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec(v_fst_2944_);
lean_dec(v___f_2943_);
lean_dec(v_onAlt_2942_);
lean_dec_ref(v_toMonadExceptOf_2939_);
lean_dec(v___x_2938_);
lean_dec(v_inst_2937_);
lean_dec(v___f_2934_);
lean_dec(v_toBind_2933_);
v___x_2953_ = lean_apply_2(v_toPure_2932_, lean_box(0), v_acc_2949_);
return v___x_2953_;
}
else
{
lean_object* v_snd_2954_; lean_object* v_snd_2955_; lean_object* v_snd_2956_; lean_object* v_snd_2957_; lean_object* v_snd_2958_; lean_object* v_fst_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_3169_; 
v_snd_2954_ = lean_ctor_get(v_acc_2949_, 1);
lean_inc(v_snd_2954_);
v_snd_2955_ = lean_ctor_get(v_snd_2954_, 1);
lean_inc(v_snd_2955_);
v_snd_2956_ = lean_ctor_get(v_snd_2955_, 1);
lean_inc(v_snd_2956_);
v_snd_2957_ = lean_ctor_get(v_snd_2956_, 1);
lean_inc(v_snd_2957_);
v_snd_2958_ = lean_ctor_get(v_snd_2957_, 1);
lean_inc(v_snd_2958_);
v_fst_2959_ = lean_ctor_get(v_acc_2949_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_acc_2949_);
if (v_isSharedCheck_3169_ == 0)
{
lean_object* v_unused_3170_; 
v_unused_3170_ = lean_ctor_get(v_acc_2949_, 1);
lean_dec(v_unused_3170_);
v___x_2961_ = v_acc_2949_;
v_isShared_2962_ = v_isSharedCheck_3169_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_fst_2959_);
lean_dec(v_acc_2949_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_3169_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v_fst_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_3167_; 
v_fst_2963_ = lean_ctor_get(v_snd_2954_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_snd_2954_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v_snd_2954_, 1);
lean_dec(v_unused_3168_);
v___x_2965_ = v_snd_2954_;
v_isShared_2966_ = v_isSharedCheck_3167_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_fst_2963_);
lean_dec(v_snd_2954_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_3167_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v_fst_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_3165_; 
v_fst_2967_ = lean_ctor_get(v_snd_2955_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v_snd_2955_);
if (v_isSharedCheck_3165_ == 0)
{
lean_object* v_unused_3166_; 
v_unused_3166_ = lean_ctor_get(v_snd_2955_, 1);
lean_dec(v_unused_3166_);
v___x_2969_ = v_snd_2955_;
v_isShared_2970_ = v_isSharedCheck_3165_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_fst_2967_);
lean_dec(v_snd_2955_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_3165_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v_fst_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3163_; 
v_fst_2971_ = lean_ctor_get(v_snd_2956_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_snd_2956_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v_snd_2956_, 1);
lean_dec(v_unused_3164_);
v___x_2973_ = v_snd_2956_;
v_isShared_2974_ = v_isSharedCheck_3163_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_fst_2971_);
lean_dec(v_snd_2956_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3163_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v_fst_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3161_; 
v_fst_2975_ = lean_ctor_get(v_snd_2957_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_snd_2957_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v_snd_2957_, 1);
lean_dec(v_unused_3162_);
v___x_2977_ = v_snd_2957_;
v_isShared_2978_ = v_isSharedCheck_3161_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_fst_2975_);
lean_dec(v_snd_2957_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3161_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v_array_2979_; lean_object* v_start_2980_; lean_object* v_stop_2981_; lean_object* v___f_2982_; lean_object* v___y_2984_; uint8_t v___x_2987_; 
v_array_2979_ = lean_ctor_get(v_snd_2958_, 0);
v_start_2980_ = lean_ctor_get(v_snd_2958_, 1);
v_stop_2981_ = lean_ctor_get(v_snd_2958_, 2);
lean_inc(v_next_2948_);
lean_inc(v_toPure_2932_);
v___f_2982_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_2982_, 0, v_toPure_2932_);
lean_closure_set(v___f_2982_, 1, v_next_2948_);
lean_closure_set(v___f_2982_, 2, v_G_2951_);
v___x_2987_ = lean_nat_dec_lt(v_start_2980_, v_stop_2981_);
if (v___x_2987_ == 0)
{
lean_object* v___x_2989_; 
lean_dec(v_next_2948_);
lean_dec(v_numDiscrEqs_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec(v_fst_2944_);
lean_dec(v___f_2943_);
lean_dec(v_onAlt_2942_);
lean_dec_ref(v_toMonadExceptOf_2939_);
lean_dec(v___x_2938_);
lean_dec(v_inst_2937_);
if (v_isShared_2978_ == 0)
{
v___x_2989_ = v___x_2977_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_fst_2975_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_snd_2958_);
v___x_2989_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
lean_object* v___x_2991_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v___x_2989_);
v___x_2991_ = v___x_2973_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_fst_2971_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
lean_object* v___x_2993_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_2991_);
v___x_2993_ = v___x_2969_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_fst_2967_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_2993_);
v___x_2995_ = v___x_2965_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_fst_2963_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v___x_2993_);
v___x_2995_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_2995_);
v___x_2997_ = v___x_2961_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_fst_2959_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
v___x_2999_ = lean_apply_2(v_toPure_2932_, lean_box(0), v___x_2998_);
v___y_2984_ = v___x_2999_;
goto v___jp_2983_;
}
}
}
}
}
}
else
{
lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3157_; 
lean_inc(v_stop_2981_);
lean_inc(v_start_2980_);
lean_inc_ref(v_array_2979_);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_snd_2958_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; lean_object* v_unused_3159_; lean_object* v_unused_3160_; 
v_unused_3158_ = lean_ctor_get(v_snd_2958_, 2);
lean_dec(v_unused_3158_);
v_unused_3159_ = lean_ctor_get(v_snd_2958_, 1);
lean_dec(v_unused_3159_);
v_unused_3160_ = lean_ctor_get(v_snd_2958_, 0);
lean_dec(v_unused_3160_);
v___x_3006_ = v_snd_2958_;
v_isShared_3007_ = v_isSharedCheck_3157_;
goto v_resetjp_3005_;
}
else
{
lean_dec(v_snd_2958_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3157_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v_array_3008_; lean_object* v_start_3009_; lean_object* v_stop_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v_array_3008_ = lean_ctor_get(v_fst_2975_, 0);
v_start_3009_ = lean_ctor_get(v_fst_2975_, 1);
v_stop_3010_ = lean_ctor_get(v_fst_2975_, 2);
v___x_3011_ = lean_array_fget(v_array_2979_, v_start_2980_);
v___x_3012_ = lean_unsigned_to_nat(1u);
v___x_3013_ = lean_nat_add(v_start_2980_, v___x_3012_);
lean_dec(v_start_2980_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 1, v___x_3013_);
v___x_3015_ = v___x_3006_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_array_2979_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_stop_2981_);
v___x_3015_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_nat_dec_lt(v_start_3009_, v_stop_3010_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3018_; 
lean_dec(v___x_3011_);
lean_dec(v_next_2948_);
lean_dec(v_numDiscrEqs_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec(v_fst_2944_);
lean_dec(v___f_2943_);
lean_dec(v_onAlt_2942_);
lean_dec_ref(v_toMonadExceptOf_2939_);
lean_dec(v___x_2938_);
lean_dec(v_inst_2937_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 1, v___x_3015_);
v___x_3018_ = v___x_2977_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_fst_2975_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3015_);
v___x_3018_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3020_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v___x_3018_);
v___x_3020_ = v___x_2973_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_fst_2971_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3022_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_3020_);
v___x_3022_ = v___x_2969_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_fst_2967_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3024_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_3022_);
v___x_3024_ = v___x_2965_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_fst_2963_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_3024_);
v___x_3026_ = v___x_2961_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_fst_2959_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
v___x_3028_ = lean_apply_2(v_toPure_2932_, lean_box(0), v___x_3027_);
v___y_2984_ = v___x_3028_;
goto v___jp_2983_;
}
}
}
}
}
}
else
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3152_; 
lean_inc(v_stop_3010_);
lean_inc(v_start_3009_);
lean_inc_ref(v_array_3008_);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_fst_2975_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; lean_object* v_unused_3154_; lean_object* v_unused_3155_; 
v_unused_3153_ = lean_ctor_get(v_fst_2975_, 2);
lean_dec(v_unused_3153_);
v_unused_3154_ = lean_ctor_get(v_fst_2975_, 1);
lean_dec(v_unused_3154_);
v_unused_3155_ = lean_ctor_get(v_fst_2975_, 0);
lean_dec(v_unused_3155_);
v___x_3035_ = v_fst_2975_;
v_isShared_3036_ = v_isSharedCheck_3152_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_fst_2975_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3152_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v_array_3037_; lean_object* v_start_3038_; lean_object* v_stop_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v_array_3037_ = lean_ctor_get(v_fst_2971_, 0);
v_start_3038_ = lean_ctor_get(v_fst_2971_, 1);
v_stop_3039_ = lean_ctor_get(v_fst_2971_, 2);
v___x_3040_ = lean_array_fget(v_array_3008_, v_start_3009_);
v___x_3041_ = lean_nat_add(v_start_3009_, v___x_3012_);
lean_dec(v_start_3009_);
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 1, v___x_3041_);
v___x_3043_ = v___x_3035_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_array_3008_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3151_, 2, v_stop_3010_);
v___x_3043_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
uint8_t v___x_3044_; 
v___x_3044_ = lean_nat_dec_lt(v_start_3038_, v_stop_3039_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3046_; 
lean_dec(v___x_3040_);
lean_dec(v___x_3011_);
lean_dec(v_next_2948_);
lean_dec(v_numDiscrEqs_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec(v_fst_2944_);
lean_dec(v___f_2943_);
lean_dec(v_onAlt_2942_);
lean_dec_ref(v_toMonadExceptOf_2939_);
lean_dec(v___x_2938_);
lean_dec(v_inst_2937_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 1, v___x_3015_);
lean_ctor_set(v___x_2977_, 0, v___x_3043_);
v___x_3046_ = v___x_2977_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3015_);
v___x_3046_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
lean_object* v___x_3048_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v___x_3046_);
v___x_3048_ = v___x_2973_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_fst_2971_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3046_);
v___x_3048_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_3048_);
v___x_3050_ = v___x_2969_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_fst_2967_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3052_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_3050_);
v___x_3052_ = v___x_2965_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_fst_2963_);
lean_ctor_set(v_reuseFailAlloc_3058_, 1, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_3052_);
v___x_3054_ = v___x_2961_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_fst_2959_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
v___x_3056_ = lean_apply_2(v_toPure_2932_, lean_box(0), v___x_3055_);
v___y_2984_ = v___x_3056_;
goto v___jp_2983_;
}
}
}
}
}
}
else
{
lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3147_; 
lean_inc(v_stop_3039_);
lean_inc(v_start_3038_);
lean_inc_ref(v_array_3037_);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_fst_2971_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; lean_object* v_unused_3149_; lean_object* v_unused_3150_; 
v_unused_3148_ = lean_ctor_get(v_fst_2971_, 2);
lean_dec(v_unused_3148_);
v_unused_3149_ = lean_ctor_get(v_fst_2971_, 1);
lean_dec(v_unused_3149_);
v_unused_3150_ = lean_ctor_get(v_fst_2971_, 0);
lean_dec(v_unused_3150_);
v___x_3063_ = v_fst_2971_;
v_isShared_3064_ = v_isSharedCheck_3147_;
goto v_resetjp_3062_;
}
else
{
lean_dec(v_fst_2971_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3147_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v_array_3065_; lean_object* v_start_3066_; lean_object* v_stop_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3071_; 
v_array_3065_ = lean_ctor_get(v_fst_2967_, 0);
v_start_3066_ = lean_ctor_get(v_fst_2967_, 1);
v_stop_3067_ = lean_ctor_get(v_fst_2967_, 2);
v___x_3068_ = lean_array_fget(v_array_3037_, v_start_3038_);
v___x_3069_ = lean_nat_add(v_start_3038_, v___x_3012_);
lean_dec(v_start_3038_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 1, v___x_3069_);
v___x_3071_ = v___x_3063_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_array_3037_);
lean_ctor_set(v_reuseFailAlloc_3146_, 1, v___x_3069_);
lean_ctor_set(v_reuseFailAlloc_3146_, 2, v_stop_3039_);
v___x_3071_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
uint8_t v___x_3072_; 
v___x_3072_ = lean_nat_dec_lt(v_start_3066_, v_stop_3067_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3074_; 
lean_dec(v___x_3068_);
lean_dec(v___x_3040_);
lean_dec(v___x_3011_);
lean_dec(v_next_2948_);
lean_dec(v_numDiscrEqs_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec(v_fst_2944_);
lean_dec(v___f_2943_);
lean_dec(v_onAlt_2942_);
lean_dec_ref(v_toMonadExceptOf_2939_);
lean_dec(v___x_2938_);
lean_dec(v_inst_2937_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 1, v___x_3015_);
lean_ctor_set(v___x_2977_, 0, v___x_3043_);
v___x_3074_ = v___x_2977_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v___x_3015_);
v___x_3074_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3076_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v___x_3074_);
lean_ctor_set(v___x_2973_, 0, v___x_3071_);
v___x_3076_ = v___x_2973_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3078_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_3076_);
v___x_3078_ = v___x_2969_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_fst_2967_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3080_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_3078_);
v___x_3080_ = v___x_2965_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_fst_2963_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3082_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_3080_);
v___x_3082_ = v___x_2961_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_fst_2959_);
lean_ctor_set(v_reuseFailAlloc_3085_, 1, v___x_3080_);
v___x_3082_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
v___x_3084_ = lean_apply_2(v_toPure_2932_, lean_box(0), v___x_3083_);
v___y_2984_ = v___x_3084_;
goto v___jp_2983_;
}
}
}
}
}
}
else
{
lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3142_; 
lean_inc(v_stop_3067_);
lean_inc(v_start_3066_);
lean_inc_ref(v_array_3065_);
v_isSharedCheck_3142_ = !lean_is_exclusive(v_fst_2967_);
if (v_isSharedCheck_3142_ == 0)
{
lean_object* v_unused_3143_; lean_object* v_unused_3144_; lean_object* v_unused_3145_; 
v_unused_3143_ = lean_ctor_get(v_fst_2967_, 2);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v_fst_2967_, 1);
lean_dec(v_unused_3144_);
v_unused_3145_ = lean_ctor_get(v_fst_2967_, 0);
lean_dec(v_unused_3145_);
v___x_3091_ = v_fst_2967_;
v_isShared_3092_ = v_isSharedCheck_3142_;
goto v_resetjp_3090_;
}
else
{
lean_dec(v_fst_2967_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3142_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v_array_3093_; lean_object* v_start_3094_; lean_object* v_stop_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3099_; 
v_array_3093_ = lean_ctor_get(v_fst_2963_, 0);
v_start_3094_ = lean_ctor_get(v_fst_2963_, 1);
v_stop_3095_ = lean_ctor_get(v_fst_2963_, 2);
v___x_3096_ = lean_array_fget(v_array_3065_, v_start_3066_);
v___x_3097_ = lean_nat_add(v_start_3066_, v___x_3012_);
lean_dec(v_start_3066_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 1, v___x_3097_);
v___x_3099_ = v___x_3091_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_array_3065_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v___x_3097_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_stop_3067_);
v___x_3099_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_nat_dec_lt(v_start_3094_, v_stop_3095_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3102_; 
lean_dec(v___x_3096_);
lean_dec(v___x_3068_);
lean_dec(v___x_3040_);
lean_dec(v___x_3011_);
lean_dec(v_next_2948_);
lean_dec(v_numDiscrEqs_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec(v_fst_2944_);
lean_dec(v___f_2943_);
lean_dec(v_onAlt_2942_);
lean_dec_ref(v_toMonadExceptOf_2939_);
lean_dec(v___x_2938_);
lean_dec(v_inst_2937_);
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 1, v___x_3015_);
lean_ctor_set(v___x_2977_, 0, v___x_3043_);
v___x_3102_ = v___x_2977_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v___x_3015_);
v___x_3102_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3104_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 1, v___x_3102_);
lean_ctor_set(v___x_2973_, 0, v___x_3071_);
v___x_3104_ = v___x_2973_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3106_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 1, v___x_3104_);
lean_ctor_set(v___x_2969_, 0, v___x_3099_);
v___x_3106_ = v___x_2969_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3104_);
v___x_3106_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
lean_object* v___x_3108_; 
if (v_isShared_2966_ == 0)
{
lean_ctor_set(v___x_2965_, 1, v___x_3106_);
v___x_3108_ = v___x_2965_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_fst_2963_);
lean_ctor_set(v_reuseFailAlloc_3114_, 1, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_3108_);
v___x_3110_ = v___x_2961_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_fst_2959_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
v___x_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
v___x_3112_ = lean_apply_2(v_toPure_2932_, lean_box(0), v___x_3111_);
v___y_2984_ = v___x_3112_;
goto v___jp_2983_;
}
}
}
}
}
}
else
{
lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3137_; 
lean_inc(v_stop_3095_);
lean_inc(v_start_3094_);
lean_inc_ref(v_array_3093_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2973_);
lean_del_object(v___x_2969_);
lean_del_object(v___x_2965_);
lean_del_object(v___x_2961_);
v_isSharedCheck_3137_ = !lean_is_exclusive(v_fst_2963_);
if (v_isSharedCheck_3137_ == 0)
{
lean_object* v_unused_3138_; lean_object* v_unused_3139_; lean_object* v_unused_3140_; 
v_unused_3138_ = lean_ctor_get(v_fst_2963_, 2);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_fst_2963_, 1);
lean_dec(v_unused_3139_);
v_unused_3140_ = lean_ctor_get(v_fst_2963_, 0);
lean_dec(v_unused_3140_);
v___x_3119_ = v_fst_2963_;
v_isShared_3120_ = v_isSharedCheck_3137_;
goto v_resetjp_3118_;
}
else
{
lean_dec(v_fst_2963_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3137_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v_numOverlaps_3121_; uint8_t v___x_3122_; 
v_numOverlaps_3121_ = lean_ctor_get(v___x_3096_, 1);
v___x_3122_ = lean_nat_dec_eq(v_numOverlaps_3121_, v___x_2935_);
if (v___x_3122_ == 0)
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_del_object(v___x_3119_);
lean_dec_ref(v___x_3099_);
lean_dec(v___x_3096_);
lean_dec(v_stop_3095_);
lean_dec(v_start_3094_);
lean_dec_ref(v_array_3093_);
lean_dec_ref(v___x_3071_);
lean_dec(v___x_3068_);
lean_dec_ref(v___x_3043_);
lean_dec(v___x_3040_);
lean_dec_ref(v___x_3015_);
lean_dec(v___x_3011_);
lean_dec(v_fst_2959_);
lean_dec(v_next_2948_);
lean_dec(v_numDiscrEqs_2947_);
lean_dec_ref(v_inst_2946_);
lean_dec_ref(v_inst_2945_);
lean_dec(v_fst_2944_);
lean_dec(v___f_2943_);
lean_dec(v_onAlt_2942_);
lean_dec_ref(v_toMonadExceptOf_2939_);
lean_dec(v___x_2938_);
lean_dec(v_inst_2937_);
lean_dec(v_toPure_2932_);
v___x_3123_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_3124_ = l_panic___redArg(v___x_2936_, v___x_3123_);
v___y_2984_ = v___x_3124_;
goto v___jp_2983_;
}
else
{
lean_object* v___f_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
lean_inc(v_inst_2937_);
lean_inc_n(v_toPure_2932_, 2);
lean_inc(v___x_3068_);
v___f_3125_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_3125_, 0, v___x_3068_);
lean_closure_set(v___f_3125_, 1, v_toPure_2932_);
lean_closure_set(v___f_3125_, 2, v_inst_2937_);
v___x_3126_ = lean_array_fget_borrowed(v_array_3093_, v_start_3094_);
v___x_3127_ = lean_box(v___x_2940_);
v___x_3128_ = lean_box(v_useSplitter_2941_);
lean_inc(v___x_3096_);
lean_inc_ref(v_inst_2946_);
lean_inc_ref(v_inst_2945_);
lean_inc(v___x_3126_);
lean_inc(v_toBind_2933_);
v___f_3129_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 22, 20);
lean_closure_set(v___f_3129_, 0, v___x_3068_);
lean_closure_set(v___f_3129_, 1, v___x_2938_);
lean_closure_set(v___f_3129_, 2, v_toMonadExceptOf_2939_);
lean_closure_set(v___f_3129_, 3, v___x_3127_);
lean_closure_set(v___f_3129_, 4, v___x_3128_);
lean_closure_set(v___f_3129_, 5, v_inst_2937_);
lean_closure_set(v___f_3129_, 6, v_onAlt_2942_);
lean_closure_set(v___f_3129_, 7, v_next_2948_);
lean_closure_set(v___f_3129_, 8, v_toBind_2933_);
lean_closure_set(v___f_3129_, 9, v___x_3126_);
lean_closure_set(v___f_3129_, 10, v___f_2943_);
lean_closure_set(v___f_3129_, 11, v_fst_2944_);
lean_closure_set(v___f_3129_, 12, v_inst_2945_);
lean_closure_set(v___f_3129_, 13, v_inst_2946_);
lean_closure_set(v___f_3129_, 14, v_numDiscrEqs_2947_);
lean_closure_set(v___f_3129_, 15, v___f_3125_);
lean_closure_set(v___f_3129_, 16, v___x_3096_);
lean_closure_set(v___f_3129_, 17, v_toPure_2932_);
lean_closure_set(v___f_3129_, 18, v___x_3012_);
lean_closure_set(v___f_3129_, 19, v___x_3011_);
v___x_3130_ = lean_nat_add(v_start_3094_, v___x_3012_);
lean_dec(v_start_3094_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 1, v___x_3130_);
v___x_3132_ = v___x_3119_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_array_3093_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v___x_3130_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_stop_3095_);
v___x_3132_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___f_3133_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3133_, 0, v_fst_2959_);
lean_closure_set(v___f_3133_, 1, v___x_3043_);
lean_closure_set(v___f_3133_, 2, v___x_3015_);
lean_closure_set(v___f_3133_, 3, v___x_3071_);
lean_closure_set(v___f_3133_, 4, v___x_3099_);
lean_closure_set(v___f_3133_, 5, v___x_3132_);
lean_closure_set(v___f_3133_, 6, v_toPure_2932_);
v___x_3134_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2946_, v_inst_2945_, v___x_3040_, v___x_3096_, v___f_3129_);
lean_inc(v_toBind_2933_);
v___x_3135_ = lean_apply_4(v_toBind_2933_, lean_box(0), lean_box(0), v___x_3134_, v___f_3133_);
v___y_2984_ = v___x_3135_;
goto v___jp_2983_;
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
}
}
v___jp_2983_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_inc(v_toBind_2933_);
v___x_2985_ = lean_apply_4(v_toBind_2933_, lean_box(0), lean_box(0), v___y_2984_, v___f_2934_);
v___x_2986_ = lean_apply_4(v_toBind_2933_, lean_box(0), lean_box(0), v___x_2985_, v___f_2982_);
return v___x_2986_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__46_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2931_ = stack[0].m_obj;
lean_object* v_toPure_2932_ = stack[1].m_obj;
lean_object* v_toBind_2933_ = stack[2].m_obj;
lean_object* v___f_2934_ = stack[3].m_obj;
lean_object* v___x_2935_ = stack[4].m_obj;
lean_object* v___x_2936_ = stack[5].m_obj;
lean_object* v_inst_2937_ = stack[6].m_obj;
lean_object* v___x_2938_ = stack[7].m_obj;
lean_object* v_toMonadExceptOf_2939_ = stack[8].m_obj;
uint8_t v___x_2940_ = stack[9].m_num;
uint8_t v_useSplitter_2941_ = stack[10].m_num;
lean_object* v_onAlt_2942_ = stack[11].m_obj;
lean_object* v___f_2943_ = stack[12].m_obj;
lean_object* v_fst_2944_ = stack[13].m_obj;
lean_object* v_inst_2945_ = stack[14].m_obj;
lean_object* v_inst_2946_ = stack[15].m_obj;
lean_object* v_numDiscrEqs_2947_ = stack[16].m_obj;
lean_object* v_next_2948_ = stack[17].m_obj;
lean_object* v_acc_2949_ = stack[18].m_obj;
lean_object* v_G_2951_ = stack[20].m_obj;
lean_object* v_res_3171_;
v_res_3171_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_2931_, v_toPure_2932_, v_toBind_2933_, v___f_2934_, v___x_2935_, v___x_2936_, v_inst_2937_, v___x_2938_, v_toMonadExceptOf_2939_, v___x_2940_, v_useSplitter_2941_, v_onAlt_2942_, v___f_2943_, v_fst_2944_, v_inst_2945_, v_inst_2946_, v_numDiscrEqs_2947_, v_next_2948_, v_acc_2949_, lean_box(0), v_G_2951_);
stack->m_obj
 = v_res_3171_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object** _args){
lean_object* v___x_3172_ = _args[0];
lean_object* v_toPure_3173_ = _args[1];
lean_object* v_toBind_3174_ = _args[2];
lean_object* v___f_3175_ = _args[3];
lean_object* v___x_3176_ = _args[4];
lean_object* v___x_3177_ = _args[5];
lean_object* v_inst_3178_ = _args[6];
lean_object* v___x_3179_ = _args[7];
lean_object* v_toMonadExceptOf_3180_ = _args[8];
lean_object* v___x_3181_ = _args[9];
lean_object* v_useSplitter_3182_ = _args[10];
lean_object* v_onAlt_3183_ = _args[11];
lean_object* v___f_3184_ = _args[12];
lean_object* v_fst_3185_ = _args[13];
lean_object* v_inst_3186_ = _args[14];
lean_object* v_inst_3187_ = _args[15];
lean_object* v_numDiscrEqs_3188_ = _args[16];
lean_object* v_next_3189_ = _args[17];
lean_object* v_acc_3190_ = _args[18];
lean_object* v_h_3191_ = _args[19];
lean_object* v_G_3192_ = _args[20];
_start:
{
uint8_t v___x_14567__boxed_3193_; uint8_t v_useSplitter_boxed_3194_; lean_object* v_res_3195_; 
v___x_14567__boxed_3193_ = lean_unbox(v___x_3181_);
v_useSplitter_boxed_3194_ = lean_unbox(v_useSplitter_3182_);
v_res_3195_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3172_, v_toPure_3173_, v_toBind_3174_, v___f_3175_, v___x_3176_, v___x_3177_, v_inst_3178_, v___x_3179_, v_toMonadExceptOf_3180_, v___x_14567__boxed_3193_, v_useSplitter_boxed_3194_, v_onAlt_3183_, v___f_3184_, v_fst_3185_, v_inst_3186_, v_inst_3187_, v_numDiscrEqs_3188_, v_next_3189_, v_acc_3190_, v_h_3191_, v_G_3192_);
lean_dec(v___x_3177_);
lean_dec(v___x_3176_);
lean_dec(v___x_3172_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3196_, lean_object* v_numParams_3197_, lean_object* v_numDiscrs_3198_, lean_object* v_altInfos_3199_, lean_object* v_uElimPos_x3f_3200_, lean_object* v_snd_3201_, lean_object* v_overlaps_3202_, lean_object* v_splitterName_3203_, lean_object* v_matcherLevels_3204_, lean_object* v_params_x27_3205_, lean_object* v_fst_3206_, lean_object* v_discrs_x27_3207_, lean_object* v_fst_3208_, lean_object* v_toPure_3209_, lean_object* v_____do__lift_3210_){
_start:
{
lean_object* v_remaining_x27_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_remaining_x27_3211_ = l_Array_append___redArg(v_fst_3196_, v_____do__lift_3210_);
v___x_3212_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3212_, 0, v_numParams_3197_);
lean_ctor_set(v___x_3212_, 1, v_numDiscrs_3198_);
lean_ctor_set(v___x_3212_, 2, v_altInfos_3199_);
lean_ctor_set(v___x_3212_, 3, v_uElimPos_x3f_3200_);
lean_ctor_set(v___x_3212_, 4, v_snd_3201_);
lean_ctor_set(v___x_3212_, 5, v_overlaps_3202_);
v___x_3213_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v_splitterName_3203_);
lean_ctor_set(v___x_3213_, 2, v_matcherLevels_3204_);
lean_ctor_set(v___x_3213_, 3, v_params_x27_3205_);
lean_ctor_set(v___x_3213_, 4, v_fst_3206_);
lean_ctor_set(v___x_3213_, 5, v_discrs_x27_3207_);
lean_ctor_set(v___x_3213_, 6, v_fst_3208_);
lean_ctor_set(v___x_3213_, 7, v_remaining_x27_3211_);
v___x_3214_ = lean_apply_2(v_toPure_3209_, lean_box(0), v___x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3215_, lean_object* v_numParams_3216_, lean_object* v_numDiscrs_3217_, lean_object* v_altInfos_3218_, lean_object* v_uElimPos_x3f_3219_, lean_object* v_snd_3220_, lean_object* v_overlaps_3221_, lean_object* v_splitterName_3222_, lean_object* v_matcherLevels_3223_, lean_object* v_params_x27_3224_, lean_object* v_fst_3225_, lean_object* v_discrs_x27_3226_, lean_object* v_fst_3227_, lean_object* v_toPure_3228_, lean_object* v_____do__lift_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3215_, v_numParams_3216_, v_numDiscrs_3217_, v_altInfos_3218_, v_uElimPos_x3f_3219_, v_snd_3220_, v_overlaps_3221_, v_splitterName_3222_, v_matcherLevels_3223_, v_params_x27_3224_, v_fst_3225_, v_discrs_x27_3226_, v_fst_3227_, v_toPure_3228_, v_____do__lift_3229_);
lean_dec_ref(v_____do__lift_3229_);
return v_res_3230_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3231_, lean_object* v_numParams_3232_, lean_object* v_numDiscrs_3233_, lean_object* v_altInfos_3234_, lean_object* v_uElimPos_x3f_3235_, lean_object* v_snd_3236_, lean_object* v_overlaps_3237_, lean_object* v_splitterName_3238_, lean_object* v_matcherLevels_3239_, lean_object* v_params_x27_3240_, lean_object* v_fst_3241_, lean_object* v_discrs_x27_3242_, lean_object* v_toPure_3243_, lean_object* v_onRemaining_3244_, lean_object* v_remaining_3245_, lean_object* v_toBind_3246_, lean_object* v_____s_3247_){
_start:
{
lean_object* v_fst_3248_; lean_object* v___f_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_fst_3248_ = lean_ctor_get(v_____s_3247_, 0);
lean_inc(v_fst_3248_);
lean_dec_ref(v_____s_3247_);
v___f_3249_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3249_, 0, v_fst_3231_);
lean_closure_set(v___f_3249_, 1, v_numParams_3232_);
lean_closure_set(v___f_3249_, 2, v_numDiscrs_3233_);
lean_closure_set(v___f_3249_, 3, v_altInfos_3234_);
lean_closure_set(v___f_3249_, 4, v_uElimPos_x3f_3235_);
lean_closure_set(v___f_3249_, 5, v_snd_3236_);
lean_closure_set(v___f_3249_, 6, v_overlaps_3237_);
lean_closure_set(v___f_3249_, 7, v_splitterName_3238_);
lean_closure_set(v___f_3249_, 8, v_matcherLevels_3239_);
lean_closure_set(v___f_3249_, 9, v_params_x27_3240_);
lean_closure_set(v___f_3249_, 10, v_fst_3241_);
lean_closure_set(v___f_3249_, 11, v_discrs_x27_3242_);
lean_closure_set(v___f_3249_, 12, v_fst_3248_);
lean_closure_set(v___f_3249_, 13, v_toPure_3243_);
v___x_3250_ = lean_apply_1(v_onRemaining_3244_, v_remaining_3245_);
v___x_3251_ = lean_apply_4(v_toBind_3246_, lean_box(0), lean_box(0), v___x_3250_, v___f_3249_);
return v___x_3251_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__48_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_3231_ = stack[0].m_obj;
lean_object* v_numParams_3232_ = stack[1].m_obj;
lean_object* v_numDiscrs_3233_ = stack[2].m_obj;
lean_object* v_altInfos_3234_ = stack[3].m_obj;
lean_object* v_uElimPos_x3f_3235_ = stack[4].m_obj;
lean_object* v_snd_3236_ = stack[5].m_obj;
lean_object* v_overlaps_3237_ = stack[6].m_obj;
lean_object* v_splitterName_3238_ = stack[7].m_obj;
lean_object* v_matcherLevels_3239_ = stack[8].m_obj;
lean_object* v_params_x27_3240_ = stack[9].m_obj;
lean_object* v_fst_3241_ = stack[10].m_obj;
lean_object* v_discrs_x27_3242_ = stack[11].m_obj;
lean_object* v_toPure_3243_ = stack[12].m_obj;
lean_object* v_onRemaining_3244_ = stack[13].m_obj;
lean_object* v_remaining_3245_ = stack[14].m_obj;
lean_object* v_toBind_3246_ = stack[15].m_obj;
lean_object* v_____s_3247_ = stack[16].m_obj;
lean_object* v_res_3252_;
v_res_3252_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3231_, v_numParams_3232_, v_numDiscrs_3233_, v_altInfos_3234_, v_uElimPos_x3f_3235_, v_snd_3236_, v_overlaps_3237_, v_splitterName_3238_, v_matcherLevels_3239_, v_params_x27_3240_, v_fst_3241_, v_discrs_x27_3242_, v_toPure_3243_, v_onRemaining_3244_, v_remaining_3245_, v_toBind_3246_, v_____s_3247_);
stack->m_obj
 = v_res_3252_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3253_ = _args[0];
lean_object* v_numParams_3254_ = _args[1];
lean_object* v_numDiscrs_3255_ = _args[2];
lean_object* v_altInfos_3256_ = _args[3];
lean_object* v_uElimPos_x3f_3257_ = _args[4];
lean_object* v_snd_3258_ = _args[5];
lean_object* v_overlaps_3259_ = _args[6];
lean_object* v_splitterName_3260_ = _args[7];
lean_object* v_matcherLevels_3261_ = _args[8];
lean_object* v_params_x27_3262_ = _args[9];
lean_object* v_fst_3263_ = _args[10];
lean_object* v_discrs_x27_3264_ = _args[11];
lean_object* v_toPure_3265_ = _args[12];
lean_object* v_onRemaining_3266_ = _args[13];
lean_object* v_remaining_3267_ = _args[14];
lean_object* v_toBind_3268_ = _args[15];
lean_object* v_____s_3269_ = _args[16];
_start:
{
lean_object* v_res_3270_; 
v_res_3270_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3253_, v_numParams_3254_, v_numDiscrs_3255_, v_altInfos_3256_, v_uElimPos_x3f_3257_, v_snd_3258_, v_overlaps_3259_, v_splitterName_3260_, v_matcherLevels_3261_, v_params_x27_3262_, v_fst_3263_, v_discrs_x27_3264_, v_toPure_3265_, v_onRemaining_3266_, v_remaining_3267_, v_toBind_3268_, v_____s_3269_);
return v_res_3270_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3271_, lean_object* v_fst_3272_, lean_object* v_numParams_3273_, lean_object* v_numDiscrs_3274_, lean_object* v_altInfos_3275_, lean_object* v_uElimPos_x3f_3276_, lean_object* v_snd_3277_, lean_object* v_overlaps_3278_, lean_object* v_splitterName_3279_, lean_object* v_matcherLevels_3280_, lean_object* v_params_x27_3281_, lean_object* v_fst_3282_, lean_object* v_discrs_x27_3283_, lean_object* v_toPure_3284_, lean_object* v_onRemaining_3285_, lean_object* v_remaining_3286_, lean_object* v_toBind_3287_, lean_object* v_origAltTypes_3288_, lean_object* v_alts_3289_, lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v_remaining_x27_3292_, lean_object* v___f_3293_, lean_object* v_altTypes_3294_){
_start:
{
lean_object* v_altInfos_3295_; lean_object* v___f_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_altInfos_3295_ = lean_ctor_get(v_splitterMatchInfo_3271_, 2);
lean_inc_ref(v_altInfos_3295_);
lean_dec_ref(v_splitterMatchInfo_3271_);
lean_inc(v_toBind_3287_);
lean_inc_ref(v_altInfos_3275_);
v___f_3296_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3296_, 0, v_fst_3272_);
lean_closure_set(v___f_3296_, 1, v_numParams_3273_);
lean_closure_set(v___f_3296_, 2, v_numDiscrs_3274_);
lean_closure_set(v___f_3296_, 3, v_altInfos_3275_);
lean_closure_set(v___f_3296_, 4, v_uElimPos_x3f_3276_);
lean_closure_set(v___f_3296_, 5, v_snd_3277_);
lean_closure_set(v___f_3296_, 6, v_overlaps_3278_);
lean_closure_set(v___f_3296_, 7, v_splitterName_3279_);
lean_closure_set(v___f_3296_, 8, v_matcherLevels_3280_);
lean_closure_set(v___f_3296_, 9, v_params_x27_3281_);
lean_closure_set(v___f_3296_, 10, v_fst_3282_);
lean_closure_set(v___f_3296_, 11, v_discrs_x27_3283_);
lean_closure_set(v___f_3296_, 12, v_toPure_3284_);
lean_closure_set(v___f_3296_, 13, v_onRemaining_3285_);
lean_closure_set(v___f_3296_, 14, v_remaining_3286_);
lean_closure_set(v___f_3296_, 15, v_toBind_3287_);
v___x_3297_ = lean_array_get_size(v_altInfos_3275_);
v___x_3298_ = lean_array_get_size(v_altInfos_3295_);
v___x_3299_ = lean_array_get_size(v_origAltTypes_3288_);
v___x_3300_ = lean_array_get_size(v_altTypes_3294_);
lean_inc_n(v___x_3290_, 5);
v___x_3301_ = l_Array_toSubarray___redArg(v_alts_3289_, v___x_3290_, v___x_3291_);
v___x_3302_ = l_Array_toSubarray___redArg(v_altInfos_3275_, v___x_3290_, v___x_3297_);
v___x_3303_ = l_Array_toSubarray___redArg(v_altInfos_3295_, v___x_3290_, v___x_3298_);
v___x_3304_ = l_Array_toSubarray___redArg(v_origAltTypes_3288_, v___x_3290_, v___x_3299_);
v___x_3305_ = l_Array_toSubarray___redArg(v_altTypes_3294_, v___x_3290_, v___x_3300_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3304_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3303_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3302_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3301_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3310_, 0, v_remaining_x27_3292_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3293_, v___x_3290_, v___x_3310_, lean_box(0));
v___x_3312_ = lean_apply_4(v_toBind_3287_, lean_box(0), lean_box(0), v___x_3311_, v___f_3296_);
return v___x_3312_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__49_0interp(lean_interpreter_value* stack)
{
lean_object* v_splitterMatchInfo_3271_ = stack[0].m_obj;
lean_object* v_fst_3272_ = stack[1].m_obj;
lean_object* v_numParams_3273_ = stack[2].m_obj;
lean_object* v_numDiscrs_3274_ = stack[3].m_obj;
lean_object* v_altInfos_3275_ = stack[4].m_obj;
lean_object* v_uElimPos_x3f_3276_ = stack[5].m_obj;
lean_object* v_snd_3277_ = stack[6].m_obj;
lean_object* v_overlaps_3278_ = stack[7].m_obj;
lean_object* v_splitterName_3279_ = stack[8].m_obj;
lean_object* v_matcherLevels_3280_ = stack[9].m_obj;
lean_object* v_params_x27_3281_ = stack[10].m_obj;
lean_object* v_fst_3282_ = stack[11].m_obj;
lean_object* v_discrs_x27_3283_ = stack[12].m_obj;
lean_object* v_toPure_3284_ = stack[13].m_obj;
lean_object* v_onRemaining_3285_ = stack[14].m_obj;
lean_object* v_remaining_3286_ = stack[15].m_obj;
lean_object* v_toBind_3287_ = stack[16].m_obj;
lean_object* v_origAltTypes_3288_ = stack[17].m_obj;
lean_object* v_alts_3289_ = stack[18].m_obj;
lean_object* v___x_3290_ = stack[19].m_obj;
lean_object* v___x_3291_ = stack[20].m_obj;
lean_object* v_remaining_x27_3292_ = stack[21].m_obj;
lean_object* v___f_3293_ = stack[22].m_obj;
lean_object* v_altTypes_3294_ = stack[23].m_obj;
lean_object* v_res_3313_;
v_res_3313_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3271_, v_fst_3272_, v_numParams_3273_, v_numDiscrs_3274_, v_altInfos_3275_, v_uElimPos_x3f_3276_, v_snd_3277_, v_overlaps_3278_, v_splitterName_3279_, v_matcherLevels_3280_, v_params_x27_3281_, v_fst_3282_, v_discrs_x27_3283_, v_toPure_3284_, v_onRemaining_3285_, v_remaining_3286_, v_toBind_3287_, v_origAltTypes_3288_, v_alts_3289_, v___x_3290_, v___x_3291_, v_remaining_x27_3292_, v___f_3293_, v_altTypes_3294_);
stack->m_obj
 = v_res_3313_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3314_ = _args[0];
lean_object* v_fst_3315_ = _args[1];
lean_object* v_numParams_3316_ = _args[2];
lean_object* v_numDiscrs_3317_ = _args[3];
lean_object* v_altInfos_3318_ = _args[4];
lean_object* v_uElimPos_x3f_3319_ = _args[5];
lean_object* v_snd_3320_ = _args[6];
lean_object* v_overlaps_3321_ = _args[7];
lean_object* v_splitterName_3322_ = _args[8];
lean_object* v_matcherLevels_3323_ = _args[9];
lean_object* v_params_x27_3324_ = _args[10];
lean_object* v_fst_3325_ = _args[11];
lean_object* v_discrs_x27_3326_ = _args[12];
lean_object* v_toPure_3327_ = _args[13];
lean_object* v_onRemaining_3328_ = _args[14];
lean_object* v_remaining_3329_ = _args[15];
lean_object* v_toBind_3330_ = _args[16];
lean_object* v_origAltTypes_3331_ = _args[17];
lean_object* v_alts_3332_ = _args[18];
lean_object* v___x_3333_ = _args[19];
lean_object* v___x_3334_ = _args[20];
lean_object* v_remaining_x27_3335_ = _args[21];
lean_object* v___f_3336_ = _args[22];
lean_object* v_altTypes_3337_ = _args[23];
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3314_, v_fst_3315_, v_numParams_3316_, v_numDiscrs_3317_, v_altInfos_3318_, v_uElimPos_x3f_3319_, v_snd_3320_, v_overlaps_3321_, v_splitterName_3322_, v_matcherLevels_3323_, v_params_x27_3324_, v_fst_3325_, v_discrs_x27_3326_, v_toPure_3327_, v_onRemaining_3328_, v_remaining_3329_, v_toBind_3330_, v_origAltTypes_3331_, v_alts_3332_, v___x_3333_, v___x_3334_, v_remaining_x27_3335_, v___f_3336_, v_altTypes_3337_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3339_, lean_object* v_aux2_3340_, lean_object* v_inst_3341_, lean_object* v_toBind_3342_, lean_object* v___f_3343_, lean_object* v_____r_3344_){
_start:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3345_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3345_, 0, v___x_3339_);
lean_closure_set(v___x_3345_, 1, v_aux2_3340_);
v___x_3346_ = lean_apply_2(v_inst_3341_, lean_box(0), v___x_3345_);
v___x_3347_ = lean_apply_4(v_toBind_3342_, lean_box(0), lean_box(0), v___x_3346_, v___f_3343_);
return v___x_3347_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3350_ = l_Lean_stringToMessageData(v___x_3349_);
return v___x_3350_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3351_, lean_object* v_params_x27_3352_, lean_object* v_fst_3353_, lean_object* v_discrs_x27_3354_, lean_object* v_fst_3355_, lean_object* v_numParams_3356_, lean_object* v_numDiscrs_3357_, lean_object* v_altInfos_3358_, lean_object* v_uElimPos_x3f_3359_, lean_object* v_snd_3360_, lean_object* v_overlaps_3361_, lean_object* v_matcherLevels_3362_, lean_object* v_toPure_3363_, lean_object* v_onRemaining_3364_, lean_object* v_remaining_3365_, lean_object* v_toBind_3366_, lean_object* v_origAltTypes_3367_, lean_object* v_alts_3368_, lean_object* v___x_3369_, lean_object* v___x_3370_, lean_object* v_remaining_x27_3371_, lean_object* v___f_3372_, lean_object* v_inst_3373_, lean_object* v___x_3374_, uint8_t v___x_3375_, lean_object* v_liftWith_3376_, lean_object* v_restoreM_3377_, lean_object* v_matchEqns_3378_){
_start:
{
lean_object* v_splitterName_3379_; lean_object* v_splitterMatchInfo_3380_; lean_object* v___x_3381_; lean_object* v_aux2_3382_; lean_object* v_aux2_3383_; lean_object* v_aux2_3384_; lean_object* v___x_3385_; lean_object* v___f_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___f_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___f_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v_splitterName_3379_ = lean_ctor_get(v_matchEqns_3378_, 1);
lean_inc_n(v_splitterName_3379_, 2);
v_splitterMatchInfo_3380_ = lean_ctor_get(v_matchEqns_3378_, 2);
lean_inc_ref(v_splitterMatchInfo_3380_);
lean_dec_ref(v_matchEqns_3378_);
v___x_3381_ = l_Lean_mkConst(v_splitterName_3379_, v___x_3351_);
v_aux2_3382_ = l_Lean_mkAppN(v___x_3381_, v_params_x27_3352_);
lean_inc_ref(v_fst_3353_);
v_aux2_3383_ = l_Lean_Expr_app___override(v_aux2_3382_, v_fst_3353_);
v_aux2_3384_ = l_Lean_mkAppN(v_aux2_3383_, v_discrs_x27_3354_);
lean_inc_ref_n(v_aux2_3384_, 2);
v___x_3385_ = l_Lean_indentExpr(v_aux2_3384_);
lean_inc(v___x_3370_);
lean_inc_n(v_toBind_3366_, 3);
v___f_3386_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3386_, 0, v_splitterMatchInfo_3380_);
lean_closure_set(v___f_3386_, 1, v_fst_3355_);
lean_closure_set(v___f_3386_, 2, v_numParams_3356_);
lean_closure_set(v___f_3386_, 3, v_numDiscrs_3357_);
lean_closure_set(v___f_3386_, 4, v_altInfos_3358_);
lean_closure_set(v___f_3386_, 5, v_uElimPos_x3f_3359_);
lean_closure_set(v___f_3386_, 6, v_snd_3360_);
lean_closure_set(v___f_3386_, 7, v_overlaps_3361_);
lean_closure_set(v___f_3386_, 8, v_splitterName_3379_);
lean_closure_set(v___f_3386_, 9, v_matcherLevels_3362_);
lean_closure_set(v___f_3386_, 10, v_params_x27_3352_);
lean_closure_set(v___f_3386_, 11, v_fst_3353_);
lean_closure_set(v___f_3386_, 12, v_discrs_x27_3354_);
lean_closure_set(v___f_3386_, 13, v_toPure_3363_);
lean_closure_set(v___f_3386_, 14, v_onRemaining_3364_);
lean_closure_set(v___f_3386_, 15, v_remaining_3365_);
lean_closure_set(v___f_3386_, 16, v_toBind_3366_);
lean_closure_set(v___f_3386_, 17, v_origAltTypes_3367_);
lean_closure_set(v___f_3386_, 18, v_alts_3368_);
lean_closure_set(v___f_3386_, 19, v___x_3369_);
lean_closure_set(v___f_3386_, 20, v___x_3370_);
lean_closure_set(v___f_3386_, 21, v_remaining_x27_3371_);
lean_closure_set(v___f_3386_, 22, v___f_3372_);
lean_inc(v_inst_3373_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3387_, 0, v___x_3370_);
lean_closure_set(v___f_3387_, 1, v_aux2_3384_);
lean_closure_set(v___f_3387_, 2, v_inst_3373_);
lean_closure_set(v___f_3387_, 3, v_toBind_3366_);
lean_closure_set(v___f_3387_, 4, v___f_3386_);
v___x_3388_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___x_3385_);
v___x_3390_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___x_3374_);
v___f_3391_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3391_, 0, v___x_3390_);
v___x_3392_ = lean_box(v___x_3375_);
v___x_3393_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3393_, 0, v_aux2_3384_);
lean_closure_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_apply_2(v_inst_3373_, lean_box(0), v___x_3393_);
v___f_3395_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3395_, 0, v___x_3394_);
lean_closure_set(v___f_3395_, 1, v___f_3391_);
v___x_3396_ = lean_apply_2(v_liftWith_3376_, lean_box(0), v___f_3395_);
v___x_3397_ = lean_apply_1(v_restoreM_3377_, lean_box(0));
v___x_3398_ = lean_apply_4(v_toBind_3366_, lean_box(0), lean_box(0), v___x_3396_, v___x_3397_);
v___x_3399_ = lean_apply_4(v_toBind_3366_, lean_box(0), lean_box(0), v___x_3398_, v___f_3387_);
return v___x_3399_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__53_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3351_ = stack[0].m_obj;
lean_object* v_params_x27_3352_ = stack[1].m_obj;
lean_object* v_fst_3353_ = stack[2].m_obj;
lean_object* v_discrs_x27_3354_ = stack[3].m_obj;
lean_object* v_fst_3355_ = stack[4].m_obj;
lean_object* v_numParams_3356_ = stack[5].m_obj;
lean_object* v_numDiscrs_3357_ = stack[6].m_obj;
lean_object* v_altInfos_3358_ = stack[7].m_obj;
lean_object* v_uElimPos_x3f_3359_ = stack[8].m_obj;
lean_object* v_snd_3360_ = stack[9].m_obj;
lean_object* v_overlaps_3361_ = stack[10].m_obj;
lean_object* v_matcherLevels_3362_ = stack[11].m_obj;
lean_object* v_toPure_3363_ = stack[12].m_obj;
lean_object* v_onRemaining_3364_ = stack[13].m_obj;
lean_object* v_remaining_3365_ = stack[14].m_obj;
lean_object* v_toBind_3366_ = stack[15].m_obj;
lean_object* v_origAltTypes_3367_ = stack[16].m_obj;
lean_object* v_alts_3368_ = stack[17].m_obj;
lean_object* v___x_3369_ = stack[18].m_obj;
lean_object* v___x_3370_ = stack[19].m_obj;
lean_object* v_remaining_x27_3371_ = stack[20].m_obj;
lean_object* v___f_3372_ = stack[21].m_obj;
lean_object* v_inst_3373_ = stack[22].m_obj;
lean_object* v___x_3374_ = stack[23].m_obj;
uint8_t v___x_3375_ = stack[24].m_num;
lean_object* v_liftWith_3376_ = stack[25].m_obj;
lean_object* v_restoreM_3377_ = stack[26].m_obj;
lean_object* v_matchEqns_3378_ = stack[27].m_obj;
lean_object* v_res_3400_;
v_res_3400_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3351_, v_params_x27_3352_, v_fst_3353_, v_discrs_x27_3354_, v_fst_3355_, v_numParams_3356_, v_numDiscrs_3357_, v_altInfos_3358_, v_uElimPos_x3f_3359_, v_snd_3360_, v_overlaps_3361_, v_matcherLevels_3362_, v_toPure_3363_, v_onRemaining_3364_, v_remaining_3365_, v_toBind_3366_, v_origAltTypes_3367_, v_alts_3368_, v___x_3369_, v___x_3370_, v_remaining_x27_3371_, v___f_3372_, v_inst_3373_, v___x_3374_, v___x_3375_, v_liftWith_3376_, v_restoreM_3377_, v_matchEqns_3378_);
stack->m_obj
 = v_res_3400_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3401_ = _args[0];
lean_object* v_params_x27_3402_ = _args[1];
lean_object* v_fst_3403_ = _args[2];
lean_object* v_discrs_x27_3404_ = _args[3];
lean_object* v_fst_3405_ = _args[4];
lean_object* v_numParams_3406_ = _args[5];
lean_object* v_numDiscrs_3407_ = _args[6];
lean_object* v_altInfos_3408_ = _args[7];
lean_object* v_uElimPos_x3f_3409_ = _args[8];
lean_object* v_snd_3410_ = _args[9];
lean_object* v_overlaps_3411_ = _args[10];
lean_object* v_matcherLevels_3412_ = _args[11];
lean_object* v_toPure_3413_ = _args[12];
lean_object* v_onRemaining_3414_ = _args[13];
lean_object* v_remaining_3415_ = _args[14];
lean_object* v_toBind_3416_ = _args[15];
lean_object* v_origAltTypes_3417_ = _args[16];
lean_object* v_alts_3418_ = _args[17];
lean_object* v___x_3419_ = _args[18];
lean_object* v___x_3420_ = _args[19];
lean_object* v_remaining_x27_3421_ = _args[20];
lean_object* v___f_3422_ = _args[21];
lean_object* v_inst_3423_ = _args[22];
lean_object* v___x_3424_ = _args[23];
lean_object* v___x_3425_ = _args[24];
lean_object* v_liftWith_3426_ = _args[25];
lean_object* v_restoreM_3427_ = _args[26];
lean_object* v_matchEqns_3428_ = _args[27];
_start:
{
uint8_t v___x_15363__boxed_3429_; lean_object* v_res_3430_; 
v___x_15363__boxed_3429_ = lean_unbox(v___x_3425_);
v_res_3430_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3401_, v_params_x27_3402_, v_fst_3403_, v_discrs_x27_3404_, v_fst_3405_, v_numParams_3406_, v_numDiscrs_3407_, v_altInfos_3408_, v_uElimPos_x3f_3409_, v_snd_3410_, v_overlaps_3411_, v_matcherLevels_3412_, v_toPure_3413_, v_onRemaining_3414_, v_remaining_3415_, v_toBind_3416_, v_origAltTypes_3417_, v_alts_3418_, v___x_3419_, v___x_3420_, v_remaining_x27_3421_, v___f_3422_, v_inst_3423_, v___x_3424_, v___x_15363__boxed_3429_, v_liftWith_3426_, v_restoreM_3427_, v_matchEqns_3428_);
return v_res_3430_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3431_, lean_object* v_params_x27_3432_, lean_object* v_fst_3433_, lean_object* v_discrs_x27_3434_, lean_object* v_fst_3435_, lean_object* v_numParams_3436_, lean_object* v_numDiscrs_3437_, lean_object* v_altInfos_3438_, lean_object* v_uElimPos_x3f_3439_, lean_object* v_snd_3440_, lean_object* v_overlaps_3441_, lean_object* v_matcherLevels_3442_, lean_object* v_toPure_3443_, lean_object* v_onRemaining_3444_, lean_object* v_remaining_3445_, lean_object* v_toBind_3446_, lean_object* v_alts_3447_, lean_object* v___x_3448_, lean_object* v___x_3449_, lean_object* v_remaining_x27_3450_, lean_object* v___f_3451_, lean_object* v_inst_3452_, lean_object* v___x_3453_, uint8_t v___x_3454_, lean_object* v_liftWith_3455_, lean_object* v_restoreM_3456_, lean_object* v_matcherName_3457_, lean_object* v_origAltTypes_3458_){
_start:
{
lean_object* v___x_3459_; lean_object* v___f_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3459_ = lean_box(v___x_3454_);
lean_inc(v_inst_3452_);
lean_inc(v_toBind_3446_);
v___f_3460_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3460_, 0, v___x_3431_);
lean_closure_set(v___f_3460_, 1, v_params_x27_3432_);
lean_closure_set(v___f_3460_, 2, v_fst_3433_);
lean_closure_set(v___f_3460_, 3, v_discrs_x27_3434_);
lean_closure_set(v___f_3460_, 4, v_fst_3435_);
lean_closure_set(v___f_3460_, 5, v_numParams_3436_);
lean_closure_set(v___f_3460_, 6, v_numDiscrs_3437_);
lean_closure_set(v___f_3460_, 7, v_altInfos_3438_);
lean_closure_set(v___f_3460_, 8, v_uElimPos_x3f_3439_);
lean_closure_set(v___f_3460_, 9, v_snd_3440_);
lean_closure_set(v___f_3460_, 10, v_overlaps_3441_);
lean_closure_set(v___f_3460_, 11, v_matcherLevels_3442_);
lean_closure_set(v___f_3460_, 12, v_toPure_3443_);
lean_closure_set(v___f_3460_, 13, v_onRemaining_3444_);
lean_closure_set(v___f_3460_, 14, v_remaining_3445_);
lean_closure_set(v___f_3460_, 15, v_toBind_3446_);
lean_closure_set(v___f_3460_, 16, v_origAltTypes_3458_);
lean_closure_set(v___f_3460_, 17, v_alts_3447_);
lean_closure_set(v___f_3460_, 18, v___x_3448_);
lean_closure_set(v___f_3460_, 19, v___x_3449_);
lean_closure_set(v___f_3460_, 20, v_remaining_x27_3450_);
lean_closure_set(v___f_3460_, 21, v___f_3451_);
lean_closure_set(v___f_3460_, 22, v_inst_3452_);
lean_closure_set(v___f_3460_, 23, v___x_3453_);
lean_closure_set(v___f_3460_, 24, v___x_3459_);
lean_closure_set(v___f_3460_, 25, v_liftWith_3455_);
lean_closure_set(v___f_3460_, 26, v_restoreM_3456_);
v___x_3461_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3461_, 0, v_matcherName_3457_);
v___x_3462_ = lean_apply_2(v_inst_3452_, lean_box(0), v___x_3461_);
v___x_3463_ = lean_apply_4(v_toBind_3446_, lean_box(0), lean_box(0), v___x_3462_, v___f_3460_);
return v___x_3463_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__51_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3431_ = stack[0].m_obj;
lean_object* v_params_x27_3432_ = stack[1].m_obj;
lean_object* v_fst_3433_ = stack[2].m_obj;
lean_object* v_discrs_x27_3434_ = stack[3].m_obj;
lean_object* v_fst_3435_ = stack[4].m_obj;
lean_object* v_numParams_3436_ = stack[5].m_obj;
lean_object* v_numDiscrs_3437_ = stack[6].m_obj;
lean_object* v_altInfos_3438_ = stack[7].m_obj;
lean_object* v_uElimPos_x3f_3439_ = stack[8].m_obj;
lean_object* v_snd_3440_ = stack[9].m_obj;
lean_object* v_overlaps_3441_ = stack[10].m_obj;
lean_object* v_matcherLevels_3442_ = stack[11].m_obj;
lean_object* v_toPure_3443_ = stack[12].m_obj;
lean_object* v_onRemaining_3444_ = stack[13].m_obj;
lean_object* v_remaining_3445_ = stack[14].m_obj;
lean_object* v_toBind_3446_ = stack[15].m_obj;
lean_object* v_alts_3447_ = stack[16].m_obj;
lean_object* v___x_3448_ = stack[17].m_obj;
lean_object* v___x_3449_ = stack[18].m_obj;
lean_object* v_remaining_x27_3450_ = stack[19].m_obj;
lean_object* v___f_3451_ = stack[20].m_obj;
lean_object* v_inst_3452_ = stack[21].m_obj;
lean_object* v___x_3453_ = stack[22].m_obj;
uint8_t v___x_3454_ = stack[23].m_num;
lean_object* v_liftWith_3455_ = stack[24].m_obj;
lean_object* v_restoreM_3456_ = stack[25].m_obj;
lean_object* v_matcherName_3457_ = stack[26].m_obj;
lean_object* v_origAltTypes_3458_ = stack[27].m_obj;
lean_object* v_res_3464_;
v_res_3464_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3431_, v_params_x27_3432_, v_fst_3433_, v_discrs_x27_3434_, v_fst_3435_, v_numParams_3436_, v_numDiscrs_3437_, v_altInfos_3438_, v_uElimPos_x3f_3439_, v_snd_3440_, v_overlaps_3441_, v_matcherLevels_3442_, v_toPure_3443_, v_onRemaining_3444_, v_remaining_3445_, v_toBind_3446_, v_alts_3447_, v___x_3448_, v___x_3449_, v_remaining_x27_3450_, v___f_3451_, v_inst_3452_, v___x_3453_, v___x_3454_, v_liftWith_3455_, v_restoreM_3456_, v_matcherName_3457_, v_origAltTypes_3458_);
stack->m_obj
 = v_res_3464_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3465_ = _args[0];
lean_object* v_params_x27_3466_ = _args[1];
lean_object* v_fst_3467_ = _args[2];
lean_object* v_discrs_x27_3468_ = _args[3];
lean_object* v_fst_3469_ = _args[4];
lean_object* v_numParams_3470_ = _args[5];
lean_object* v_numDiscrs_3471_ = _args[6];
lean_object* v_altInfos_3472_ = _args[7];
lean_object* v_uElimPos_x3f_3473_ = _args[8];
lean_object* v_snd_3474_ = _args[9];
lean_object* v_overlaps_3475_ = _args[10];
lean_object* v_matcherLevels_3476_ = _args[11];
lean_object* v_toPure_3477_ = _args[12];
lean_object* v_onRemaining_3478_ = _args[13];
lean_object* v_remaining_3479_ = _args[14];
lean_object* v_toBind_3480_ = _args[15];
lean_object* v_alts_3481_ = _args[16];
lean_object* v___x_3482_ = _args[17];
lean_object* v___x_3483_ = _args[18];
lean_object* v_remaining_x27_3484_ = _args[19];
lean_object* v___f_3485_ = _args[20];
lean_object* v_inst_3486_ = _args[21];
lean_object* v___x_3487_ = _args[22];
lean_object* v___x_3488_ = _args[23];
lean_object* v_liftWith_3489_ = _args[24];
lean_object* v_restoreM_3490_ = _args[25];
lean_object* v_matcherName_3491_ = _args[26];
lean_object* v_origAltTypes_3492_ = _args[27];
_start:
{
uint8_t v___x_15462__boxed_3493_; lean_object* v_res_3494_; 
v___x_15462__boxed_3493_ = lean_unbox(v___x_3488_);
v_res_3494_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3465_, v_params_x27_3466_, v_fst_3467_, v_discrs_x27_3468_, v_fst_3469_, v_numParams_3470_, v_numDiscrs_3471_, v_altInfos_3472_, v_uElimPos_x3f_3473_, v_snd_3474_, v_overlaps_3475_, v_matcherLevels_3476_, v_toPure_3477_, v_onRemaining_3478_, v_remaining_3479_, v_toBind_3480_, v_alts_3481_, v___x_3482_, v___x_3483_, v_remaining_x27_3484_, v___f_3485_, v_inst_3486_, v___x_3487_, v___x_15462__boxed_3493_, v_liftWith_3489_, v_restoreM_3490_, v_matcherName_3491_, v_origAltTypes_3492_);
return v_res_3494_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3495_, lean_object* v_toPure_3496_, lean_object* v_toBind_3497_, lean_object* v___f_3498_, lean_object* v___x_3499_, lean_object* v___x_3500_, lean_object* v_inst_3501_, lean_object* v___x_3502_, lean_object* v_toMonadExceptOf_3503_, uint8_t v___x_3504_, uint8_t v_useSplitter_3505_, lean_object* v_onAlt_3506_, lean_object* v___f_3507_, lean_object* v_fst_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_numDiscrEqs_3511_, lean_object* v___x_3512_, lean_object* v_params_x27_3513_, lean_object* v_fst_3514_, lean_object* v_discrs_x27_3515_, lean_object* v_fst_3516_, lean_object* v_numParams_3517_, lean_object* v_numDiscrs_3518_, lean_object* v_altInfos_3519_, lean_object* v_uElimPos_x3f_3520_, lean_object* v_snd_3521_, lean_object* v_overlaps_3522_, lean_object* v_matcherLevels_3523_, lean_object* v_onRemaining_3524_, lean_object* v_remaining_3525_, lean_object* v_remaining_x27_3526_, lean_object* v___x_3527_, uint8_t v___x_3528_, lean_object* v_liftWith_3529_, lean_object* v_restoreM_3530_, lean_object* v_matcherName_3531_, lean_object* v_aux1_3532_, lean_object* v_____r_3533_){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___f_3537_; lean_object* v___x_3538_; lean_object* v___f_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3534_ = lean_array_get_size(v_alts_3495_);
v___x_3535_ = lean_box(v___x_3504_);
v___x_3536_ = lean_box(v_useSplitter_3505_);
lean_inc_n(v_inst_3501_, 2);
lean_inc(v___x_3499_);
lean_inc_n(v_toBind_3497_, 2);
lean_inc(v_toPure_3496_);
v___f_3537_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 21, 17);
lean_closure_set(v___f_3537_, 0, v___x_3534_);
lean_closure_set(v___f_3537_, 1, v_toPure_3496_);
lean_closure_set(v___f_3537_, 2, v_toBind_3497_);
lean_closure_set(v___f_3537_, 3, v___f_3498_);
lean_closure_set(v___f_3537_, 4, v___x_3499_);
lean_closure_set(v___f_3537_, 5, v___x_3500_);
lean_closure_set(v___f_3537_, 6, v_inst_3501_);
lean_closure_set(v___f_3537_, 7, v___x_3502_);
lean_closure_set(v___f_3537_, 8, v_toMonadExceptOf_3503_);
lean_closure_set(v___f_3537_, 9, v___x_3535_);
lean_closure_set(v___f_3537_, 10, v___x_3536_);
lean_closure_set(v___f_3537_, 11, v_onAlt_3506_);
lean_closure_set(v___f_3537_, 12, v___f_3507_);
lean_closure_set(v___f_3537_, 13, v_fst_3508_);
lean_closure_set(v___f_3537_, 14, v_inst_3509_);
lean_closure_set(v___f_3537_, 15, v_inst_3510_);
lean_closure_set(v___f_3537_, 16, v_numDiscrEqs_3511_);
v___x_3538_ = lean_box(v___x_3528_);
v___f_3539_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 28, 27);
lean_closure_set(v___f_3539_, 0, v___x_3512_);
lean_closure_set(v___f_3539_, 1, v_params_x27_3513_);
lean_closure_set(v___f_3539_, 2, v_fst_3514_);
lean_closure_set(v___f_3539_, 3, v_discrs_x27_3515_);
lean_closure_set(v___f_3539_, 4, v_fst_3516_);
lean_closure_set(v___f_3539_, 5, v_numParams_3517_);
lean_closure_set(v___f_3539_, 6, v_numDiscrs_3518_);
lean_closure_set(v___f_3539_, 7, v_altInfos_3519_);
lean_closure_set(v___f_3539_, 8, v_uElimPos_x3f_3520_);
lean_closure_set(v___f_3539_, 9, v_snd_3521_);
lean_closure_set(v___f_3539_, 10, v_overlaps_3522_);
lean_closure_set(v___f_3539_, 11, v_matcherLevels_3523_);
lean_closure_set(v___f_3539_, 12, v_toPure_3496_);
lean_closure_set(v___f_3539_, 13, v_onRemaining_3524_);
lean_closure_set(v___f_3539_, 14, v_remaining_3525_);
lean_closure_set(v___f_3539_, 15, v_toBind_3497_);
lean_closure_set(v___f_3539_, 16, v_alts_3495_);
lean_closure_set(v___f_3539_, 17, v___x_3499_);
lean_closure_set(v___f_3539_, 18, v___x_3534_);
lean_closure_set(v___f_3539_, 19, v_remaining_x27_3526_);
lean_closure_set(v___f_3539_, 20, v___f_3537_);
lean_closure_set(v___f_3539_, 21, v_inst_3501_);
lean_closure_set(v___f_3539_, 22, v___x_3527_);
lean_closure_set(v___f_3539_, 23, v___x_3538_);
lean_closure_set(v___f_3539_, 24, v_liftWith_3529_);
lean_closure_set(v___f_3539_, 25, v_restoreM_3530_);
lean_closure_set(v___f_3539_, 26, v_matcherName_3531_);
v___x_3540_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3540_, 0, v___x_3534_);
lean_closure_set(v___x_3540_, 1, v_aux1_3532_);
v___x_3541_ = lean_apply_2(v_inst_3501_, lean_box(0), v___x_3540_);
v___x_3542_ = lean_apply_4(v_toBind_3497_, lean_box(0), lean_box(0), v___x_3541_, v___f_3539_);
return v___x_3542_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__52_0interp(lean_interpreter_value* stack)
{
lean_object* v_alts_3495_ = stack[0].m_obj;
lean_object* v_toPure_3496_ = stack[1].m_obj;
lean_object* v_toBind_3497_ = stack[2].m_obj;
lean_object* v___f_3498_ = stack[3].m_obj;
lean_object* v___x_3499_ = stack[4].m_obj;
lean_object* v___x_3500_ = stack[5].m_obj;
lean_object* v_inst_3501_ = stack[6].m_obj;
lean_object* v___x_3502_ = stack[7].m_obj;
lean_object* v_toMonadExceptOf_3503_ = stack[8].m_obj;
uint8_t v___x_3504_ = stack[9].m_num;
uint8_t v_useSplitter_3505_ = stack[10].m_num;
lean_object* v_onAlt_3506_ = stack[11].m_obj;
lean_object* v___f_3507_ = stack[12].m_obj;
lean_object* v_fst_3508_ = stack[13].m_obj;
lean_object* v_inst_3509_ = stack[14].m_obj;
lean_object* v_inst_3510_ = stack[15].m_obj;
lean_object* v_numDiscrEqs_3511_ = stack[16].m_obj;
lean_object* v___x_3512_ = stack[17].m_obj;
lean_object* v_params_x27_3513_ = stack[18].m_obj;
lean_object* v_fst_3514_ = stack[19].m_obj;
lean_object* v_discrs_x27_3515_ = stack[20].m_obj;
lean_object* v_fst_3516_ = stack[21].m_obj;
lean_object* v_numParams_3517_ = stack[22].m_obj;
lean_object* v_numDiscrs_3518_ = stack[23].m_obj;
lean_object* v_altInfos_3519_ = stack[24].m_obj;
lean_object* v_uElimPos_x3f_3520_ = stack[25].m_obj;
lean_object* v_snd_3521_ = stack[26].m_obj;
lean_object* v_overlaps_3522_ = stack[27].m_obj;
lean_object* v_matcherLevels_3523_ = stack[28].m_obj;
lean_object* v_onRemaining_3524_ = stack[29].m_obj;
lean_object* v_remaining_3525_ = stack[30].m_obj;
lean_object* v_remaining_x27_3526_ = stack[31].m_obj;
lean_object* v___x_3527_ = stack[32].m_obj;
uint8_t v___x_3528_ = stack[33].m_num;
lean_object* v_liftWith_3529_ = stack[34].m_obj;
lean_object* v_restoreM_3530_ = stack[35].m_obj;
lean_object* v_matcherName_3531_ = stack[36].m_obj;
lean_object* v_aux1_3532_ = stack[37].m_obj;
lean_object* v_____r_3533_ = stack[38].m_obj;
lean_object* v_res_3543_;
v_res_3543_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3495_, v_toPure_3496_, v_toBind_3497_, v___f_3498_, v___x_3499_, v___x_3500_, v_inst_3501_, v___x_3502_, v_toMonadExceptOf_3503_, v___x_3504_, v_useSplitter_3505_, v_onAlt_3506_, v___f_3507_, v_fst_3508_, v_inst_3509_, v_inst_3510_, v_numDiscrEqs_3511_, v___x_3512_, v_params_x27_3513_, v_fst_3514_, v_discrs_x27_3515_, v_fst_3516_, v_numParams_3517_, v_numDiscrs_3518_, v_altInfos_3519_, v_uElimPos_x3f_3520_, v_snd_3521_, v_overlaps_3522_, v_matcherLevels_3523_, v_onRemaining_3524_, v_remaining_3525_, v_remaining_x27_3526_, v___x_3527_, v___x_3528_, v_liftWith_3529_, v_restoreM_3530_, v_matcherName_3531_, v_aux1_3532_, v_____r_3533_);
stack->m_obj
 = v_res_3543_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3544_ = _args[0];
lean_object* v_toPure_3545_ = _args[1];
lean_object* v_toBind_3546_ = _args[2];
lean_object* v___f_3547_ = _args[3];
lean_object* v___x_3548_ = _args[4];
lean_object* v___x_3549_ = _args[5];
lean_object* v_inst_3550_ = _args[6];
lean_object* v___x_3551_ = _args[7];
lean_object* v_toMonadExceptOf_3552_ = _args[8];
lean_object* v___x_3553_ = _args[9];
lean_object* v_useSplitter_3554_ = _args[10];
lean_object* v_onAlt_3555_ = _args[11];
lean_object* v___f_3556_ = _args[12];
lean_object* v_fst_3557_ = _args[13];
lean_object* v_inst_3558_ = _args[14];
lean_object* v_inst_3559_ = _args[15];
lean_object* v_numDiscrEqs_3560_ = _args[16];
lean_object* v___x_3561_ = _args[17];
lean_object* v_params_x27_3562_ = _args[18];
lean_object* v_fst_3563_ = _args[19];
lean_object* v_discrs_x27_3564_ = _args[20];
lean_object* v_fst_3565_ = _args[21];
lean_object* v_numParams_3566_ = _args[22];
lean_object* v_numDiscrs_3567_ = _args[23];
lean_object* v_altInfos_3568_ = _args[24];
lean_object* v_uElimPos_x3f_3569_ = _args[25];
lean_object* v_snd_3570_ = _args[26];
lean_object* v_overlaps_3571_ = _args[27];
lean_object* v_matcherLevels_3572_ = _args[28];
lean_object* v_onRemaining_3573_ = _args[29];
lean_object* v_remaining_3574_ = _args[30];
lean_object* v_remaining_x27_3575_ = _args[31];
lean_object* v___x_3576_ = _args[32];
lean_object* v___x_3577_ = _args[33];
lean_object* v_liftWith_3578_ = _args[34];
lean_object* v_restoreM_3579_ = _args[35];
lean_object* v_matcherName_3580_ = _args[36];
lean_object* v_aux1_3581_ = _args[37];
lean_object* v_____r_3582_ = _args[38];
_start:
{
uint8_t v___x_15519__boxed_3583_; uint8_t v_useSplitter_boxed_3584_; uint8_t v___x_15527__boxed_3585_; lean_object* v_res_3586_; 
v___x_15519__boxed_3583_ = lean_unbox(v___x_3553_);
v_useSplitter_boxed_3584_ = lean_unbox(v_useSplitter_3554_);
v___x_15527__boxed_3585_ = lean_unbox(v___x_3577_);
v_res_3586_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3544_, v_toPure_3545_, v_toBind_3546_, v___f_3547_, v___x_3548_, v___x_3549_, v_inst_3550_, v___x_3551_, v_toMonadExceptOf_3552_, v___x_15519__boxed_3583_, v_useSplitter_boxed_3584_, v_onAlt_3555_, v___f_3556_, v_fst_3557_, v_inst_3558_, v_inst_3559_, v_numDiscrEqs_3560_, v___x_3561_, v_params_x27_3562_, v_fst_3563_, v_discrs_x27_3564_, v_fst_3565_, v_numParams_3566_, v_numDiscrs_3567_, v_altInfos_3568_, v_uElimPos_x3f_3569_, v_snd_3570_, v_overlaps_3571_, v_matcherLevels_3572_, v_onRemaining_3573_, v_remaining_3574_, v_remaining_x27_3575_, v___x_3576_, v___x_15527__boxed_3585_, v_liftWith_3578_, v_restoreM_3579_, v_matcherName_3580_, v_aux1_3581_, v_____r_3582_);
return v_res_3586_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3589_ = l_Lean_stringToMessageData(v___x_3588_);
return v___x_3589_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2));
v___x_3592_ = l_Lean_stringToMessageData(v___x_3591_);
return v___x_3592_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4));
v___x_3595_ = l_Lean_stringToMessageData(v___x_3594_);
return v___x_3595_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v_numParams_3596_, lean_object* v_numDiscrs_3597_, lean_object* v_altInfos_3598_, lean_object* v_uElimPos_x3f_3599_, lean_object* v_snd_3600_, lean_object* v_overlaps_3601_, lean_object* v_matcherName_3602_, lean_object* v_matcherLevels_3603_, lean_object* v_params_x27_3604_, lean_object* v_fst_3605_, lean_object* v_discrs_x27_3606_, lean_object* v_toPure_3607_, lean_object* v_onRemaining_3608_, lean_object* v_remaining_3609_, lean_object* v_toBind_3610_, lean_object* v_inst_3611_, lean_object* v_alts_3612_, lean_object* v___f_3613_, uint8_t v___x_3614_, lean_object* v_inst_3615_, lean_object* v_remaining_x27_3616_, lean_object* v_onAlt_3617_, lean_object* v_inst_3618_, lean_object* v___f_3619_, lean_object* v_matcherApp_3620_, lean_object* v___x_3621_, uint8_t v_useSplitter_3622_, uint8_t v_isCasesOn_3623_, lean_object* v___f_3624_, lean_object* v___x_3625_, lean_object* v___x_3626_, lean_object* v_toMonadExceptOf_3627_, lean_object* v___f_3628_, lean_object* v_numDiscrEqs_3629_, lean_object* v_____s_3630_){
_start:
{
lean_object* v_snd_3631_; lean_object* v_fst_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3698_; 
v_snd_3631_ = lean_ctor_get(v_____s_3630_, 1);
v_fst_3632_ = lean_ctor_get(v_____s_3630_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_____s_3630_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3634_ = v_____s_3630_;
v_isShared_3635_ = v_isSharedCheck_3698_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_snd_3631_);
lean_inc(v_fst_3632_);
lean_dec(v_____s_3630_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3698_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_fst_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3696_; 
v_fst_3636_ = lean_ctor_get(v_snd_3631_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_snd_3631_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; 
v_unused_3697_ = lean_ctor_get(v_snd_3631_, 1);
lean_dec(v_unused_3697_);
v___x_3638_ = v_snd_3631_;
v_isShared_3639_ = v_isSharedCheck_3696_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_fst_3636_);
lean_dec(v_snd_3631_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3696_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___f_3640_; 
lean_inc(v_toBind_3610_);
lean_inc_ref(v_remaining_3609_);
lean_inc(v_onRemaining_3608_);
lean_inc(v_toPure_3607_);
lean_inc_ref(v_discrs_x27_3606_);
lean_inc_ref(v_fst_3605_);
lean_inc_ref(v_params_x27_3604_);
lean_inc_ref(v_matcherLevels_3603_);
lean_inc(v_matcherName_3602_);
lean_inc_ref(v_overlaps_3601_);
lean_inc_ref(v_snd_3600_);
lean_inc(v_uElimPos_x3f_3599_);
lean_inc_ref(v_altInfos_3598_);
lean_inc(v_numDiscrs_3597_);
lean_inc(v_numParams_3596_);
lean_inc(v_fst_3632_);
v___f_3640_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3640_, 0, v_fst_3632_);
lean_closure_set(v___f_3640_, 1, v_numParams_3596_);
lean_closure_set(v___f_3640_, 2, v_numDiscrs_3597_);
lean_closure_set(v___f_3640_, 3, v_altInfos_3598_);
lean_closure_set(v___f_3640_, 4, v_uElimPos_x3f_3599_);
lean_closure_set(v___f_3640_, 5, v_snd_3600_);
lean_closure_set(v___f_3640_, 6, v_overlaps_3601_);
lean_closure_set(v___f_3640_, 7, v_matcherName_3602_);
lean_closure_set(v___f_3640_, 8, v_matcherLevels_3603_);
lean_closure_set(v___f_3640_, 9, v_params_x27_3604_);
lean_closure_set(v___f_3640_, 10, v_fst_3605_);
lean_closure_set(v___f_3640_, 11, v_discrs_x27_3606_);
lean_closure_set(v___f_3640_, 12, v_toPure_3607_);
lean_closure_set(v___f_3640_, 13, v_onRemaining_3608_);
lean_closure_set(v___f_3640_, 14, v_remaining_3609_);
lean_closure_set(v___f_3640_, 15, v_toBind_3610_);
if (v_useSplitter_3622_ == 0)
{
lean_del_object(v___x_3634_);
lean_dec(v_fst_3632_);
lean_dec(v_numDiscrEqs_3629_);
lean_dec(v___f_3628_);
lean_dec_ref(v_toMonadExceptOf_3627_);
lean_dec(v___x_3626_);
lean_dec(v___x_3625_);
lean_dec(v___f_3624_);
lean_dec_ref(v_remaining_3609_);
lean_dec(v_onRemaining_3608_);
lean_dec_ref(v_overlaps_3601_);
lean_dec_ref(v_snd_3600_);
lean_dec(v_uElimPos_x3f_3599_);
lean_dec_ref(v_altInfos_3598_);
lean_dec(v_numDiscrs_3597_);
lean_dec(v_numParams_3596_);
goto v___jp_3641_;
}
else
{
if (v_isCasesOn_3623_ == 0)
{
lean_object* v_liftWith_3668_; lean_object* v_restoreM_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_aux1_3672_; lean_object* v_aux1_3673_; lean_object* v_aux1_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
lean_dec_ref(v___f_3640_);
lean_del_object(v___x_3638_);
lean_dec_ref(v_matcherApp_3620_);
lean_dec(v___f_3619_);
lean_dec(v___f_3613_);
v_liftWith_3668_ = lean_ctor_get(v_inst_3611_, 0);
lean_inc(v_liftWith_3668_);
v_restoreM_3669_ = lean_ctor_get(v_inst_3611_, 1);
lean_inc(v_restoreM_3669_);
lean_inc_ref(v_matcherLevels_3603_);
v___x_3670_ = lean_array_to_list(v_matcherLevels_3603_);
lean_inc(v___x_3670_);
lean_inc(v_matcherName_3602_);
v___x_3671_ = l_Lean_mkConst(v_matcherName_3602_, v___x_3670_);
v_aux1_3672_ = l_Lean_mkAppN(v___x_3671_, v_params_x27_3604_);
lean_inc_ref(v_fst_3605_);
v_aux1_3673_ = l_Lean_Expr_app___override(v_aux1_3672_, v_fst_3605_);
v_aux1_3674_ = l_Lean_mkAppN(v_aux1_3673_, v_discrs_x27_3606_);
lean_inc_ref(v_aux1_3674_);
v___x_3675_ = l_Lean_indentExpr(v_aux1_3674_);
v___x_3676_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
if (v_isShared_3635_ == 0)
{
lean_ctor_set_tag(v___x_3634_, 7);
lean_ctor_set(v___x_3634_, 1, v___x_3675_);
lean_ctor_set(v___x_3634_, 0, v___x_3676_);
v___x_3678_ = v___x_3634_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3676_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v___x_3675_);
v___x_3678_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___f_3681_; uint8_t v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___f_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___f_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3679_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_3680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___f_3681_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3681_, 0, v___x_3680_);
v___x_3682_ = 0;
v___x_3683_ = lean_box(v___x_3614_);
v___x_3684_ = lean_box(v_useSplitter_3622_);
v___x_3685_ = lean_box(v___x_3682_);
lean_inc_ref(v_aux1_3674_);
lean_inc(v_restoreM_3669_);
lean_inc(v_liftWith_3668_);
lean_inc(v_inst_3615_);
lean_inc_n(v_toBind_3610_, 2);
v___f_3686_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 39, 38);
lean_closure_set(v___f_3686_, 0, v_alts_3612_);
lean_closure_set(v___f_3686_, 1, v_toPure_3607_);
lean_closure_set(v___f_3686_, 2, v_toBind_3610_);
lean_closure_set(v___f_3686_, 3, v___f_3624_);
lean_closure_set(v___f_3686_, 4, v___x_3621_);
lean_closure_set(v___f_3686_, 5, v___x_3625_);
lean_closure_set(v___f_3686_, 6, v_inst_3615_);
lean_closure_set(v___f_3686_, 7, v___x_3626_);
lean_closure_set(v___f_3686_, 8, v_toMonadExceptOf_3627_);
lean_closure_set(v___f_3686_, 9, v___x_3683_);
lean_closure_set(v___f_3686_, 10, v___x_3684_);
lean_closure_set(v___f_3686_, 11, v_onAlt_3617_);
lean_closure_set(v___f_3686_, 12, v___f_3628_);
lean_closure_set(v___f_3686_, 13, v_fst_3636_);
lean_closure_set(v___f_3686_, 14, v_inst_3611_);
lean_closure_set(v___f_3686_, 15, v_inst_3618_);
lean_closure_set(v___f_3686_, 16, v_numDiscrEqs_3629_);
lean_closure_set(v___f_3686_, 17, v___x_3670_);
lean_closure_set(v___f_3686_, 18, v_params_x27_3604_);
lean_closure_set(v___f_3686_, 19, v_fst_3605_);
lean_closure_set(v___f_3686_, 20, v_discrs_x27_3606_);
lean_closure_set(v___f_3686_, 21, v_fst_3632_);
lean_closure_set(v___f_3686_, 22, v_numParams_3596_);
lean_closure_set(v___f_3686_, 23, v_numDiscrs_3597_);
lean_closure_set(v___f_3686_, 24, v_altInfos_3598_);
lean_closure_set(v___f_3686_, 25, v_uElimPos_x3f_3599_);
lean_closure_set(v___f_3686_, 26, v_snd_3600_);
lean_closure_set(v___f_3686_, 27, v_overlaps_3601_);
lean_closure_set(v___f_3686_, 28, v_matcherLevels_3603_);
lean_closure_set(v___f_3686_, 29, v_onRemaining_3608_);
lean_closure_set(v___f_3686_, 30, v_remaining_3609_);
lean_closure_set(v___f_3686_, 31, v_remaining_x27_3616_);
lean_closure_set(v___f_3686_, 32, v___x_3679_);
lean_closure_set(v___f_3686_, 33, v___x_3685_);
lean_closure_set(v___f_3686_, 34, v_liftWith_3668_);
lean_closure_set(v___f_3686_, 35, v_restoreM_3669_);
lean_closure_set(v___f_3686_, 36, v_matcherName_3602_);
lean_closure_set(v___f_3686_, 37, v_aux1_3674_);
v___x_3687_ = lean_box(v___x_3682_);
v___x_3688_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3688_, 0, v_aux1_3674_);
lean_closure_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = lean_apply_2(v_inst_3615_, lean_box(0), v___x_3688_);
v___f_3690_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3690_, 0, v___x_3689_);
lean_closure_set(v___f_3690_, 1, v___f_3681_);
v___x_3691_ = lean_apply_2(v_liftWith_3668_, lean_box(0), v___f_3690_);
v___x_3692_ = lean_apply_1(v_restoreM_3669_, lean_box(0));
v___x_3693_ = lean_apply_4(v_toBind_3610_, lean_box(0), lean_box(0), v___x_3691_, v___x_3692_);
v___x_3694_ = lean_apply_4(v_toBind_3610_, lean_box(0), lean_box(0), v___x_3693_, v___f_3686_);
return v___x_3694_;
}
}
else
{
lean_del_object(v___x_3634_);
lean_dec(v_fst_3632_);
lean_dec(v_numDiscrEqs_3629_);
lean_dec(v___f_3628_);
lean_dec_ref(v_toMonadExceptOf_3627_);
lean_dec(v___x_3626_);
lean_dec(v___x_3625_);
lean_dec(v___f_3624_);
lean_dec_ref(v_remaining_3609_);
lean_dec(v_onRemaining_3608_);
lean_dec_ref(v_overlaps_3601_);
lean_dec_ref(v_snd_3600_);
lean_dec(v_uElimPos_x3f_3599_);
lean_dec_ref(v_altInfos_3598_);
lean_dec(v_numDiscrs_3597_);
lean_dec(v_numParams_3596_);
goto v___jp_3641_;
}
}
v___jp_3641_:
{
lean_object* v_liftWith_3642_; lean_object* v_restoreM_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v_aux_3646_; lean_object* v_aux_3647_; lean_object* v_aux_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___f_3653_; lean_object* v___x_3654_; lean_object* v___x_3656_; 
v_liftWith_3642_ = lean_ctor_get(v_inst_3611_, 0);
lean_inc(v_liftWith_3642_);
v_restoreM_3643_ = lean_ctor_get(v_inst_3611_, 1);
lean_inc(v_restoreM_3643_);
v___x_3644_ = lean_array_to_list(v_matcherLevels_3603_);
v___x_3645_ = l_Lean_mkConst(v_matcherName_3602_, v___x_3644_);
v_aux_3646_ = l_Lean_mkAppN(v___x_3645_, v_params_x27_3604_);
lean_dec_ref(v_params_x27_3604_);
v_aux_3647_ = l_Lean_Expr_app___override(v_aux_3646_, v_fst_3605_);
v_aux_3648_ = l_Lean_mkAppN(v_aux_3647_, v_discrs_x27_3606_);
lean_dec_ref(v_discrs_x27_3606_);
lean_inc_ref_n(v_aux_3648_, 2);
v___x_3649_ = l_Lean_indentExpr(v_aux_3648_);
v___x_3650_ = 1;
v___x_3651_ = lean_box(v___x_3614_);
v___x_3652_ = lean_box(v___x_3650_);
lean_inc(v_inst_3615_);
lean_inc(v_toBind_3610_);
v___f_3653_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3653_, 0, v_alts_3612_);
lean_closure_set(v___f_3653_, 1, v_toPure_3607_);
lean_closure_set(v___f_3653_, 2, v_toBind_3610_);
lean_closure_set(v___f_3653_, 3, v___f_3613_);
lean_closure_set(v___f_3653_, 4, v___x_3651_);
lean_closure_set(v___f_3653_, 5, v___x_3652_);
lean_closure_set(v___f_3653_, 6, v_inst_3615_);
lean_closure_set(v___f_3653_, 7, v_remaining_x27_3616_);
lean_closure_set(v___f_3653_, 8, v_onAlt_3617_);
lean_closure_set(v___f_3653_, 9, v_inst_3611_);
lean_closure_set(v___f_3653_, 10, v_inst_3618_);
lean_closure_set(v___f_3653_, 11, v___f_3619_);
lean_closure_set(v___f_3653_, 12, v_fst_3636_);
lean_closure_set(v___f_3653_, 13, v_matcherApp_3620_);
lean_closure_set(v___f_3653_, 14, v___x_3621_);
lean_closure_set(v___f_3653_, 15, v___f_3640_);
lean_closure_set(v___f_3653_, 16, v_aux_3648_);
v___x_3654_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 7);
lean_ctor_set(v___x_3638_, 1, v___x_3649_);
lean_ctor_set(v___x_3638_, 0, v___x_3654_);
v___x_3656_ = v___x_3638_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3649_);
v___x_3656_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___f_3657_; uint8_t v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___f_3657_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3657_, 0, v___x_3656_);
v___x_3658_ = 0;
v___x_3659_ = lean_box(v___x_3658_);
v___x_3660_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3660_, 0, v_aux_3648_);
lean_closure_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = lean_apply_2(v_inst_3615_, lean_box(0), v___x_3660_);
v___f_3662_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3662_, 0, v___x_3661_);
lean_closure_set(v___f_3662_, 1, v___f_3657_);
v___x_3663_ = lean_apply_2(v_liftWith_3642_, lean_box(0), v___f_3662_);
v___x_3664_ = lean_apply_1(v_restoreM_3643_, lean_box(0));
lean_inc(v_toBind_3610_);
v___x_3665_ = lean_apply_4(v_toBind_3610_, lean_box(0), lean_box(0), v___x_3663_, v___x_3664_);
v___x_3666_ = lean_apply_4(v_toBind_3610_, lean_box(0), lean_box(0), v___x_3665_, v___f_3653_);
return v___x_3666_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__55_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_3596_ = stack[0].m_obj;
lean_object* v_numDiscrs_3597_ = stack[1].m_obj;
lean_object* v_altInfos_3598_ = stack[2].m_obj;
lean_object* v_uElimPos_x3f_3599_ = stack[3].m_obj;
lean_object* v_snd_3600_ = stack[4].m_obj;
lean_object* v_overlaps_3601_ = stack[5].m_obj;
lean_object* v_matcherName_3602_ = stack[6].m_obj;
lean_object* v_matcherLevels_3603_ = stack[7].m_obj;
lean_object* v_params_x27_3604_ = stack[8].m_obj;
lean_object* v_fst_3605_ = stack[9].m_obj;
lean_object* v_discrs_x27_3606_ = stack[10].m_obj;
lean_object* v_toPure_3607_ = stack[11].m_obj;
lean_object* v_onRemaining_3608_ = stack[12].m_obj;
lean_object* v_remaining_3609_ = stack[13].m_obj;
lean_object* v_toBind_3610_ = stack[14].m_obj;
lean_object* v_inst_3611_ = stack[15].m_obj;
lean_object* v_alts_3612_ = stack[16].m_obj;
lean_object* v___f_3613_ = stack[17].m_obj;
uint8_t v___x_3614_ = stack[18].m_num;
lean_object* v_inst_3615_ = stack[19].m_obj;
lean_object* v_remaining_x27_3616_ = stack[20].m_obj;
lean_object* v_onAlt_3617_ = stack[21].m_obj;
lean_object* v_inst_3618_ = stack[22].m_obj;
lean_object* v___f_3619_ = stack[23].m_obj;
lean_object* v_matcherApp_3620_ = stack[24].m_obj;
lean_object* v___x_3621_ = stack[25].m_obj;
uint8_t v_useSplitter_3622_ = stack[26].m_num;
uint8_t v_isCasesOn_3623_ = stack[27].m_num;
lean_object* v___f_3624_ = stack[28].m_obj;
lean_object* v___x_3625_ = stack[29].m_obj;
lean_object* v___x_3626_ = stack[30].m_obj;
lean_object* v_toMonadExceptOf_3627_ = stack[31].m_obj;
lean_object* v___f_3628_ = stack[32].m_obj;
lean_object* v_numDiscrEqs_3629_ = stack[33].m_obj;
lean_object* v_____s_3630_ = stack[34].m_obj;
lean_object* v_res_3699_;
v_res_3699_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3596_, v_numDiscrs_3597_, v_altInfos_3598_, v_uElimPos_x3f_3599_, v_snd_3600_, v_overlaps_3601_, v_matcherName_3602_, v_matcherLevels_3603_, v_params_x27_3604_, v_fst_3605_, v_discrs_x27_3606_, v_toPure_3607_, v_onRemaining_3608_, v_remaining_3609_, v_toBind_3610_, v_inst_3611_, v_alts_3612_, v___f_3613_, v___x_3614_, v_inst_3615_, v_remaining_x27_3616_, v_onAlt_3617_, v_inst_3618_, v___f_3619_, v_matcherApp_3620_, v___x_3621_, v_useSplitter_3622_, v_isCasesOn_3623_, v___f_3624_, v___x_3625_, v___x_3626_, v_toMonadExceptOf_3627_, v___f_3628_, v_numDiscrEqs_3629_, v_____s_3630_);
stack->m_obj
 = v_res_3699_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v_numParams_3700_ = _args[0];
lean_object* v_numDiscrs_3701_ = _args[1];
lean_object* v_altInfos_3702_ = _args[2];
lean_object* v_uElimPos_x3f_3703_ = _args[3];
lean_object* v_snd_3704_ = _args[4];
lean_object* v_overlaps_3705_ = _args[5];
lean_object* v_matcherName_3706_ = _args[6];
lean_object* v_matcherLevels_3707_ = _args[7];
lean_object* v_params_x27_3708_ = _args[8];
lean_object* v_fst_3709_ = _args[9];
lean_object* v_discrs_x27_3710_ = _args[10];
lean_object* v_toPure_3711_ = _args[11];
lean_object* v_onRemaining_3712_ = _args[12];
lean_object* v_remaining_3713_ = _args[13];
lean_object* v_toBind_3714_ = _args[14];
lean_object* v_inst_3715_ = _args[15];
lean_object* v_alts_3716_ = _args[16];
lean_object* v___f_3717_ = _args[17];
lean_object* v___x_3718_ = _args[18];
lean_object* v_inst_3719_ = _args[19];
lean_object* v_remaining_x27_3720_ = _args[20];
lean_object* v_onAlt_3721_ = _args[21];
lean_object* v_inst_3722_ = _args[22];
lean_object* v___f_3723_ = _args[23];
lean_object* v_matcherApp_3724_ = _args[24];
lean_object* v___x_3725_ = _args[25];
lean_object* v_useSplitter_3726_ = _args[26];
lean_object* v_isCasesOn_3727_ = _args[27];
lean_object* v___f_3728_ = _args[28];
lean_object* v___x_3729_ = _args[29];
lean_object* v___x_3730_ = _args[30];
lean_object* v_toMonadExceptOf_3731_ = _args[31];
lean_object* v___f_3732_ = _args[32];
lean_object* v_numDiscrEqs_3733_ = _args[33];
lean_object* v_____s_3734_ = _args[34];
_start:
{
uint8_t v___x_15638__boxed_3735_; uint8_t v_useSplitter_boxed_3736_; uint8_t v_isCasesOn_boxed_3737_; lean_object* v_res_3738_; 
v___x_15638__boxed_3735_ = lean_unbox(v___x_3718_);
v_useSplitter_boxed_3736_ = lean_unbox(v_useSplitter_3726_);
v_isCasesOn_boxed_3737_ = lean_unbox(v_isCasesOn_3727_);
v_res_3738_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3700_, v_numDiscrs_3701_, v_altInfos_3702_, v_uElimPos_x3f_3703_, v_snd_3704_, v_overlaps_3705_, v_matcherName_3706_, v_matcherLevels_3707_, v_params_x27_3708_, v_fst_3709_, v_discrs_x27_3710_, v_toPure_3711_, v_onRemaining_3712_, v_remaining_3713_, v_toBind_3714_, v_inst_3715_, v_alts_3716_, v___f_3717_, v___x_15638__boxed_3735_, v_inst_3719_, v_remaining_x27_3720_, v_onAlt_3721_, v_inst_3722_, v___f_3723_, v_matcherApp_3724_, v___x_3725_, v_useSplitter_boxed_3736_, v_isCasesOn_boxed_3737_, v___f_3728_, v___x_3729_, v___x_3730_, v_toMonadExceptOf_3731_, v___f_3732_, v_numDiscrEqs_3733_, v_____s_3734_);
return v_res_3738_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3739_, lean_object* v_numDiscrs_3740_, lean_object* v_altInfos_3741_, lean_object* v_uElimPos_x3f_3742_, lean_object* v_snd_3743_, lean_object* v_overlaps_3744_, lean_object* v_matcherName_3745_, lean_object* v_params_x27_3746_, lean_object* v_fst_3747_, lean_object* v_discrs_x27_3748_, lean_object* v_toPure_3749_, lean_object* v_onRemaining_3750_, lean_object* v_remaining_3751_, lean_object* v_toBind_3752_, lean_object* v_inst_3753_, lean_object* v_alts_3754_, lean_object* v___f_3755_, uint8_t v___x_3756_, lean_object* v_inst_3757_, lean_object* v_onAlt_3758_, lean_object* v_inst_3759_, lean_object* v___f_3760_, lean_object* v_matcherApp_3761_, uint8_t v_useSplitter_3762_, uint8_t v_isCasesOn_3763_, lean_object* v___f_3764_, lean_object* v___x_3765_, lean_object* v___x_3766_, lean_object* v_toMonadExceptOf_3767_, lean_object* v___f_3768_, lean_object* v_numDiscrEqs_3769_, lean_object* v_fst_3770_, lean_object* v___f_3771_, lean_object* v_matcherLevels_3772_){
_start:
{
lean_object* v___x_3773_; lean_object* v_remaining_x27_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___f_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; size_t v_sz_3785_; size_t v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3773_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3774_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3775_ = lean_box(v___x_3756_);
v___x_3776_ = lean_box(v_useSplitter_3762_);
v___x_3777_ = lean_box(v_isCasesOn_3763_);
lean_inc_ref(v_inst_3759_);
lean_inc(v_toBind_3752_);
lean_inc_ref(v_discrs_x27_3748_);
v___f_3778_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 35, 34);
lean_closure_set(v___f_3778_, 0, v_numParams_3739_);
lean_closure_set(v___f_3778_, 1, v_numDiscrs_3740_);
lean_closure_set(v___f_3778_, 2, v_altInfos_3741_);
lean_closure_set(v___f_3778_, 3, v_uElimPos_x3f_3742_);
lean_closure_set(v___f_3778_, 4, v_snd_3743_);
lean_closure_set(v___f_3778_, 5, v_overlaps_3744_);
lean_closure_set(v___f_3778_, 6, v_matcherName_3745_);
lean_closure_set(v___f_3778_, 7, v_matcherLevels_3772_);
lean_closure_set(v___f_3778_, 8, v_params_x27_3746_);
lean_closure_set(v___f_3778_, 9, v_fst_3747_);
lean_closure_set(v___f_3778_, 10, v_discrs_x27_3748_);
lean_closure_set(v___f_3778_, 11, v_toPure_3749_);
lean_closure_set(v___f_3778_, 12, v_onRemaining_3750_);
lean_closure_set(v___f_3778_, 13, v_remaining_3751_);
lean_closure_set(v___f_3778_, 14, v_toBind_3752_);
lean_closure_set(v___f_3778_, 15, v_inst_3753_);
lean_closure_set(v___f_3778_, 16, v_alts_3754_);
lean_closure_set(v___f_3778_, 17, v___f_3755_);
lean_closure_set(v___f_3778_, 18, v___x_3775_);
lean_closure_set(v___f_3778_, 19, v_inst_3757_);
lean_closure_set(v___f_3778_, 20, v_remaining_x27_3774_);
lean_closure_set(v___f_3778_, 21, v_onAlt_3758_);
lean_closure_set(v___f_3778_, 22, v_inst_3759_);
lean_closure_set(v___f_3778_, 23, v___f_3760_);
lean_closure_set(v___f_3778_, 24, v_matcherApp_3761_);
lean_closure_set(v___f_3778_, 25, v___x_3773_);
lean_closure_set(v___f_3778_, 26, v___x_3776_);
lean_closure_set(v___f_3778_, 27, v___x_3777_);
lean_closure_set(v___f_3778_, 28, v___f_3764_);
lean_closure_set(v___f_3778_, 29, v___x_3765_);
lean_closure_set(v___f_3778_, 30, v___x_3766_);
lean_closure_set(v___f_3778_, 31, v_toMonadExceptOf_3767_);
lean_closure_set(v___f_3778_, 32, v___f_3768_);
lean_closure_set(v___f_3778_, 33, v_numDiscrEqs_3769_);
v___x_3779_ = l_Array_reverse___redArg(v_fst_3770_);
v___x_3780_ = lean_array_get_size(v___x_3779_);
v___x_3781_ = l_Array_toSubarray___redArg(v___x_3779_, v___x_3773_, v___x_3780_);
v___x_3782_ = l_Array_reverse___redArg(v_discrs_x27_3748_);
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3773_);
lean_ctor_set(v___x_3783_, 1, v___x_3781_);
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v_remaining_x27_3774_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v_sz_3785_ = lean_array_size(v___x_3782_);
v___x_3786_ = ((size_t)0ULL);
v___x_3787_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3759_, v___x_3782_, v___f_3771_, v_sz_3785_, v___x_3786_, v___x_3784_);
v___x_3788_ = lean_apply_4(v_toBind_3752_, lean_box(0), lean_box(0), v___x_3787_, v___f_3778_);
return v___x_3788_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__54_0interp(lean_interpreter_value* stack)
{
lean_object* v_numParams_3739_ = stack[0].m_obj;
lean_object* v_numDiscrs_3740_ = stack[1].m_obj;
lean_object* v_altInfos_3741_ = stack[2].m_obj;
lean_object* v_uElimPos_x3f_3742_ = stack[3].m_obj;
lean_object* v_snd_3743_ = stack[4].m_obj;
lean_object* v_overlaps_3744_ = stack[5].m_obj;
lean_object* v_matcherName_3745_ = stack[6].m_obj;
lean_object* v_params_x27_3746_ = stack[7].m_obj;
lean_object* v_fst_3747_ = stack[8].m_obj;
lean_object* v_discrs_x27_3748_ = stack[9].m_obj;
lean_object* v_toPure_3749_ = stack[10].m_obj;
lean_object* v_onRemaining_3750_ = stack[11].m_obj;
lean_object* v_remaining_3751_ = stack[12].m_obj;
lean_object* v_toBind_3752_ = stack[13].m_obj;
lean_object* v_inst_3753_ = stack[14].m_obj;
lean_object* v_alts_3754_ = stack[15].m_obj;
lean_object* v___f_3755_ = stack[16].m_obj;
uint8_t v___x_3756_ = stack[17].m_num;
lean_object* v_inst_3757_ = stack[18].m_obj;
lean_object* v_onAlt_3758_ = stack[19].m_obj;
lean_object* v_inst_3759_ = stack[20].m_obj;
lean_object* v___f_3760_ = stack[21].m_obj;
lean_object* v_matcherApp_3761_ = stack[22].m_obj;
uint8_t v_useSplitter_3762_ = stack[23].m_num;
uint8_t v_isCasesOn_3763_ = stack[24].m_num;
lean_object* v___f_3764_ = stack[25].m_obj;
lean_object* v___x_3765_ = stack[26].m_obj;
lean_object* v___x_3766_ = stack[27].m_obj;
lean_object* v_toMonadExceptOf_3767_ = stack[28].m_obj;
lean_object* v___f_3768_ = stack[29].m_obj;
lean_object* v_numDiscrEqs_3769_ = stack[30].m_obj;
lean_object* v_fst_3770_ = stack[31].m_obj;
lean_object* v___f_3771_ = stack[32].m_obj;
lean_object* v_matcherLevels_3772_ = stack[33].m_obj;
lean_object* v_res_3789_;
v_res_3789_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3739_, v_numDiscrs_3740_, v_altInfos_3741_, v_uElimPos_x3f_3742_, v_snd_3743_, v_overlaps_3744_, v_matcherName_3745_, v_params_x27_3746_, v_fst_3747_, v_discrs_x27_3748_, v_toPure_3749_, v_onRemaining_3750_, v_remaining_3751_, v_toBind_3752_, v_inst_3753_, v_alts_3754_, v___f_3755_, v___x_3756_, v_inst_3757_, v_onAlt_3758_, v_inst_3759_, v___f_3760_, v_matcherApp_3761_, v_useSplitter_3762_, v_isCasesOn_3763_, v___f_3764_, v___x_3765_, v___x_3766_, v_toMonadExceptOf_3767_, v___f_3768_, v_numDiscrEqs_3769_, v_fst_3770_, v___f_3771_, v_matcherLevels_3772_);
stack->m_obj
 = v_res_3789_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3790_ = _args[0];
lean_object* v_numDiscrs_3791_ = _args[1];
lean_object* v_altInfos_3792_ = _args[2];
lean_object* v_uElimPos_x3f_3793_ = _args[3];
lean_object* v_snd_3794_ = _args[4];
lean_object* v_overlaps_3795_ = _args[5];
lean_object* v_matcherName_3796_ = _args[6];
lean_object* v_params_x27_3797_ = _args[7];
lean_object* v_fst_3798_ = _args[8];
lean_object* v_discrs_x27_3799_ = _args[9];
lean_object* v_toPure_3800_ = _args[10];
lean_object* v_onRemaining_3801_ = _args[11];
lean_object* v_remaining_3802_ = _args[12];
lean_object* v_toBind_3803_ = _args[13];
lean_object* v_inst_3804_ = _args[14];
lean_object* v_alts_3805_ = _args[15];
lean_object* v___f_3806_ = _args[16];
lean_object* v___x_3807_ = _args[17];
lean_object* v_inst_3808_ = _args[18];
lean_object* v_onAlt_3809_ = _args[19];
lean_object* v_inst_3810_ = _args[20];
lean_object* v___f_3811_ = _args[21];
lean_object* v_matcherApp_3812_ = _args[22];
lean_object* v_useSplitter_3813_ = _args[23];
lean_object* v_isCasesOn_3814_ = _args[24];
lean_object* v___f_3815_ = _args[25];
lean_object* v___x_3816_ = _args[26];
lean_object* v___x_3817_ = _args[27];
lean_object* v_toMonadExceptOf_3818_ = _args[28];
lean_object* v___f_3819_ = _args[29];
lean_object* v_numDiscrEqs_3820_ = _args[30];
lean_object* v_fst_3821_ = _args[31];
lean_object* v___f_3822_ = _args[32];
lean_object* v_matcherLevels_3823_ = _args[33];
_start:
{
uint8_t v___x_15892__boxed_3824_; uint8_t v_useSplitter_boxed_3825_; uint8_t v_isCasesOn_boxed_3826_; lean_object* v_res_3827_; 
v___x_15892__boxed_3824_ = lean_unbox(v___x_3807_);
v_useSplitter_boxed_3825_ = lean_unbox(v_useSplitter_3813_);
v_isCasesOn_boxed_3826_ = lean_unbox(v_isCasesOn_3814_);
v_res_3827_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3790_, v_numDiscrs_3791_, v_altInfos_3792_, v_uElimPos_x3f_3793_, v_snd_3794_, v_overlaps_3795_, v_matcherName_3796_, v_params_x27_3797_, v_fst_3798_, v_discrs_x27_3799_, v_toPure_3800_, v_onRemaining_3801_, v_remaining_3802_, v_toBind_3803_, v_inst_3804_, v_alts_3805_, v___f_3806_, v___x_15892__boxed_3824_, v_inst_3808_, v_onAlt_3809_, v_inst_3810_, v___f_3811_, v_matcherApp_3812_, v_useSplitter_boxed_3825_, v_isCasesOn_boxed_3826_, v___f_3815_, v___x_3816_, v___x_3817_, v_toMonadExceptOf_3818_, v___f_3819_, v_numDiscrEqs_3820_, v_fst_3821_, v___f_3822_, v_matcherLevels_3823_);
return v_res_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v___f_3828_, lean_object* v_matcherLevels_3829_){
_start:
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_apply_1(v___f_3828_, v_matcherLevels_3829_);
return v___x_3830_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3831_, lean_object* v_matcherName_3832_, lean_object* v_params_x27_3833_, lean_object* v_discrs_x27_3834_, lean_object* v_toPure_3835_, lean_object* v_onRemaining_3836_, lean_object* v_remaining_3837_, lean_object* v_toBind_3838_, lean_object* v_inst_3839_, lean_object* v_alts_3840_, lean_object* v___f_3841_, uint8_t v___x_3842_, lean_object* v_inst_3843_, lean_object* v_onAlt_3844_, lean_object* v_inst_3845_, lean_object* v___f_3846_, lean_object* v_matcherApp_3847_, uint8_t v_useSplitter_3848_, uint8_t v_isCasesOn_3849_, lean_object* v___f_3850_, lean_object* v___x_3851_, lean_object* v___x_3852_, lean_object* v_toMonadExceptOf_3853_, lean_object* v___f_3854_, lean_object* v_numDiscrEqs_3855_, lean_object* v___f_3856_, lean_object* v_matcherLevels_3857_, lean_object* v_____x_3858_){
_start:
{
lean_object* v_snd_3859_; lean_object* v_snd_3860_; lean_object* v_fst_3861_; lean_object* v_fst_3862_; lean_object* v_fst_3863_; lean_object* v_snd_3864_; lean_object* v_numParams_3865_; lean_object* v_numDiscrs_3866_; lean_object* v_altInfos_3867_; lean_object* v_uElimPos_x3f_3868_; lean_object* v_overlaps_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___f_3873_; 
v_snd_3859_ = lean_ctor_get(v_____x_3858_, 1);
lean_inc(v_snd_3859_);
v_snd_3860_ = lean_ctor_get(v_snd_3859_, 1);
lean_inc(v_snd_3860_);
v_fst_3861_ = lean_ctor_get(v_____x_3858_, 0);
lean_inc(v_fst_3861_);
lean_dec_ref(v_____x_3858_);
v_fst_3862_ = lean_ctor_get(v_snd_3859_, 0);
lean_inc(v_fst_3862_);
lean_dec(v_snd_3859_);
v_fst_3863_ = lean_ctor_get(v_snd_3860_, 0);
lean_inc(v_fst_3863_);
v_snd_3864_ = lean_ctor_get(v_snd_3860_, 1);
lean_inc(v_snd_3864_);
lean_dec(v_snd_3860_);
v_numParams_3865_ = lean_ctor_get(v_toMatcherInfo_3831_, 0);
lean_inc(v_numParams_3865_);
v_numDiscrs_3866_ = lean_ctor_get(v_toMatcherInfo_3831_, 1);
lean_inc(v_numDiscrs_3866_);
v_altInfos_3867_ = lean_ctor_get(v_toMatcherInfo_3831_, 2);
lean_inc_ref(v_altInfos_3867_);
v_uElimPos_x3f_3868_ = lean_ctor_get(v_toMatcherInfo_3831_, 3);
lean_inc_n(v_uElimPos_x3f_3868_, 2);
v_overlaps_3869_ = lean_ctor_get(v_toMatcherInfo_3831_, 5);
lean_inc_ref(v_overlaps_3869_);
lean_dec_ref(v_toMatcherInfo_3831_);
v___x_3870_ = lean_box(v___x_3842_);
v___x_3871_ = lean_box(v_useSplitter_3848_);
v___x_3872_ = lean_box(v_isCasesOn_3849_);
lean_inc(v_toBind_3838_);
lean_inc(v_toPure_3835_);
v___f_3873_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 34, 33);
lean_closure_set(v___f_3873_, 0, v_numParams_3865_);
lean_closure_set(v___f_3873_, 1, v_numDiscrs_3866_);
lean_closure_set(v___f_3873_, 2, v_altInfos_3867_);
lean_closure_set(v___f_3873_, 3, v_uElimPos_x3f_3868_);
lean_closure_set(v___f_3873_, 4, v_snd_3864_);
lean_closure_set(v___f_3873_, 5, v_overlaps_3869_);
lean_closure_set(v___f_3873_, 6, v_matcherName_3832_);
lean_closure_set(v___f_3873_, 7, v_params_x27_3833_);
lean_closure_set(v___f_3873_, 8, v_fst_3861_);
lean_closure_set(v___f_3873_, 9, v_discrs_x27_3834_);
lean_closure_set(v___f_3873_, 10, v_toPure_3835_);
lean_closure_set(v___f_3873_, 11, v_onRemaining_3836_);
lean_closure_set(v___f_3873_, 12, v_remaining_3837_);
lean_closure_set(v___f_3873_, 13, v_toBind_3838_);
lean_closure_set(v___f_3873_, 14, v_inst_3839_);
lean_closure_set(v___f_3873_, 15, v_alts_3840_);
lean_closure_set(v___f_3873_, 16, v___f_3841_);
lean_closure_set(v___f_3873_, 17, v___x_3870_);
lean_closure_set(v___f_3873_, 18, v_inst_3843_);
lean_closure_set(v___f_3873_, 19, v_onAlt_3844_);
lean_closure_set(v___f_3873_, 20, v_inst_3845_);
lean_closure_set(v___f_3873_, 21, v___f_3846_);
lean_closure_set(v___f_3873_, 22, v_matcherApp_3847_);
lean_closure_set(v___f_3873_, 23, v___x_3871_);
lean_closure_set(v___f_3873_, 24, v___x_3872_);
lean_closure_set(v___f_3873_, 25, v___f_3850_);
lean_closure_set(v___f_3873_, 26, v___x_3851_);
lean_closure_set(v___f_3873_, 27, v___x_3852_);
lean_closure_set(v___f_3873_, 28, v_toMonadExceptOf_3853_);
lean_closure_set(v___f_3873_, 29, v___f_3854_);
lean_closure_set(v___f_3873_, 30, v_numDiscrEqs_3855_);
lean_closure_set(v___f_3873_, 31, v_fst_3863_);
lean_closure_set(v___f_3873_, 32, v___f_3856_);
if (lean_obj_tag(v_uElimPos_x3f_3868_) == 0)
{
lean_object* v___f_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_dec(v_fst_3862_);
v___f_3874_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3874_, 0, v___f_3873_);
v___x_3875_ = lean_apply_2(v_toPure_3835_, lean_box(0), v_matcherLevels_3857_);
v___x_3876_ = lean_apply_4(v_toBind_3838_, lean_box(0), lean_box(0), v___x_3875_, v___f_3874_);
return v___x_3876_;
}
else
{
lean_object* v_val_3877_; lean_object* v___f_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v_val_3877_ = lean_ctor_get(v_uElimPos_x3f_3868_, 0);
lean_inc(v_val_3877_);
lean_dec_ref_known(v_uElimPos_x3f_3868_, 1);
v___f_3878_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3878_, 0, v___f_3873_);
v___x_3879_ = lean_array_set(v_matcherLevels_3857_, v_val_3877_, v_fst_3862_);
lean_dec(v_val_3877_);
v___x_3880_ = lean_apply_2(v_toPure_3835_, lean_box(0), v___x_3879_);
v___x_3881_ = lean_apply_4(v_toBind_3838_, lean_box(0), lean_box(0), v___x_3880_, v___f_3878_);
return v___x_3881_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__58_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMatcherInfo_3831_ = stack[0].m_obj;
lean_object* v_matcherName_3832_ = stack[1].m_obj;
lean_object* v_params_x27_3833_ = stack[2].m_obj;
lean_object* v_discrs_x27_3834_ = stack[3].m_obj;
lean_object* v_toPure_3835_ = stack[4].m_obj;
lean_object* v_onRemaining_3836_ = stack[5].m_obj;
lean_object* v_remaining_3837_ = stack[6].m_obj;
lean_object* v_toBind_3838_ = stack[7].m_obj;
lean_object* v_inst_3839_ = stack[8].m_obj;
lean_object* v_alts_3840_ = stack[9].m_obj;
lean_object* v___f_3841_ = stack[10].m_obj;
uint8_t v___x_3842_ = stack[11].m_num;
lean_object* v_inst_3843_ = stack[12].m_obj;
lean_object* v_onAlt_3844_ = stack[13].m_obj;
lean_object* v_inst_3845_ = stack[14].m_obj;
lean_object* v___f_3846_ = stack[15].m_obj;
lean_object* v_matcherApp_3847_ = stack[16].m_obj;
uint8_t v_useSplitter_3848_ = stack[17].m_num;
uint8_t v_isCasesOn_3849_ = stack[18].m_num;
lean_object* v___f_3850_ = stack[19].m_obj;
lean_object* v___x_3851_ = stack[20].m_obj;
lean_object* v___x_3852_ = stack[21].m_obj;
lean_object* v_toMonadExceptOf_3853_ = stack[22].m_obj;
lean_object* v___f_3854_ = stack[23].m_obj;
lean_object* v_numDiscrEqs_3855_ = stack[24].m_obj;
lean_object* v___f_3856_ = stack[25].m_obj;
lean_object* v_matcherLevels_3857_ = stack[26].m_obj;
lean_object* v_____x_3858_ = stack[27].m_obj;
lean_object* v_res_3882_;
v_res_3882_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3831_, v_matcherName_3832_, v_params_x27_3833_, v_discrs_x27_3834_, v_toPure_3835_, v_onRemaining_3836_, v_remaining_3837_, v_toBind_3838_, v_inst_3839_, v_alts_3840_, v___f_3841_, v___x_3842_, v_inst_3843_, v_onAlt_3844_, v_inst_3845_, v___f_3846_, v_matcherApp_3847_, v_useSplitter_3848_, v_isCasesOn_3849_, v___f_3850_, v___x_3851_, v___x_3852_, v_toMonadExceptOf_3853_, v___f_3854_, v_numDiscrEqs_3855_, v___f_3856_, v_matcherLevels_3857_, v_____x_3858_);
stack->m_obj
 = v_res_3882_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3883_ = _args[0];
lean_object* v_matcherName_3884_ = _args[1];
lean_object* v_params_x27_3885_ = _args[2];
lean_object* v_discrs_x27_3886_ = _args[3];
lean_object* v_toPure_3887_ = _args[4];
lean_object* v_onRemaining_3888_ = _args[5];
lean_object* v_remaining_3889_ = _args[6];
lean_object* v_toBind_3890_ = _args[7];
lean_object* v_inst_3891_ = _args[8];
lean_object* v_alts_3892_ = _args[9];
lean_object* v___f_3893_ = _args[10];
lean_object* v___x_3894_ = _args[11];
lean_object* v_inst_3895_ = _args[12];
lean_object* v_onAlt_3896_ = _args[13];
lean_object* v_inst_3897_ = _args[14];
lean_object* v___f_3898_ = _args[15];
lean_object* v_matcherApp_3899_ = _args[16];
lean_object* v_useSplitter_3900_ = _args[17];
lean_object* v_isCasesOn_3901_ = _args[18];
lean_object* v___f_3902_ = _args[19];
lean_object* v___x_3903_ = _args[20];
lean_object* v___x_3904_ = _args[21];
lean_object* v_toMonadExceptOf_3905_ = _args[22];
lean_object* v___f_3906_ = _args[23];
lean_object* v_numDiscrEqs_3907_ = _args[24];
lean_object* v___f_3908_ = _args[25];
lean_object* v_matcherLevels_3909_ = _args[26];
lean_object* v_____x_3910_ = _args[27];
_start:
{
uint8_t v___x_16008__boxed_3911_; uint8_t v_useSplitter_boxed_3912_; uint8_t v_isCasesOn_boxed_3913_; lean_object* v_res_3914_; 
v___x_16008__boxed_3911_ = lean_unbox(v___x_3894_);
v_useSplitter_boxed_3912_ = lean_unbox(v_useSplitter_3900_);
v_isCasesOn_boxed_3913_ = lean_unbox(v_isCasesOn_3901_);
v_res_3914_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3883_, v_matcherName_3884_, v_params_x27_3885_, v_discrs_x27_3886_, v_toPure_3887_, v_onRemaining_3888_, v_remaining_3889_, v_toBind_3890_, v_inst_3891_, v_alts_3892_, v___f_3893_, v___x_16008__boxed_3911_, v_inst_3895_, v_onAlt_3896_, v_inst_3897_, v___f_3898_, v_matcherApp_3899_, v_useSplitter_boxed_3912_, v_isCasesOn_boxed_3913_, v___f_3902_, v___x_3903_, v___x_3904_, v_toMonadExceptOf_3905_, v___f_3906_, v_numDiscrEqs_3907_, v___f_3908_, v_matcherLevels_3909_, v_____x_3910_);
return v_res_3914_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3915_, lean_object* v_inst_3916_, lean_object* v_toBind_3917_, lean_object* v_toMatcherInfo_3918_, lean_object* v_inst_3919_, lean_object* v___f_3920_, lean_object* v_onMotive_3921_, lean_object* v_discrs_3922_, lean_object* v_inst_3923_, lean_object* v_matcherName_3924_, lean_object* v_params_x27_3925_, lean_object* v_onRemaining_3926_, lean_object* v_remaining_3927_, lean_object* v_inst_3928_, lean_object* v_alts_3929_, lean_object* v___f_3930_, lean_object* v_onAlt_3931_, lean_object* v___f_3932_, lean_object* v_matcherApp_3933_, uint8_t v_useSplitter_3934_, uint8_t v_isCasesOn_3935_, lean_object* v___f_3936_, lean_object* v___x_3937_, lean_object* v___x_3938_, lean_object* v_toMonadExceptOf_3939_, lean_object* v___f_3940_, lean_object* v_numDiscrEqs_3941_, lean_object* v___f_3942_, lean_object* v_matcherLevels_3943_, lean_object* v_motive_3944_, lean_object* v_discrs_x27_3945_){
_start:
{
lean_object* v___f_3946_; uint8_t v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___f_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
lean_inc_ref_n(v_inst_3919_, 2);
lean_inc_ref(v_discrs_x27_3945_);
lean_inc_ref(v_toMatcherInfo_3918_);
lean_inc_n(v_toBind_3917_, 2);
lean_inc(v_inst_3916_);
lean_inc(v_toPure_3915_);
v___f_3946_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3946_, 0, v_toPure_3915_);
lean_closure_set(v___f_3946_, 1, v_inst_3916_);
lean_closure_set(v___f_3946_, 2, v_toBind_3917_);
lean_closure_set(v___f_3946_, 3, v_toMatcherInfo_3918_);
lean_closure_set(v___f_3946_, 4, v_discrs_x27_3945_);
lean_closure_set(v___f_3946_, 5, v_inst_3919_);
lean_closure_set(v___f_3946_, 6, v___f_3920_);
lean_closure_set(v___f_3946_, 7, v_onMotive_3921_);
lean_closure_set(v___f_3946_, 8, v_discrs_3922_);
lean_closure_set(v___f_3946_, 9, v_inst_3923_);
v___x_3947_ = 0;
v___x_3948_ = lean_box(v___x_3947_);
v___x_3949_ = lean_box(v_useSplitter_3934_);
v___x_3950_ = lean_box(v_isCasesOn_3935_);
lean_inc_ref(v_inst_3928_);
v___f_3951_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 28, 27);
lean_closure_set(v___f_3951_, 0, v_toMatcherInfo_3918_);
lean_closure_set(v___f_3951_, 1, v_matcherName_3924_);
lean_closure_set(v___f_3951_, 2, v_params_x27_3925_);
lean_closure_set(v___f_3951_, 3, v_discrs_x27_3945_);
lean_closure_set(v___f_3951_, 4, v_toPure_3915_);
lean_closure_set(v___f_3951_, 5, v_onRemaining_3926_);
lean_closure_set(v___f_3951_, 6, v_remaining_3927_);
lean_closure_set(v___f_3951_, 7, v_toBind_3917_);
lean_closure_set(v___f_3951_, 8, v_inst_3928_);
lean_closure_set(v___f_3951_, 9, v_alts_3929_);
lean_closure_set(v___f_3951_, 10, v___f_3930_);
lean_closure_set(v___f_3951_, 11, v___x_3948_);
lean_closure_set(v___f_3951_, 12, v_inst_3916_);
lean_closure_set(v___f_3951_, 13, v_onAlt_3931_);
lean_closure_set(v___f_3951_, 14, v_inst_3919_);
lean_closure_set(v___f_3951_, 15, v___f_3932_);
lean_closure_set(v___f_3951_, 16, v_matcherApp_3933_);
lean_closure_set(v___f_3951_, 17, v___x_3949_);
lean_closure_set(v___f_3951_, 18, v___x_3950_);
lean_closure_set(v___f_3951_, 19, v___f_3936_);
lean_closure_set(v___f_3951_, 20, v___x_3937_);
lean_closure_set(v___f_3951_, 21, v___x_3938_);
lean_closure_set(v___f_3951_, 22, v_toMonadExceptOf_3939_);
lean_closure_set(v___f_3951_, 23, v___f_3940_);
lean_closure_set(v___f_3951_, 24, v_numDiscrEqs_3941_);
lean_closure_set(v___f_3951_, 25, v___f_3942_);
lean_closure_set(v___f_3951_, 26, v_matcherLevels_3943_);
v___x_3952_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3928_, v_inst_3919_, v_motive_3944_, v___f_3946_, v___x_3947_);
v___x_3953_ = lean_apply_4(v_toBind_3917_, lean_box(0), lean_box(0), v___x_3952_, v___f_3951_);
return v___x_3953_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__57_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3915_ = stack[0].m_obj;
lean_object* v_inst_3916_ = stack[1].m_obj;
lean_object* v_toBind_3917_ = stack[2].m_obj;
lean_object* v_toMatcherInfo_3918_ = stack[3].m_obj;
lean_object* v_inst_3919_ = stack[4].m_obj;
lean_object* v___f_3920_ = stack[5].m_obj;
lean_object* v_onMotive_3921_ = stack[6].m_obj;
lean_object* v_discrs_3922_ = stack[7].m_obj;
lean_object* v_inst_3923_ = stack[8].m_obj;
lean_object* v_matcherName_3924_ = stack[9].m_obj;
lean_object* v_params_x27_3925_ = stack[10].m_obj;
lean_object* v_onRemaining_3926_ = stack[11].m_obj;
lean_object* v_remaining_3927_ = stack[12].m_obj;
lean_object* v_inst_3928_ = stack[13].m_obj;
lean_object* v_alts_3929_ = stack[14].m_obj;
lean_object* v___f_3930_ = stack[15].m_obj;
lean_object* v_onAlt_3931_ = stack[16].m_obj;
lean_object* v___f_3932_ = stack[17].m_obj;
lean_object* v_matcherApp_3933_ = stack[18].m_obj;
uint8_t v_useSplitter_3934_ = stack[19].m_num;
uint8_t v_isCasesOn_3935_ = stack[20].m_num;
lean_object* v___f_3936_ = stack[21].m_obj;
lean_object* v___x_3937_ = stack[22].m_obj;
lean_object* v___x_3938_ = stack[23].m_obj;
lean_object* v_toMonadExceptOf_3939_ = stack[24].m_obj;
lean_object* v___f_3940_ = stack[25].m_obj;
lean_object* v_numDiscrEqs_3941_ = stack[26].m_obj;
lean_object* v___f_3942_ = stack[27].m_obj;
lean_object* v_matcherLevels_3943_ = stack[28].m_obj;
lean_object* v_motive_3944_ = stack[29].m_obj;
lean_object* v_discrs_x27_3945_ = stack[30].m_obj;
lean_object* v_res_3954_;
v_res_3954_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3915_, v_inst_3916_, v_toBind_3917_, v_toMatcherInfo_3918_, v_inst_3919_, v___f_3920_, v_onMotive_3921_, v_discrs_3922_, v_inst_3923_, v_matcherName_3924_, v_params_x27_3925_, v_onRemaining_3926_, v_remaining_3927_, v_inst_3928_, v_alts_3929_, v___f_3930_, v_onAlt_3931_, v___f_3932_, v_matcherApp_3933_, v_useSplitter_3934_, v_isCasesOn_3935_, v___f_3936_, v___x_3937_, v___x_3938_, v_toMonadExceptOf_3939_, v___f_3940_, v_numDiscrEqs_3941_, v___f_3942_, v_matcherLevels_3943_, v_motive_3944_, v_discrs_x27_3945_);
stack->m_obj
 = v_res_3954_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3955_ = _args[0];
lean_object* v_inst_3956_ = _args[1];
lean_object* v_toBind_3957_ = _args[2];
lean_object* v_toMatcherInfo_3958_ = _args[3];
lean_object* v_inst_3959_ = _args[4];
lean_object* v___f_3960_ = _args[5];
lean_object* v_onMotive_3961_ = _args[6];
lean_object* v_discrs_3962_ = _args[7];
lean_object* v_inst_3963_ = _args[8];
lean_object* v_matcherName_3964_ = _args[9];
lean_object* v_params_x27_3965_ = _args[10];
lean_object* v_onRemaining_3966_ = _args[11];
lean_object* v_remaining_3967_ = _args[12];
lean_object* v_inst_3968_ = _args[13];
lean_object* v_alts_3969_ = _args[14];
lean_object* v___f_3970_ = _args[15];
lean_object* v_onAlt_3971_ = _args[16];
lean_object* v___f_3972_ = _args[17];
lean_object* v_matcherApp_3973_ = _args[18];
lean_object* v_useSplitter_3974_ = _args[19];
lean_object* v_isCasesOn_3975_ = _args[20];
lean_object* v___f_3976_ = _args[21];
lean_object* v___x_3977_ = _args[22];
lean_object* v___x_3978_ = _args[23];
lean_object* v_toMonadExceptOf_3979_ = _args[24];
lean_object* v___f_3980_ = _args[25];
lean_object* v_numDiscrEqs_3981_ = _args[26];
lean_object* v___f_3982_ = _args[27];
lean_object* v_matcherLevels_3983_ = _args[28];
lean_object* v_motive_3984_ = _args[29];
lean_object* v_discrs_x27_3985_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3986_; uint8_t v_isCasesOn_boxed_3987_; lean_object* v_res_3988_; 
v_useSplitter_boxed_3986_ = lean_unbox(v_useSplitter_3974_);
v_isCasesOn_boxed_3987_ = lean_unbox(v_isCasesOn_3975_);
v_res_3988_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3955_, v_inst_3956_, v_toBind_3957_, v_toMatcherInfo_3958_, v_inst_3959_, v___f_3960_, v_onMotive_3961_, v_discrs_3962_, v_inst_3963_, v_matcherName_3964_, v_params_x27_3965_, v_onRemaining_3966_, v_remaining_3967_, v_inst_3968_, v_alts_3969_, v___f_3970_, v_onAlt_3971_, v___f_3972_, v_matcherApp_3973_, v_useSplitter_boxed_3986_, v_isCasesOn_boxed_3987_, v___f_3976_, v___x_3977_, v___x_3978_, v_toMonadExceptOf_3979_, v___f_3980_, v_numDiscrEqs_3981_, v___f_3982_, v_matcherLevels_3983_, v_motive_3984_, v_discrs_x27_3985_);
return v_res_3988_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3989_, lean_object* v_inst_3990_, lean_object* v_toBind_3991_, lean_object* v_toMatcherInfo_3992_, lean_object* v_inst_3993_, lean_object* v___f_3994_, lean_object* v_onMotive_3995_, lean_object* v_discrs_3996_, lean_object* v_inst_3997_, lean_object* v_matcherName_3998_, lean_object* v_onRemaining_3999_, lean_object* v_remaining_4000_, lean_object* v_inst_4001_, lean_object* v_alts_4002_, lean_object* v___f_4003_, lean_object* v_onAlt_4004_, lean_object* v___f_4005_, lean_object* v_matcherApp_4006_, uint8_t v_useSplitter_4007_, uint8_t v_isCasesOn_4008_, lean_object* v___f_4009_, lean_object* v___x_4010_, lean_object* v___x_4011_, lean_object* v_toMonadExceptOf_4012_, lean_object* v___f_4013_, lean_object* v_numDiscrEqs_4014_, lean_object* v___f_4015_, lean_object* v_matcherLevels_4016_, lean_object* v_motive_4017_, lean_object* v_onParams_4018_, lean_object* v_params_x27_4019_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___f_4022_; size_t v_sz_4023_; size_t v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4020_ = lean_box(v_useSplitter_4007_);
v___x_4021_ = lean_box(v_isCasesOn_4008_);
lean_inc_ref(v_discrs_3996_);
lean_inc_ref(v_inst_3993_);
lean_inc(v_toBind_3991_);
v___f_4022_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 31, 30);
lean_closure_set(v___f_4022_, 0, v_toPure_3989_);
lean_closure_set(v___f_4022_, 1, v_inst_3990_);
lean_closure_set(v___f_4022_, 2, v_toBind_3991_);
lean_closure_set(v___f_4022_, 3, v_toMatcherInfo_3992_);
lean_closure_set(v___f_4022_, 4, v_inst_3993_);
lean_closure_set(v___f_4022_, 5, v___f_3994_);
lean_closure_set(v___f_4022_, 6, v_onMotive_3995_);
lean_closure_set(v___f_4022_, 7, v_discrs_3996_);
lean_closure_set(v___f_4022_, 8, v_inst_3997_);
lean_closure_set(v___f_4022_, 9, v_matcherName_3998_);
lean_closure_set(v___f_4022_, 10, v_params_x27_4019_);
lean_closure_set(v___f_4022_, 11, v_onRemaining_3999_);
lean_closure_set(v___f_4022_, 12, v_remaining_4000_);
lean_closure_set(v___f_4022_, 13, v_inst_4001_);
lean_closure_set(v___f_4022_, 14, v_alts_4002_);
lean_closure_set(v___f_4022_, 15, v___f_4003_);
lean_closure_set(v___f_4022_, 16, v_onAlt_4004_);
lean_closure_set(v___f_4022_, 17, v___f_4005_);
lean_closure_set(v___f_4022_, 18, v_matcherApp_4006_);
lean_closure_set(v___f_4022_, 19, v___x_4020_);
lean_closure_set(v___f_4022_, 20, v___x_4021_);
lean_closure_set(v___f_4022_, 21, v___f_4009_);
lean_closure_set(v___f_4022_, 22, v___x_4010_);
lean_closure_set(v___f_4022_, 23, v___x_4011_);
lean_closure_set(v___f_4022_, 24, v_toMonadExceptOf_4012_);
lean_closure_set(v___f_4022_, 25, v___f_4013_);
lean_closure_set(v___f_4022_, 26, v_numDiscrEqs_4014_);
lean_closure_set(v___f_4022_, 27, v___f_4015_);
lean_closure_set(v___f_4022_, 28, v_matcherLevels_4016_);
lean_closure_set(v___f_4022_, 29, v_motive_4017_);
v_sz_4023_ = lean_array_size(v_discrs_3996_);
v___x_4024_ = ((size_t)0ULL);
v___x_4025_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3993_, v_onParams_4018_, v_sz_4023_, v___x_4024_, v_discrs_3996_);
v___x_4026_ = lean_apply_4(v_toBind_3991_, lean_box(0), lean_box(0), v___x_4025_, v___f_4022_);
return v___x_4026_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__59_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_3989_ = stack[0].m_obj;
lean_object* v_inst_3990_ = stack[1].m_obj;
lean_object* v_toBind_3991_ = stack[2].m_obj;
lean_object* v_toMatcherInfo_3992_ = stack[3].m_obj;
lean_object* v_inst_3993_ = stack[4].m_obj;
lean_object* v___f_3994_ = stack[5].m_obj;
lean_object* v_onMotive_3995_ = stack[6].m_obj;
lean_object* v_discrs_3996_ = stack[7].m_obj;
lean_object* v_inst_3997_ = stack[8].m_obj;
lean_object* v_matcherName_3998_ = stack[9].m_obj;
lean_object* v_onRemaining_3999_ = stack[10].m_obj;
lean_object* v_remaining_4000_ = stack[11].m_obj;
lean_object* v_inst_4001_ = stack[12].m_obj;
lean_object* v_alts_4002_ = stack[13].m_obj;
lean_object* v___f_4003_ = stack[14].m_obj;
lean_object* v_onAlt_4004_ = stack[15].m_obj;
lean_object* v___f_4005_ = stack[16].m_obj;
lean_object* v_matcherApp_4006_ = stack[17].m_obj;
uint8_t v_useSplitter_4007_ = stack[18].m_num;
uint8_t v_isCasesOn_4008_ = stack[19].m_num;
lean_object* v___f_4009_ = stack[20].m_obj;
lean_object* v___x_4010_ = stack[21].m_obj;
lean_object* v___x_4011_ = stack[22].m_obj;
lean_object* v_toMonadExceptOf_4012_ = stack[23].m_obj;
lean_object* v___f_4013_ = stack[24].m_obj;
lean_object* v_numDiscrEqs_4014_ = stack[25].m_obj;
lean_object* v___f_4015_ = stack[26].m_obj;
lean_object* v_matcherLevels_4016_ = stack[27].m_obj;
lean_object* v_motive_4017_ = stack[28].m_obj;
lean_object* v_onParams_4018_ = stack[29].m_obj;
lean_object* v_params_x27_4019_ = stack[30].m_obj;
lean_object* v_res_4027_;
v_res_4027_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3989_, v_inst_3990_, v_toBind_3991_, v_toMatcherInfo_3992_, v_inst_3993_, v___f_3994_, v_onMotive_3995_, v_discrs_3996_, v_inst_3997_, v_matcherName_3998_, v_onRemaining_3999_, v_remaining_4000_, v_inst_4001_, v_alts_4002_, v___f_4003_, v_onAlt_4004_, v___f_4005_, v_matcherApp_4006_, v_useSplitter_4007_, v_isCasesOn_4008_, v___f_4009_, v___x_4010_, v___x_4011_, v_toMonadExceptOf_4012_, v___f_4013_, v_numDiscrEqs_4014_, v___f_4015_, v_matcherLevels_4016_, v_motive_4017_, v_onParams_4018_, v_params_x27_4019_);
stack->m_obj
 = v_res_4027_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_4028_ = _args[0];
lean_object* v_inst_4029_ = _args[1];
lean_object* v_toBind_4030_ = _args[2];
lean_object* v_toMatcherInfo_4031_ = _args[3];
lean_object* v_inst_4032_ = _args[4];
lean_object* v___f_4033_ = _args[5];
lean_object* v_onMotive_4034_ = _args[6];
lean_object* v_discrs_4035_ = _args[7];
lean_object* v_inst_4036_ = _args[8];
lean_object* v_matcherName_4037_ = _args[9];
lean_object* v_onRemaining_4038_ = _args[10];
lean_object* v_remaining_4039_ = _args[11];
lean_object* v_inst_4040_ = _args[12];
lean_object* v_alts_4041_ = _args[13];
lean_object* v___f_4042_ = _args[14];
lean_object* v_onAlt_4043_ = _args[15];
lean_object* v___f_4044_ = _args[16];
lean_object* v_matcherApp_4045_ = _args[17];
lean_object* v_useSplitter_4046_ = _args[18];
lean_object* v_isCasesOn_4047_ = _args[19];
lean_object* v___f_4048_ = _args[20];
lean_object* v___x_4049_ = _args[21];
lean_object* v___x_4050_ = _args[22];
lean_object* v_toMonadExceptOf_4051_ = _args[23];
lean_object* v___f_4052_ = _args[24];
lean_object* v_numDiscrEqs_4053_ = _args[25];
lean_object* v___f_4054_ = _args[26];
lean_object* v_matcherLevels_4055_ = _args[27];
lean_object* v_motive_4056_ = _args[28];
lean_object* v_onParams_4057_ = _args[29];
lean_object* v_params_x27_4058_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4059_; uint8_t v_isCasesOn_boxed_4060_; lean_object* v_res_4061_; 
v_useSplitter_boxed_4059_ = lean_unbox(v_useSplitter_4046_);
v_isCasesOn_boxed_4060_ = lean_unbox(v_isCasesOn_4047_);
v_res_4061_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_4028_, v_inst_4029_, v_toBind_4030_, v_toMatcherInfo_4031_, v_inst_4032_, v___f_4033_, v_onMotive_4034_, v_discrs_4035_, v_inst_4036_, v_matcherName_4037_, v_onRemaining_4038_, v_remaining_4039_, v_inst_4040_, v_alts_4041_, v___f_4042_, v_onAlt_4043_, v___f_4044_, v_matcherApp_4045_, v_useSplitter_boxed_4059_, v_isCasesOn_boxed_4060_, v___f_4048_, v___x_4049_, v___x_4050_, v_toMonadExceptOf_4051_, v___f_4052_, v_numDiscrEqs_4053_, v___f_4054_, v_matcherLevels_4055_, v_motive_4056_, v_onParams_4057_, v_params_x27_4058_);
return v_res_4061_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_4062_, lean_object* v_inst_4063_, lean_object* v_toBind_4064_, lean_object* v_toMatcherInfo_4065_, lean_object* v_inst_4066_, lean_object* v___f_4067_, lean_object* v_onMotive_4068_, lean_object* v_discrs_4069_, lean_object* v_inst_4070_, lean_object* v_matcherName_4071_, lean_object* v_onRemaining_4072_, lean_object* v_remaining_4073_, lean_object* v_inst_4074_, lean_object* v_alts_4075_, lean_object* v___f_4076_, lean_object* v_onAlt_4077_, lean_object* v___f_4078_, lean_object* v_matcherApp_4079_, uint8_t v_useSplitter_4080_, uint8_t v_isCasesOn_4081_, lean_object* v___f_4082_, lean_object* v___x_4083_, lean_object* v___x_4084_, lean_object* v_toMonadExceptOf_4085_, lean_object* v___f_4086_, lean_object* v___f_4087_, lean_object* v_matcherLevels_4088_, lean_object* v_motive_4089_, lean_object* v_onParams_4090_, lean_object* v_params_4091_, lean_object* v_numDiscrEqs_4092_){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___f_4095_; size_t v_sz_4096_; size_t v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4093_ = lean_box(v_useSplitter_4080_);
v___x_4094_ = lean_box(v_isCasesOn_4081_);
lean_inc(v_onParams_4090_);
lean_inc_ref(v_inst_4066_);
lean_inc(v_toBind_4064_);
v___f_4095_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 31, 30);
lean_closure_set(v___f_4095_, 0, v_toPure_4062_);
lean_closure_set(v___f_4095_, 1, v_inst_4063_);
lean_closure_set(v___f_4095_, 2, v_toBind_4064_);
lean_closure_set(v___f_4095_, 3, v_toMatcherInfo_4065_);
lean_closure_set(v___f_4095_, 4, v_inst_4066_);
lean_closure_set(v___f_4095_, 5, v___f_4067_);
lean_closure_set(v___f_4095_, 6, v_onMotive_4068_);
lean_closure_set(v___f_4095_, 7, v_discrs_4069_);
lean_closure_set(v___f_4095_, 8, v_inst_4070_);
lean_closure_set(v___f_4095_, 9, v_matcherName_4071_);
lean_closure_set(v___f_4095_, 10, v_onRemaining_4072_);
lean_closure_set(v___f_4095_, 11, v_remaining_4073_);
lean_closure_set(v___f_4095_, 12, v_inst_4074_);
lean_closure_set(v___f_4095_, 13, v_alts_4075_);
lean_closure_set(v___f_4095_, 14, v___f_4076_);
lean_closure_set(v___f_4095_, 15, v_onAlt_4077_);
lean_closure_set(v___f_4095_, 16, v___f_4078_);
lean_closure_set(v___f_4095_, 17, v_matcherApp_4079_);
lean_closure_set(v___f_4095_, 18, v___x_4093_);
lean_closure_set(v___f_4095_, 19, v___x_4094_);
lean_closure_set(v___f_4095_, 20, v___f_4082_);
lean_closure_set(v___f_4095_, 21, v___x_4083_);
lean_closure_set(v___f_4095_, 22, v___x_4084_);
lean_closure_set(v___f_4095_, 23, v_toMonadExceptOf_4085_);
lean_closure_set(v___f_4095_, 24, v___f_4086_);
lean_closure_set(v___f_4095_, 25, v_numDiscrEqs_4092_);
lean_closure_set(v___f_4095_, 26, v___f_4087_);
lean_closure_set(v___f_4095_, 27, v_matcherLevels_4088_);
lean_closure_set(v___f_4095_, 28, v_motive_4089_);
lean_closure_set(v___f_4095_, 29, v_onParams_4090_);
v_sz_4096_ = lean_array_size(v_params_4091_);
v___x_4097_ = ((size_t)0ULL);
v___x_4098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4066_, v_onParams_4090_, v_sz_4096_, v___x_4097_, v_params_4091_);
v___x_4099_ = lean_apply_4(v_toBind_4064_, lean_box(0), lean_box(0), v___x_4098_, v___f_4095_);
return v___x_4099_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__60_0interp(lean_interpreter_value* stack)
{
lean_object* v_toPure_4062_ = stack[0].m_obj;
lean_object* v_inst_4063_ = stack[1].m_obj;
lean_object* v_toBind_4064_ = stack[2].m_obj;
lean_object* v_toMatcherInfo_4065_ = stack[3].m_obj;
lean_object* v_inst_4066_ = stack[4].m_obj;
lean_object* v___f_4067_ = stack[5].m_obj;
lean_object* v_onMotive_4068_ = stack[6].m_obj;
lean_object* v_discrs_4069_ = stack[7].m_obj;
lean_object* v_inst_4070_ = stack[8].m_obj;
lean_object* v_matcherName_4071_ = stack[9].m_obj;
lean_object* v_onRemaining_4072_ = stack[10].m_obj;
lean_object* v_remaining_4073_ = stack[11].m_obj;
lean_object* v_inst_4074_ = stack[12].m_obj;
lean_object* v_alts_4075_ = stack[13].m_obj;
lean_object* v___f_4076_ = stack[14].m_obj;
lean_object* v_onAlt_4077_ = stack[15].m_obj;
lean_object* v___f_4078_ = stack[16].m_obj;
lean_object* v_matcherApp_4079_ = stack[17].m_obj;
uint8_t v_useSplitter_4080_ = stack[18].m_num;
uint8_t v_isCasesOn_4081_ = stack[19].m_num;
lean_object* v___f_4082_ = stack[20].m_obj;
lean_object* v___x_4083_ = stack[21].m_obj;
lean_object* v___x_4084_ = stack[22].m_obj;
lean_object* v_toMonadExceptOf_4085_ = stack[23].m_obj;
lean_object* v___f_4086_ = stack[24].m_obj;
lean_object* v___f_4087_ = stack[25].m_obj;
lean_object* v_matcherLevels_4088_ = stack[26].m_obj;
lean_object* v_motive_4089_ = stack[27].m_obj;
lean_object* v_onParams_4090_ = stack[28].m_obj;
lean_object* v_params_4091_ = stack[29].m_obj;
lean_object* v_numDiscrEqs_4092_ = stack[30].m_obj;
lean_object* v_res_4100_;
v_res_4100_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4062_, v_inst_4063_, v_toBind_4064_, v_toMatcherInfo_4065_, v_inst_4066_, v___f_4067_, v_onMotive_4068_, v_discrs_4069_, v_inst_4070_, v_matcherName_4071_, v_onRemaining_4072_, v_remaining_4073_, v_inst_4074_, v_alts_4075_, v___f_4076_, v_onAlt_4077_, v___f_4078_, v_matcherApp_4079_, v_useSplitter_4080_, v_isCasesOn_4081_, v___f_4082_, v___x_4083_, v___x_4084_, v_toMonadExceptOf_4085_, v___f_4086_, v___f_4087_, v_matcherLevels_4088_, v_motive_4089_, v_onParams_4090_, v_params_4091_, v_numDiscrEqs_4092_);
stack->m_obj
 = v_res_4100_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4101_ = _args[0];
lean_object* v_inst_4102_ = _args[1];
lean_object* v_toBind_4103_ = _args[2];
lean_object* v_toMatcherInfo_4104_ = _args[3];
lean_object* v_inst_4105_ = _args[4];
lean_object* v___f_4106_ = _args[5];
lean_object* v_onMotive_4107_ = _args[6];
lean_object* v_discrs_4108_ = _args[7];
lean_object* v_inst_4109_ = _args[8];
lean_object* v_matcherName_4110_ = _args[9];
lean_object* v_onRemaining_4111_ = _args[10];
lean_object* v_remaining_4112_ = _args[11];
lean_object* v_inst_4113_ = _args[12];
lean_object* v_alts_4114_ = _args[13];
lean_object* v___f_4115_ = _args[14];
lean_object* v_onAlt_4116_ = _args[15];
lean_object* v___f_4117_ = _args[16];
lean_object* v_matcherApp_4118_ = _args[17];
lean_object* v_useSplitter_4119_ = _args[18];
lean_object* v_isCasesOn_4120_ = _args[19];
lean_object* v___f_4121_ = _args[20];
lean_object* v___x_4122_ = _args[21];
lean_object* v___x_4123_ = _args[22];
lean_object* v_toMonadExceptOf_4124_ = _args[23];
lean_object* v___f_4125_ = _args[24];
lean_object* v___f_4126_ = _args[25];
lean_object* v_matcherLevels_4127_ = _args[26];
lean_object* v_motive_4128_ = _args[27];
lean_object* v_onParams_4129_ = _args[28];
lean_object* v_params_4130_ = _args[29];
lean_object* v_numDiscrEqs_4131_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4132_; uint8_t v_isCasesOn_boxed_4133_; lean_object* v_res_4134_; 
v_useSplitter_boxed_4132_ = lean_unbox(v_useSplitter_4119_);
v_isCasesOn_boxed_4133_ = lean_unbox(v_isCasesOn_4120_);
v_res_4134_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4101_, v_inst_4102_, v_toBind_4103_, v_toMatcherInfo_4104_, v_inst_4105_, v___f_4106_, v_onMotive_4107_, v_discrs_4108_, v_inst_4109_, v_matcherName_4110_, v_onRemaining_4111_, v_remaining_4112_, v_inst_4113_, v_alts_4114_, v___f_4115_, v_onAlt_4116_, v___f_4117_, v_matcherApp_4118_, v_useSplitter_boxed_4132_, v_isCasesOn_boxed_4133_, v___f_4121_, v___x_4122_, v___x_4123_, v_toMonadExceptOf_4124_, v___f_4125_, v___f_4126_, v_matcherLevels_4127_, v_motive_4128_, v_onParams_4129_, v_params_4130_, v_numDiscrEqs_4131_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4135_, lean_object* v_numDiscrEqs_4136_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = lean_apply_1(v___f_4135_, v_numDiscrEqs_4136_);
return v___x_4137_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4139_; lean_object* v___x_4140_; 
v___x_4139_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4140_ = l_Lean_stringToMessageData(v___x_4139_);
return v___x_4140_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; 
v___x_4142_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4143_ = l_Lean_stringToMessageData(v___x_4142_);
return v___x_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4144_, lean_object* v_inst_4145_, lean_object* v_inst_4146_, lean_object* v_toBind_4147_, lean_object* v___f_4148_, lean_object* v_toPure_4149_, lean_object* v___f_4150_, lean_object* v_____do__lift_4151_){
_start:
{
if (lean_obj_tag(v_____do__lift_4151_) == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_dec(v___f_4150_);
lean_dec(v_toPure_4149_);
v___x_4152_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4153_ = l_Lean_MessageData_ofName(v_matcherName_4144_);
v___x_4154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4152_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = l_Lean_throwError___redArg(v_inst_4145_, v_inst_4146_, v___x_4156_);
v___x_4158_ = lean_apply_4(v_toBind_4147_, lean_box(0), lean_box(0), v___x_4157_, v___f_4148_);
return v___x_4158_;
}
else
{
lean_object* v_val_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
lean_dec(v___f_4148_);
lean_dec_ref(v_inst_4146_);
lean_dec_ref(v_inst_4145_);
lean_dec(v_matcherName_4144_);
v_val_4159_ = lean_ctor_get(v_____do__lift_4151_, 0);
v___x_4160_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4159_);
v___x_4161_ = lean_apply_2(v_toPure_4149_, lean_box(0), v___x_4160_);
v___x_4162_ = lean_apply_4(v_toBind_4147_, lean_box(0), lean_box(0), v___x_4161_, v___f_4150_);
return v___x_4162_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4163_, lean_object* v_inst_4164_, lean_object* v_inst_4165_, lean_object* v_toBind_4166_, lean_object* v___f_4167_, lean_object* v_toPure_4168_, lean_object* v___f_4169_, lean_object* v_____do__lift_4170_){
_start:
{
lean_object* v_res_4171_; 
v_res_4171_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4163_, v_inst_4164_, v_inst_4165_, v_toBind_4166_, v___f_4167_, v_toPure_4168_, v___f_4169_, v_____do__lift_4170_);
lean_dec(v_____do__lift_4170_);
return v_res_4171_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4172_, lean_object* v_toPure_4173_, lean_object* v_inst_4174_, lean_object* v_toBind_4175_, lean_object* v_inst_4176_, lean_object* v___f_4177_, lean_object* v_onMotive_4178_, lean_object* v_inst_4179_, lean_object* v_onRemaining_4180_, lean_object* v_inst_4181_, lean_object* v___f_4182_, lean_object* v_onAlt_4183_, lean_object* v___f_4184_, uint8_t v_useSplitter_4185_, lean_object* v___f_4186_, lean_object* v___x_4187_, lean_object* v___x_4188_, lean_object* v_toMonadExceptOf_4189_, lean_object* v___f_4190_, lean_object* v___f_4191_, lean_object* v_onParams_4192_, lean_object* v_inst_4193_, lean_object* v_____do__lift_4194_){
_start:
{
lean_object* v_toMatcherInfo_4195_; lean_object* v_matcherName_4196_; lean_object* v_matcherLevels_4197_; lean_object* v_params_4198_; lean_object* v_motive_4199_; lean_object* v_discrs_4200_; lean_object* v_alts_4201_; lean_object* v_remaining_4202_; uint8_t v_isCasesOn_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___f_4206_; 
v_toMatcherInfo_4195_ = lean_ctor_get(v_matcherApp_4172_, 0);
lean_inc_ref(v_toMatcherInfo_4195_);
v_matcherName_4196_ = lean_ctor_get(v_matcherApp_4172_, 1);
lean_inc_n(v_matcherName_4196_, 3);
v_matcherLevels_4197_ = lean_ctor_get(v_matcherApp_4172_, 2);
lean_inc_ref(v_matcherLevels_4197_);
v_params_4198_ = lean_ctor_get(v_matcherApp_4172_, 3);
lean_inc_ref(v_params_4198_);
v_motive_4199_ = lean_ctor_get(v_matcherApp_4172_, 4);
lean_inc_ref(v_motive_4199_);
v_discrs_4200_ = lean_ctor_get(v_matcherApp_4172_, 5);
lean_inc_ref(v_discrs_4200_);
v_alts_4201_ = lean_ctor_get(v_matcherApp_4172_, 6);
lean_inc_ref(v_alts_4201_);
v_remaining_4202_ = lean_ctor_get(v_matcherApp_4172_, 7);
lean_inc_ref(v_remaining_4202_);
v_isCasesOn_4203_ = l_Lean_isCasesOnRecursor(v_____do__lift_4194_, v_matcherName_4196_);
v___x_4204_ = lean_box(v_useSplitter_4185_);
v___x_4205_ = lean_box(v_isCasesOn_4203_);
lean_inc_ref(v_inst_4179_);
lean_inc_ref(v_inst_4176_);
lean_inc(v_toBind_4175_);
lean_inc(v_toPure_4173_);
v___f_4206_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 31, 30);
lean_closure_set(v___f_4206_, 0, v_toPure_4173_);
lean_closure_set(v___f_4206_, 1, v_inst_4174_);
lean_closure_set(v___f_4206_, 2, v_toBind_4175_);
lean_closure_set(v___f_4206_, 3, v_toMatcherInfo_4195_);
lean_closure_set(v___f_4206_, 4, v_inst_4176_);
lean_closure_set(v___f_4206_, 5, v___f_4177_);
lean_closure_set(v___f_4206_, 6, v_onMotive_4178_);
lean_closure_set(v___f_4206_, 7, v_discrs_4200_);
lean_closure_set(v___f_4206_, 8, v_inst_4179_);
lean_closure_set(v___f_4206_, 9, v_matcherName_4196_);
lean_closure_set(v___f_4206_, 10, v_onRemaining_4180_);
lean_closure_set(v___f_4206_, 11, v_remaining_4202_);
lean_closure_set(v___f_4206_, 12, v_inst_4181_);
lean_closure_set(v___f_4206_, 13, v_alts_4201_);
lean_closure_set(v___f_4206_, 14, v___f_4182_);
lean_closure_set(v___f_4206_, 15, v_onAlt_4183_);
lean_closure_set(v___f_4206_, 16, v___f_4184_);
lean_closure_set(v___f_4206_, 17, v_matcherApp_4172_);
lean_closure_set(v___f_4206_, 18, v___x_4204_);
lean_closure_set(v___f_4206_, 19, v___x_4205_);
lean_closure_set(v___f_4206_, 20, v___f_4186_);
lean_closure_set(v___f_4206_, 21, v___x_4187_);
lean_closure_set(v___f_4206_, 22, v___x_4188_);
lean_closure_set(v___f_4206_, 23, v_toMonadExceptOf_4189_);
lean_closure_set(v___f_4206_, 24, v___f_4190_);
lean_closure_set(v___f_4206_, 25, v___f_4191_);
lean_closure_set(v___f_4206_, 26, v_matcherLevels_4197_);
lean_closure_set(v___f_4206_, 27, v_motive_4199_);
lean_closure_set(v___f_4206_, 28, v_onParams_4192_);
lean_closure_set(v___f_4206_, 29, v_params_4198_);
if (v_isCasesOn_4203_ == 0)
{
lean_object* v___f_4207_; lean_object* v___f_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___f_4207_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4207_, 0, v___f_4206_);
lean_inc_ref(v___f_4207_);
lean_inc(v_toBind_4175_);
lean_inc_ref(v_inst_4176_);
lean_inc(v_matcherName_4196_);
v___f_4208_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4208_, 0, v_matcherName_4196_);
lean_closure_set(v___f_4208_, 1, v_inst_4176_);
lean_closure_set(v___f_4208_, 2, v_inst_4179_);
lean_closure_set(v___f_4208_, 3, v_toBind_4175_);
lean_closure_set(v___f_4208_, 4, v___f_4207_);
lean_closure_set(v___f_4208_, 5, v_toPure_4173_);
lean_closure_set(v___f_4208_, 6, v___f_4207_);
v___x_4209_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4176_, v_inst_4193_, v_matcherName_4196_);
v___x_4210_ = lean_apply_4(v_toBind_4175_, lean_box(0), lean_box(0), v___x_4209_, v___f_4208_);
return v___x_4210_;
}
else
{
lean_object* v___f_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_dec(v_matcherName_4196_);
lean_dec_ref(v_inst_4193_);
lean_dec_ref(v_inst_4179_);
lean_dec_ref(v_inst_4176_);
v___f_4211_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4211_, 0, v___f_4206_);
v___x_4212_ = lean_unsigned_to_nat(0u);
v___x_4213_ = lean_apply_2(v_toPure_4173_, lean_box(0), v___x_4212_);
v___x_4214_ = lean_apply_4(v_toBind_4175_, lean_box(0), lean_box(0), v___x_4213_, v___f_4211_);
return v___x_4214_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg___lam__64_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_4172_ = stack[0].m_obj;
lean_object* v_toPure_4173_ = stack[1].m_obj;
lean_object* v_inst_4174_ = stack[2].m_obj;
lean_object* v_toBind_4175_ = stack[3].m_obj;
lean_object* v_inst_4176_ = stack[4].m_obj;
lean_object* v___f_4177_ = stack[5].m_obj;
lean_object* v_onMotive_4178_ = stack[6].m_obj;
lean_object* v_inst_4179_ = stack[7].m_obj;
lean_object* v_onRemaining_4180_ = stack[8].m_obj;
lean_object* v_inst_4181_ = stack[9].m_obj;
lean_object* v___f_4182_ = stack[10].m_obj;
lean_object* v_onAlt_4183_ = stack[11].m_obj;
lean_object* v___f_4184_ = stack[12].m_obj;
uint8_t v_useSplitter_4185_ = stack[13].m_num;
lean_object* v___f_4186_ = stack[14].m_obj;
lean_object* v___x_4187_ = stack[15].m_obj;
lean_object* v___x_4188_ = stack[16].m_obj;
lean_object* v_toMonadExceptOf_4189_ = stack[17].m_obj;
lean_object* v___f_4190_ = stack[18].m_obj;
lean_object* v___f_4191_ = stack[19].m_obj;
lean_object* v_onParams_4192_ = stack[20].m_obj;
lean_object* v_inst_4193_ = stack[21].m_obj;
lean_object* v_____do__lift_4194_ = stack[22].m_obj;
lean_object* v_res_4215_;
v_res_4215_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4172_, v_toPure_4173_, v_inst_4174_, v_toBind_4175_, v_inst_4176_, v___f_4177_, v_onMotive_4178_, v_inst_4179_, v_onRemaining_4180_, v_inst_4181_, v___f_4182_, v_onAlt_4183_, v___f_4184_, v_useSplitter_4185_, v___f_4186_, v___x_4187_, v___x_4188_, v_toMonadExceptOf_4189_, v___f_4190_, v___f_4191_, v_onParams_4192_, v_inst_4193_, v_____do__lift_4194_);
stack->m_obj
 = v_res_4215_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4216_ = _args[0];
lean_object* v_toPure_4217_ = _args[1];
lean_object* v_inst_4218_ = _args[2];
lean_object* v_toBind_4219_ = _args[3];
lean_object* v_inst_4220_ = _args[4];
lean_object* v___f_4221_ = _args[5];
lean_object* v_onMotive_4222_ = _args[6];
lean_object* v_inst_4223_ = _args[7];
lean_object* v_onRemaining_4224_ = _args[8];
lean_object* v_inst_4225_ = _args[9];
lean_object* v___f_4226_ = _args[10];
lean_object* v_onAlt_4227_ = _args[11];
lean_object* v___f_4228_ = _args[12];
lean_object* v_useSplitter_4229_ = _args[13];
lean_object* v___f_4230_ = _args[14];
lean_object* v___x_4231_ = _args[15];
lean_object* v___x_4232_ = _args[16];
lean_object* v_toMonadExceptOf_4233_ = _args[17];
lean_object* v___f_4234_ = _args[18];
lean_object* v___f_4235_ = _args[19];
lean_object* v_onParams_4236_ = _args[20];
lean_object* v_inst_4237_ = _args[21];
lean_object* v_____do__lift_4238_ = _args[22];
_start:
{
uint8_t v_useSplitter_boxed_4239_; lean_object* v_res_4240_; 
v_useSplitter_boxed_4239_ = lean_unbox(v_useSplitter_4229_);
v_res_4240_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4216_, v_toPure_4217_, v_inst_4218_, v_toBind_4219_, v_inst_4220_, v___f_4221_, v_onMotive_4222_, v_inst_4223_, v_onRemaining_4224_, v_inst_4225_, v___f_4226_, v_onAlt_4227_, v___f_4228_, v_useSplitter_boxed_4239_, v___f_4230_, v___x_4231_, v___x_4232_, v_toMonadExceptOf_4233_, v___f_4234_, v___f_4235_, v_onParams_4236_, v_inst_4237_, v_____do__lift_4238_);
return v_res_4240_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Subarray_empty___redArg();
return v___x_4241_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
return v___x_4243_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4244_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1);
v___x_4245_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
lean_ctor_set(v___x_4246_, 1, v___x_4244_);
return v___x_4246_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3(void){
_start:
{
lean_object* v___x_4247_; 
v___x_4247_ = l_Array_instInhabited___redArg();
return v___x_4247_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4(void){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4248_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2);
v___x_4249_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4249_);
lean_ctor_set(v___x_4250_, 1, v___x_4248_);
return v___x_4250_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5(void){
_start:
{
lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4);
v___x_4252_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4252_);
lean_ctor_set(v___x_4253_, 1, v___x_4251_);
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6(void){
_start:
{
lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4254_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5);
v___x_4255_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
lean_ctor_set(v___x_4256_, 1, v___x_4254_);
return v___x_4256_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7(void){
_start:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4257_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6);
v___x_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
return v___x_4258_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_inst_4263_, lean_object* v_matcherApp_4264_, uint8_t v_useSplitter_4265_, uint8_t v_addEqualities_4266_, lean_object* v_onParams_4267_, lean_object* v_onMotive_4268_, lean_object* v_onAlt_4269_, lean_object* v_onRemaining_4270_){
_start:
{
lean_object* v_toApplicative_4271_; lean_object* v_toBind_4272_; lean_object* v_getEnv_4273_; lean_object* v_toPure_4274_; lean_object* v_toMonadExceptOf_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___f_4278_; lean_object* v___f_4279_; lean_object* v___f_4280_; lean_object* v___x_4281_; lean_object* v___f_4282_; lean_object* v___x_4283_; lean_object* v___f_4284_; lean_object* v___f_4285_; lean_object* v___f_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___f_4289_; lean_object* v___x_4290_; 
v_toApplicative_4271_ = lean_ctor_get(v_inst_4261_, 0);
v_toBind_4272_ = lean_ctor_get(v_inst_4261_, 1);
lean_inc_n(v_toBind_4272_, 4);
v_getEnv_4273_ = lean_ctor_get(v_inst_4263_, 0);
lean_inc(v_getEnv_4273_);
v_toPure_4274_ = lean_ctor_get(v_toApplicative_4271_, 1);
lean_inc_n(v_toPure_4274_, 5);
v_toMonadExceptOf_4275_ = lean_ctor_get(v_inst_4262_, 0);
lean_inc_ref(v_toMonadExceptOf_4275_);
v___x_4276_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
lean_inc_ref_n(v_inst_4261_, 4);
v___x_4277_ = l_instInhabitedOfMonad___redArg(v_inst_4261_, v___x_4276_);
lean_inc_ref(v_inst_4262_);
v___f_4278_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4278_, 0, v_inst_4261_);
lean_closure_set(v___f_4278_, 1, v_inst_4262_);
lean_inc_n(v_inst_4259_, 3);
v___f_4279_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4279_, 0, v_inst_4259_);
v___f_4280_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4280_, 0, v_inst_4261_);
lean_closure_set(v___f_4280_, 1, v___f_4279_);
v___x_4281_ = l_Lean_instInhabitedExpr;
v___f_4282_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 6, 3);
lean_closure_set(v___f_4282_, 0, v_toPure_4274_);
lean_closure_set(v___f_4282_, 1, v_inst_4259_);
lean_closure_set(v___f_4282_, 2, v_toBind_4272_);
v___x_4283_ = lean_box(v_addEqualities_4266_);
v___f_4284_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4284_, 0, v_toPure_4274_);
lean_closure_set(v___f_4284_, 1, v___x_4283_);
lean_closure_set(v___f_4284_, 2, v_inst_4259_);
lean_closure_set(v___f_4284_, 3, v_toBind_4272_);
v___f_4285_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11), 2, 1);
lean_closure_set(v___f_4285_, 0, v_toPure_4274_);
v___f_4286_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 2, 1);
lean_closure_set(v___f_4286_, 0, v_toPure_4274_);
v___x_4287_ = l_instInhabitedOfMonad___redArg(v_inst_4261_, v___x_4281_);
v___x_4288_ = lean_box(v_useSplitter_4265_);
v___f_4289_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 23, 22);
lean_closure_set(v___f_4289_, 0, v_matcherApp_4264_);
lean_closure_set(v___f_4289_, 1, v_toPure_4274_);
lean_closure_set(v___f_4289_, 2, v_inst_4259_);
lean_closure_set(v___f_4289_, 3, v_toBind_4272_);
lean_closure_set(v___f_4289_, 4, v_inst_4261_);
lean_closure_set(v___f_4289_, 5, v___f_4284_);
lean_closure_set(v___f_4289_, 6, v_onMotive_4268_);
lean_closure_set(v___f_4289_, 7, v_inst_4262_);
lean_closure_set(v___f_4289_, 8, v_onRemaining_4270_);
lean_closure_set(v___f_4289_, 9, v_inst_4260_);
lean_closure_set(v___f_4289_, 10, v___f_4286_);
lean_closure_set(v___f_4289_, 11, v_onAlt_4269_);
lean_closure_set(v___f_4289_, 12, v___f_4280_);
lean_closure_set(v___f_4289_, 13, v___x_4288_);
lean_closure_set(v___f_4289_, 14, v___f_4285_);
lean_closure_set(v___f_4289_, 15, v___x_4277_);
lean_closure_set(v___f_4289_, 16, v___x_4287_);
lean_closure_set(v___f_4289_, 17, v_toMonadExceptOf_4275_);
lean_closure_set(v___f_4289_, 18, v___f_4278_);
lean_closure_set(v___f_4289_, 19, v___f_4282_);
lean_closure_set(v___f_4289_, 20, v_onParams_4267_);
lean_closure_set(v___f_4289_, 21, v_inst_4263_);
v___x_4290_ = lean_apply_4(v_toBind_4272_, lean_box(0), lean_box(0), v_getEnv_4273_, v___f_4289_);
return v___x_4290_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4259_ = stack[0].m_obj;
lean_object* v_inst_4260_ = stack[1].m_obj;
lean_object* v_inst_4261_ = stack[2].m_obj;
lean_object* v_inst_4262_ = stack[3].m_obj;
lean_object* v_inst_4263_ = stack[4].m_obj;
lean_object* v_matcherApp_4264_ = stack[5].m_obj;
uint8_t v_useSplitter_4265_ = stack[6].m_num;
uint8_t v_addEqualities_4266_ = stack[7].m_num;
lean_object* v_onParams_4267_ = stack[8].m_obj;
lean_object* v_onMotive_4268_ = stack[9].m_obj;
lean_object* v_onAlt_4269_ = stack[10].m_obj;
lean_object* v_onRemaining_4270_ = stack[11].m_obj;
lean_object* v_res_4291_;
v_res_4291_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4259_, v_inst_4260_, v_inst_4261_, v_inst_4262_, v_inst_4263_, v_matcherApp_4264_, v_useSplitter_4265_, v_addEqualities_4266_, v_onParams_4267_, v_onMotive_4268_, v_onAlt_4269_, v_onRemaining_4270_);
stack->m_obj
 = v_res_4291_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4292_, lean_object* v_inst_4293_, lean_object* v_inst_4294_, lean_object* v_inst_4295_, lean_object* v_inst_4296_, lean_object* v_matcherApp_4297_, lean_object* v_useSplitter_4298_, lean_object* v_addEqualities_4299_, lean_object* v_onParams_4300_, lean_object* v_onMotive_4301_, lean_object* v_onAlt_4302_, lean_object* v_onRemaining_4303_){
_start:
{
uint8_t v_useSplitter_boxed_4304_; uint8_t v_addEqualities_boxed_4305_; lean_object* v_res_4306_; 
v_useSplitter_boxed_4304_ = lean_unbox(v_useSplitter_4298_);
v_addEqualities_boxed_4305_ = lean_unbox(v_addEqualities_4299_);
v_res_4306_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4292_, v_inst_4293_, v_inst_4294_, v_inst_4295_, v_inst_4296_, v_matcherApp_4297_, v_useSplitter_boxed_4304_, v_addEqualities_boxed_4305_, v_onParams_4300_, v_onMotive_4301_, v_onAlt_4302_, v_onRemaining_4303_);
return v_res_4306_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4307_, lean_object* v_inst_4308_, lean_object* v_inst_4309_, lean_object* v_inst_4310_, lean_object* v_inst_4311_, lean_object* v_inst_4312_, lean_object* v_inst_4313_, lean_object* v_inst_4314_, lean_object* v_inst_4315_, lean_object* v_matcherApp_4316_, uint8_t v_useSplitter_4317_, uint8_t v_addEqualities_4318_, lean_object* v_onParams_4319_, lean_object* v_onMotive_4320_, lean_object* v_onAlt_4321_, lean_object* v_onRemaining_4322_){
_start:
{
lean_object* v___x_4323_; 
v___x_4323_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4308_, v_inst_4309_, v_inst_4310_, v_inst_4311_, v_inst_4312_, v_matcherApp_4316_, v_useSplitter_4317_, v_addEqualities_4318_, v_onParams_4319_, v_onMotive_4320_, v_onAlt_4321_, v_onRemaining_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_4308_ = stack[1].m_obj;
lean_object* v_inst_4309_ = stack[2].m_obj;
lean_object* v_inst_4310_ = stack[3].m_obj;
lean_object* v_inst_4311_ = stack[4].m_obj;
lean_object* v_inst_4312_ = stack[5].m_obj;
lean_object* v_inst_4313_ = stack[6].m_obj;
lean_object* v_inst_4314_ = stack[7].m_obj;
lean_object* v_inst_4315_ = stack[8].m_obj;
lean_object* v_matcherApp_4316_ = stack[9].m_obj;
uint8_t v_useSplitter_4317_ = stack[10].m_num;
uint8_t v_addEqualities_4318_ = stack[11].m_num;
lean_object* v_onParams_4319_ = stack[12].m_obj;
lean_object* v_onMotive_4320_ = stack[13].m_obj;
lean_object* v_onAlt_4321_ = stack[14].m_obj;
lean_object* v_onRemaining_4322_ = stack[15].m_obj;
lean_object* v_res_4324_;
v_res_4324_ = l_Lean_Meta_MatcherApp_transform(lean_box(0), v_inst_4308_, v_inst_4309_, v_inst_4310_, v_inst_4311_, v_inst_4312_, v_inst_4313_, v_inst_4314_, v_inst_4315_, v_matcherApp_4316_, v_useSplitter_4317_, v_addEqualities_4318_, v_onParams_4319_, v_onMotive_4320_, v_onAlt_4321_, v_onRemaining_4322_);
stack->m_obj
 = v_res_4324_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4325_, lean_object* v_inst_4326_, lean_object* v_inst_4327_, lean_object* v_inst_4328_, lean_object* v_inst_4329_, lean_object* v_inst_4330_, lean_object* v_inst_4331_, lean_object* v_inst_4332_, lean_object* v_inst_4333_, lean_object* v_matcherApp_4334_, lean_object* v_useSplitter_4335_, lean_object* v_addEqualities_4336_, lean_object* v_onParams_4337_, lean_object* v_onMotive_4338_, lean_object* v_onAlt_4339_, lean_object* v_onRemaining_4340_){
_start:
{
uint8_t v_useSplitter_boxed_4341_; uint8_t v_addEqualities_boxed_4342_; lean_object* v_res_4343_; 
v_useSplitter_boxed_4341_ = lean_unbox(v_useSplitter_4335_);
v_addEqualities_boxed_4342_ = lean_unbox(v_addEqualities_4336_);
v_res_4343_ = l_Lean_Meta_MatcherApp_transform(v_n_4325_, v_inst_4326_, v_inst_4327_, v_inst_4328_, v_inst_4329_, v_inst_4330_, v_inst_4331_, v_inst_4332_, v_inst_4333_, v_matcherApp_4334_, v_useSplitter_boxed_4341_, v_addEqualities_boxed_4342_, v_onParams_4337_, v_onMotive_4338_, v_onAlt_4339_, v_onRemaining_4340_);
lean_dec_ref(v_inst_4333_);
lean_dec(v_inst_4332_);
lean_dec_ref(v_inst_4331_);
return v_res_4343_;
}
}
lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4350_, 0, v___y_4344_);
return v___x_4350_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_inferMatchType___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4344_ = stack[0].m_obj;
lean_object* v___y_4345_ = stack[1].m_obj;
lean_object* v___y_4346_ = stack[2].m_obj;
lean_object* v___y_4347_ = stack[3].m_obj;
lean_object* v___y_4348_ = stack[4].m_obj;
lean_object* v_res_4351_;
v_res_4351_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
stack->m_obj
 = v_res_4351_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
return v_res_4358_;
}
}
lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___y_4359_);
return v___x_4365_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_inferMatchType___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_4359_ = stack[0].m_obj;
lean_object* v___y_4360_ = stack[1].m_obj;
lean_object* v___y_4361_ = stack[2].m_obj;
lean_object* v___y_4362_ = stack[3].m_obj;
lean_object* v___y_4363_ = stack[4].m_obj;
lean_object* v_res_4366_;
v_res_4366_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
stack->m_obj
 = v_res_4366_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, v___y_4371_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec(v___y_4369_);
lean_dec_ref(v___y_4368_);
return v_res_4373_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4374_, lean_object* v_opt_4375_){
_start:
{
lean_object* v_name_4376_; lean_object* v_defValue_4377_; lean_object* v_map_4378_; lean_object* v___x_4379_; 
v_name_4376_ = lean_ctor_get(v_opt_4375_, 0);
v_defValue_4377_ = lean_ctor_get(v_opt_4375_, 1);
v_map_4378_ = lean_ctor_get(v_opts_4374_, 0);
v___x_4379_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4378_, v_name_4376_);
if (lean_obj_tag(v___x_4379_) == 0)
{
uint8_t v___x_4380_; 
v___x_4380_ = lean_unbox(v_defValue_4377_);
return v___x_4380_;
}
else
{
lean_object* v_val_4381_; 
v_val_4381_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_val_4381_);
lean_dec_ref_known(v___x_4379_, 1);
if (lean_obj_tag(v_val_4381_) == 1)
{
uint8_t v_v_4382_; 
v_v_4382_ = lean_ctor_get_uint8(v_val_4381_, 0);
lean_dec_ref_known(v_val_4381_, 0);
return v_v_4382_;
}
else
{
uint8_t v___x_4383_; 
lean_dec(v_val_4381_);
v___x_4383_ = lean_unbox(v_defValue_4377_);
return v___x_4383_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_4374_ = stack[0].m_obj;
lean_object* v_opt_4375_ = stack[1].m_obj;
uint8_t v_res_4384_;
v_res_4384_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4374_, v_opt_4375_);
stack->m_num = v_res_4384_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4385_, lean_object* v_opt_4386_){
_start:
{
uint8_t v_res_4387_; lean_object* v_r_4388_; 
v_res_4387_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4385_, v_opt_4386_);
lean_dec_ref(v_opt_4386_);
lean_dec_ref(v_opts_4385_);
v_r_4388_ = lean_box(v_res_4387_);
return v_r_4388_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_4397_, uint8_t v___y_4398_, lean_object* v_x_4399_){
_start:
{
if (lean_obj_tag(v_x_4399_) == 1)
{
lean_object* v_pre_4400_; 
v_pre_4400_ = lean_ctor_get(v_x_4399_, 0);
switch(lean_obj_tag(v_pre_4400_))
{
case 1:
{
lean_object* v_pre_4401_; 
v_pre_4401_ = lean_ctor_get(v_pre_4400_, 0);
switch(lean_obj_tag(v_pre_4401_))
{
case 0:
{
lean_object* v_str_4402_; lean_object* v_str_4403_; lean_object* v___x_4404_; uint8_t v___x_4405_; 
v_str_4402_ = lean_ctor_get(v_x_4399_, 1);
v_str_4403_ = lean_ctor_get(v_pre_4400_, 1);
v___x_4404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4405_ = lean_string_dec_eq(v_str_4403_, v___x_4404_);
if (v___x_4405_ == 0)
{
lean_object* v___x_4406_; uint8_t v___x_4407_; 
v___x_4406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4407_ = lean_string_dec_eq(v_str_4403_, v___x_4406_);
if (v___x_4407_ == 0)
{
return v___x_4407_;
}
else
{
lean_object* v___x_4408_; uint8_t v___x_4409_; 
v___x_4408_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4409_ = lean_string_dec_eq(v_str_4402_, v___x_4408_);
if (v___x_4409_ == 0)
{
return v___x_4409_;
}
else
{
return v_suppressElabErrors_4397_;
}
}
}
else
{
lean_object* v___x_4410_; uint8_t v___x_4411_; 
v___x_4410_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4411_ = lean_string_dec_eq(v_str_4402_, v___x_4410_);
if (v___x_4411_ == 0)
{
return v___x_4411_;
}
else
{
return v_suppressElabErrors_4397_;
}
}
}
case 1:
{
lean_object* v_pre_4412_; 
v_pre_4412_ = lean_ctor_get(v_pre_4401_, 0);
if (lean_obj_tag(v_pre_4412_) == 0)
{
lean_object* v_str_4413_; lean_object* v_str_4414_; lean_object* v_str_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v_str_4413_ = lean_ctor_get(v_x_4399_, 1);
v_str_4414_ = lean_ctor_get(v_pre_4400_, 1);
v_str_4415_ = lean_ctor_get(v_pre_4401_, 1);
v___x_4416_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4417_ = lean_string_dec_eq(v_str_4415_, v___x_4416_);
if (v___x_4417_ == 0)
{
return v___x_4417_;
}
else
{
lean_object* v___x_4418_; uint8_t v___x_4419_; 
v___x_4418_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4419_ = lean_string_dec_eq(v_str_4414_, v___x_4418_);
if (v___x_4419_ == 0)
{
return v___x_4419_;
}
else
{
lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4420_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4421_ = lean_string_dec_eq(v_str_4413_, v___x_4420_);
if (v___x_4421_ == 0)
{
return v___x_4421_;
}
else
{
return v_suppressElabErrors_4397_;
}
}
}
}
else
{
return v___y_4398_;
}
}
default: 
{
return v___y_4398_;
}
}
}
case 0:
{
lean_object* v_str_4422_; lean_object* v___x_4423_; uint8_t v___x_4424_; 
v_str_4422_ = lean_ctor_get(v_x_4399_, 1);
v___x_4423_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4424_ = lean_string_dec_eq(v_str_4422_, v___x_4423_);
if (v___x_4424_ == 0)
{
return v___x_4424_;
}
else
{
return v_suppressElabErrors_4397_;
}
}
default: 
{
return v___y_4398_;
}
}
}
else
{
return v___y_4398_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_4397_ = stack[0].m_num;
uint8_t v___y_4398_ = stack[1].m_num;
lean_object* v_x_4399_ = stack[2].m_obj;
uint8_t v_res_4425_;
v_res_4425_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_4397_, v___y_4398_, v_x_4399_);
stack->m_num = v_res_4425_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_4426_, lean_object* v___y_4427_, lean_object* v_x_4428_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4429_; uint8_t v___y_32251__boxed_4430_; uint8_t v_res_4431_; lean_object* v_r_4432_; 
v_suppressElabErrors_boxed_4429_ = lean_unbox(v_suppressElabErrors_4426_);
v___y_32251__boxed_4430_ = lean_unbox(v___y_4427_);
v_res_4431_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_4429_, v___y_32251__boxed_4430_, v_x_4428_);
lean_dec(v_x_4428_);
v_r_4432_ = lean_box(v_res_4431_);
return v_r_4432_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4434_, lean_object* v_msgData_4435_, uint8_t v_severity_4436_, uint8_t v_isSilent_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; uint8_t v___y_4447_; lean_object* v___y_4448_; lean_object* v___y_4449_; uint8_t v___y_4450_; lean_object* v_toCold_4451_; lean_object* v___y_4452_; lean_object* v___y_4481_; lean_object* v___y_4482_; uint8_t v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; uint8_t v___y_4486_; uint8_t v___y_4487_; lean_object* v___y_4488_; uint8_t v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; uint8_t v___y_4511_; lean_object* v___y_4512_; uint8_t v___y_4513_; lean_object* v___y_4514_; uint8_t v___y_4518_; uint8_t v___y_4519_; uint8_t v___y_4520_; uint8_t v___x_4531_; uint8_t v___y_4533_; uint8_t v___y_4534_; uint8_t v___y_4535_; uint8_t v___y_4537_; uint8_t v___x_4545_; 
v___x_4531_ = 2;
v___x_4545_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4436_, v___x_4531_);
if (v___x_4545_ == 0)
{
v___y_4537_ = v___x_4545_;
goto v___jp_4536_;
}
else
{
uint8_t v___x_4546_; 
lean_inc_ref(v_msgData_4435_);
v___x_4546_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4435_);
v___y_4537_ = v___x_4546_;
goto v___jp_4536_;
}
v___jp_4443_:
{
lean_object* v_currNamespace_4453_; lean_object* v_openDecls_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v_env_4459_; lean_object* v_nextMacroScope_4460_; lean_object* v_ngen_4461_; lean_object* v_auxDeclNGen_4462_; lean_object* v_traceState_4463_; lean_object* v_cache_4464_; lean_object* v_recordedDeps_4465_; lean_object* v_messages_4466_; lean_object* v_infoState_4467_; lean_object* v_snapshotTasks_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4479_; 
v_currNamespace_4453_ = lean_ctor_get(v_toCold_4451_, 4);
v_openDecls_4454_ = lean_ctor_get(v_toCold_4451_, 5);
lean_inc(v_openDecls_4454_);
lean_inc(v_currNamespace_4453_);
v___x_4455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4455_, 0, v_currNamespace_4453_);
lean_ctor_set(v___x_4455_, 1, v_openDecls_4454_);
v___x_4456_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4456_, 0, v___x_4455_);
lean_ctor_set(v___x_4456_, 1, v___y_4445_);
lean_inc_ref(v___y_4448_);
lean_inc_ref(v___y_4449_);
v___x_4457_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4457_, 0, v___y_4449_);
lean_ctor_set(v___x_4457_, 1, v___y_4444_);
lean_ctor_set(v___x_4457_, 2, v___y_4446_);
lean_ctor_set(v___x_4457_, 3, v___y_4448_);
lean_ctor_set(v___x_4457_, 4, v___x_4456_);
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*5, v___y_4450_);
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*5 + 1, v___y_4447_);
lean_ctor_set_uint8(v___x_4457_, sizeof(void*)*5 + 2, v_isSilent_4437_);
v___x_4458_ = lean_st_ref_take(v___y_4452_);
v_env_4459_ = lean_ctor_get(v___x_4458_, 0);
v_nextMacroScope_4460_ = lean_ctor_get(v___x_4458_, 1);
v_ngen_4461_ = lean_ctor_get(v___x_4458_, 2);
v_auxDeclNGen_4462_ = lean_ctor_get(v___x_4458_, 3);
v_traceState_4463_ = lean_ctor_get(v___x_4458_, 4);
v_cache_4464_ = lean_ctor_get(v___x_4458_, 5);
v_recordedDeps_4465_ = lean_ctor_get(v___x_4458_, 6);
v_messages_4466_ = lean_ctor_get(v___x_4458_, 7);
v_infoState_4467_ = lean_ctor_get(v___x_4458_, 8);
v_snapshotTasks_4468_ = lean_ctor_get(v___x_4458_, 9);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4470_ = v___x_4458_;
v_isShared_4471_ = v_isSharedCheck_4479_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_snapshotTasks_4468_);
lean_inc(v_infoState_4467_);
lean_inc(v_messages_4466_);
lean_inc(v_recordedDeps_4465_);
lean_inc(v_cache_4464_);
lean_inc(v_traceState_4463_);
lean_inc(v_auxDeclNGen_4462_);
lean_inc(v_ngen_4461_);
lean_inc(v_nextMacroScope_4460_);
lean_inc(v_env_4459_);
lean_dec(v___x_4458_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4479_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4472_ = lean_box(0);
v___x_4473_ = l_Lean_MessageLog_add(v___x_4457_, v_messages_4466_);
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 7, v___x_4473_);
v___x_4475_ = v___x_4470_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_env_4459_);
lean_ctor_set(v_reuseFailAlloc_4478_, 1, v_nextMacroScope_4460_);
lean_ctor_set(v_reuseFailAlloc_4478_, 2, v_ngen_4461_);
lean_ctor_set(v_reuseFailAlloc_4478_, 3, v_auxDeclNGen_4462_);
lean_ctor_set(v_reuseFailAlloc_4478_, 4, v_traceState_4463_);
lean_ctor_set(v_reuseFailAlloc_4478_, 5, v_cache_4464_);
lean_ctor_set(v_reuseFailAlloc_4478_, 6, v_recordedDeps_4465_);
lean_ctor_set(v_reuseFailAlloc_4478_, 7, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4478_, 8, v_infoState_4467_);
lean_ctor_set(v_reuseFailAlloc_4478_, 9, v_snapshotTasks_4468_);
v___x_4475_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_st_ref_put(v___y_4452_, v___x_4475_);
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4472_);
return v___x_4477_;
}
}
}
v___jp_4480_:
{
lean_object* v_fileName_4489_; lean_object* v_fileMap_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4506_; 
v_fileName_4489_ = lean_ctor_get(v___y_4484_, 0);
v_fileMap_4490_ = lean_ctor_get(v___y_4484_, 1);
v___x_4491_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4435_);
v___x_4492_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4491_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
v_a_4493_ = lean_ctor_get(v___x_4492_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4492_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4495_ = v___x_4492_;
v_isShared_4496_ = v_isSharedCheck_4506_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4492_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4506_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
lean_inc_ref_n(v_fileMap_4490_, 2);
v___x_4497_ = l_Lean_FileMap_toPosition(v_fileMap_4490_, v___y_4485_);
lean_dec(v___y_4485_);
v___x_4498_ = l_Lean_FileMap_toPosition(v_fileMap_4490_, v___y_4488_);
lean_dec(v___y_4488_);
v___x_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4498_);
v___x_4500_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4483_ == 0)
{
lean_del_object(v___x_4495_);
lean_dec_ref(v___y_4482_);
v___y_4444_ = v___x_4497_;
v___y_4445_ = v_a_4493_;
v___y_4446_ = v___x_4499_;
v___y_4447_ = v___y_4486_;
v___y_4448_ = v___x_4500_;
v___y_4449_ = v_fileName_4489_;
v___y_4450_ = v___y_4487_;
v_toCold_4451_ = v___y_4481_;
v___y_4452_ = v___y_4441_;
goto v___jp_4443_;
}
else
{
uint8_t v___x_4501_; 
lean_inc(v_a_4493_);
v___x_4501_ = l_Lean_MessageData_hasTag(v___y_4482_, v_a_4493_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; lean_object* v___x_4504_; 
lean_dec_ref_known(v___x_4499_, 1);
lean_dec_ref(v___x_4497_);
lean_dec(v_a_4493_);
v___x_4502_ = lean_box(0);
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v___x_4502_);
v___x_4504_ = v___x_4495_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
else
{
lean_del_object(v___x_4495_);
v___y_4444_ = v___x_4497_;
v___y_4445_ = v_a_4493_;
v___y_4446_ = v___x_4499_;
v___y_4447_ = v___y_4486_;
v___y_4448_ = v___x_4500_;
v___y_4449_ = v_fileName_4489_;
v___y_4450_ = v___y_4487_;
v_toCold_4451_ = v___y_4481_;
v___y_4452_ = v___y_4441_;
goto v___jp_4443_;
}
}
}
}
v___jp_4507_:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_Syntax_getTailPos_x3f(v___y_4512_, v___y_4513_);
lean_dec(v___y_4512_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_inc(v___y_4514_);
v___y_4481_ = v___y_4509_;
v___y_4482_ = v___y_4510_;
v___y_4483_ = v___y_4508_;
v___y_4484_ = v___y_4509_;
v___y_4485_ = v___y_4514_;
v___y_4486_ = v___y_4511_;
v___y_4487_ = v___y_4513_;
v___y_4488_ = v___y_4514_;
goto v___jp_4480_;
}
else
{
lean_object* v_val_4516_; 
v_val_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_val_4516_);
lean_dec_ref_known(v___x_4515_, 1);
v___y_4481_ = v___y_4509_;
v___y_4482_ = v___y_4510_;
v___y_4483_ = v___y_4508_;
v___y_4484_ = v___y_4509_;
v___y_4485_ = v___y_4514_;
v___y_4486_ = v___y_4511_;
v___y_4487_ = v___y_4513_;
v___y_4488_ = v_val_4516_;
goto v___jp_4480_;
}
}
v___jp_4517_:
{
lean_object* v_toCold_4521_; lean_object* v_ref_4522_; uint8_t v_suppressElabErrors_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___f_4526_; lean_object* v_ref_4527_; lean_object* v___x_4528_; 
v_toCold_4521_ = lean_ctor_get(v___y_4440_, 0);
v_ref_4522_ = lean_ctor_get(v___y_4440_, 2);
v_suppressElabErrors_4523_ = lean_ctor_get_uint8(v___y_4440_, sizeof(void*)*3 + 2);
v___x_4524_ = lean_box(v_suppressElabErrors_4523_);
v___x_4525_ = lean_box(v___y_4518_);
v___f_4526_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4526_, 0, v___x_4524_);
lean_closure_set(v___f_4526_, 1, v___x_4525_);
v_ref_4527_ = l_Lean_replaceRef(v_ref_4434_, v_ref_4522_);
v___x_4528_ = l_Lean_Syntax_getPos_x3f(v_ref_4527_, v___y_4519_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v___x_4529_; 
v___x_4529_ = lean_unsigned_to_nat(0u);
v___y_4508_ = v_suppressElabErrors_4523_;
v___y_4509_ = v_toCold_4521_;
v___y_4510_ = v___f_4526_;
v___y_4511_ = v___y_4520_;
v___y_4512_ = v_ref_4527_;
v___y_4513_ = v___y_4519_;
v___y_4514_ = v___x_4529_;
goto v___jp_4507_;
}
else
{
lean_object* v_val_4530_; 
v_val_4530_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_val_4530_);
lean_dec_ref_known(v___x_4528_, 1);
v___y_4508_ = v_suppressElabErrors_4523_;
v___y_4509_ = v_toCold_4521_;
v___y_4510_ = v___f_4526_;
v___y_4511_ = v___y_4520_;
v___y_4512_ = v_ref_4527_;
v___y_4513_ = v___y_4519_;
v___y_4514_ = v_val_4530_;
goto v___jp_4507_;
}
}
v___jp_4532_:
{
if (v___y_4535_ == 0)
{
v___y_4518_ = v___y_4533_;
v___y_4519_ = v___y_4534_;
v___y_4520_ = v_severity_4436_;
goto v___jp_4517_;
}
else
{
v___y_4518_ = v___y_4533_;
v___y_4519_ = v___y_4534_;
v___y_4520_ = v___x_4531_;
goto v___jp_4517_;
}
}
v___jp_4536_:
{
if (v___y_4537_ == 0)
{
uint8_t v___x_4538_; uint8_t v___x_4539_; 
v___x_4538_ = 1;
v___x_4539_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4436_, v___x_4538_);
if (v___x_4539_ == 0)
{
v___y_4533_ = v___y_4537_;
v___y_4534_ = v___y_4537_;
v___y_4535_ = v___x_4539_;
goto v___jp_4532_;
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4540_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4440_);
v___x_4541_ = l_Lean_warningAsError;
v___x_4542_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v___x_4540_, v___x_4541_);
lean_dec_ref(v___x_4540_);
v___y_4533_ = v___y_4537_;
v___y_4534_ = v___y_4537_;
v___y_4535_ = v___x_4542_;
goto v___jp_4532_;
}
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
lean_dec_ref(v_msgData_4435_);
v___x_4543_ = lean_box(0);
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___x_4543_);
return v___x_4544_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_4434_ = stack[0].m_obj;
lean_object* v_msgData_4435_ = stack[1].m_obj;
uint8_t v_severity_4436_ = stack[2].m_num;
uint8_t v_isSilent_4437_ = stack[3].m_num;
lean_object* v___y_4438_ = stack[4].m_obj;
lean_object* v___y_4439_ = stack[5].m_obj;
lean_object* v___y_4440_ = stack[6].m_obj;
lean_object* v___y_4441_ = stack[7].m_obj;
lean_object* v_res_4547_;
v_res_4547_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4434_, v_msgData_4435_, v_severity_4436_, v_isSilent_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
stack->m_obj
 = v_res_4547_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4548_, lean_object* v_msgData_4549_, lean_object* v_severity_4550_, lean_object* v_isSilent_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
uint8_t v_severity_boxed_4557_; uint8_t v_isSilent_boxed_4558_; lean_object* v_res_4559_; 
v_severity_boxed_4557_ = lean_unbox(v_severity_4550_);
v_isSilent_boxed_4558_ = lean_unbox(v_isSilent_4551_);
v_res_4559_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4548_, v_msgData_4549_, v_severity_boxed_4557_, v_isSilent_boxed_4558_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v_ref_4548_);
return v_res_4559_;
}
}
lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4560_, uint8_t v_severity_4561_, uint8_t v_isSilent_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_ref_4568_; lean_object* v___x_4569_; 
v_ref_4568_ = lean_ctor_get(v___y_4565_, 2);
v___x_4569_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4568_, v_msgData_4560_, v_severity_4561_, v_isSilent_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
return v___x_4569_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4560_ = stack[0].m_obj;
uint8_t v_severity_4561_ = stack[1].m_num;
uint8_t v_isSilent_4562_ = stack[2].m_num;
lean_object* v___y_4563_ = stack[3].m_obj;
lean_object* v___y_4564_ = stack[4].m_obj;
lean_object* v___y_4565_ = stack[5].m_obj;
lean_object* v___y_4566_ = stack[6].m_obj;
lean_object* v_res_4570_;
v_res_4570_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4560_, v_severity_4561_, v_isSilent_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
stack->m_obj
 = v_res_4570_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4571_, lean_object* v_severity_4572_, lean_object* v_isSilent_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
uint8_t v_severity_boxed_4579_; uint8_t v_isSilent_boxed_4580_; lean_object* v_res_4581_; 
v_severity_boxed_4579_ = lean_unbox(v_severity_4572_);
v_isSilent_boxed_4580_ = lean_unbox(v_isSilent_4573_);
v_res_4581_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4571_, v_severity_boxed_4579_, v_isSilent_boxed_4580_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
return v_res_4581_;
}
}
lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
uint8_t v___x_4588_; uint8_t v___x_4589_; lean_object* v___x_4590_; 
v___x_4588_ = 0;
v___x_4589_ = 0;
v___x_4590_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4582_, v___x_4588_, v___x_4589_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
return v___x_4590_;
}
}
LEAN_EXPORT void l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_4582_ = stack[0].m_obj;
lean_object* v___y_4583_ = stack[1].m_obj;
lean_object* v___y_4584_ = stack[2].m_obj;
lean_object* v___y_4585_ = stack[3].m_obj;
lean_object* v___y_4586_ = stack[4].m_obj;
lean_object* v_res_4591_;
v_res_4591_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
stack->m_obj
 = v_res_4591_;
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v_res_4598_; 
v_res_4598_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec_ref(v___y_4593_);
return v_res_4598_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4600_; lean_object* v___x_4601_; 
v___x_4600_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4601_ = l_Lean_stringToMessageData(v___x_4600_);
return v___x_4601_;
}
}
lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4602_, lean_object* v___altIdx_4603_, lean_object* v_expAltType_4604_, lean_object* v___altFVars_4605_, lean_object* v_alt_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
lean_object* v___x_4612_; 
lean_inc(v___y_4610_);
lean_inc_ref(v___y_4609_);
lean_inc(v___y_4608_);
lean_inc_ref(v___y_4607_);
lean_inc_ref(v_alt_4606_);
v___x_4612_ = lean_infer_type(v_alt_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
if (lean_obj_tag(v___x_4612_) == 0)
{
lean_object* v_a_4613_; lean_object* v___x_4614_; 
v_a_4613_ = lean_ctor_get(v___x_4612_, 0);
lean_inc(v_a_4613_);
lean_dec_ref_known(v___x_4612_, 1);
v___x_4614_ = l_Lean_Meta_mkEq(v_expAltType_4604_, v_a_4613_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
lean_inc(v_a_4615_);
lean_dec_ref_known(v___x_4614_, 1);
v___x_4616_ = lean_box(0);
v___x_4617_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4615_, v___x_4616_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_object* v_a_4618_; lean_object* v___y_4620_; lean_object* v___x_4630_; lean_object* v___x_4631_; 
v_a_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc(v_a_4618_);
lean_dec_ref_known(v___x_4617_, 1);
v___x_4630_ = l_Lean_Expr_mvarId_x21(v_a_4618_);
v___x_4631_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4630_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; lean_object* v___x_4633_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc_n(v_a_4632_, 2);
lean_dec_ref_known(v___x_4631_, 1);
v___x_4633_ = l_Lean_MVarId_refl(v_a_4632_, v___x_4602_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_dec(v_a_4632_);
v___y_4620_ = v___x_4633_;
goto v___jp_4619_;
}
else
{
lean_object* v_a_4634_; uint8_t v___y_4636_; uint8_t v___x_4649_; 
v_a_4634_ = lean_ctor_get(v___x_4633_, 0);
v___x_4649_ = l_Lean_Exception_isInterrupt(v_a_4634_);
if (v___x_4649_ == 0)
{
uint8_t v___x_4650_; 
lean_inc(v_a_4634_);
v___x_4650_ = l_Lean_Exception_isRuntime(v_a_4634_);
v___y_4636_ = v___x_4650_;
goto v___jp_4635_;
}
else
{
v___y_4636_ = v___x_4649_;
goto v___jp_4635_;
}
v___jp_4635_:
{
if (v___y_4636_ == 0)
{
lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4647_; 
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4633_);
if (v_isSharedCheck_4647_ == 0)
{
lean_object* v_unused_4648_; 
v_unused_4648_ = lean_ctor_get(v___x_4633_, 0);
lean_dec(v_unused_4648_);
v___x_4638_ = v___x_4633_;
v_isShared_4639_ = v_isSharedCheck_4647_;
goto v_resetjp_4637_;
}
else
{
lean_dec(v___x_4633_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4647_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4640_; lean_object* v___x_4642_; 
v___x_4640_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4632_);
if (v_isShared_4639_ == 0)
{
lean_ctor_set(v___x_4638_, 0, v_a_4632_);
v___x_4642_ = v___x_4638_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4646_; 
v_reuseFailAlloc_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4646_, 0, v_a_4632_);
v___x_4642_ = v_reuseFailAlloc_4646_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4640_);
lean_ctor_set(v___x_4643_, 1, v___x_4642_);
v___x_4644_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4643_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
if (lean_obj_tag(v___x_4644_) == 0)
{
lean_object* v___x_4645_; 
lean_dec_ref_known(v___x_4644_, 1);
v___x_4645_ = l_Lean_MVarId_admit(v_a_4632_, v___x_4602_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
v___y_4620_ = v___x_4645_;
goto v___jp_4619_;
}
else
{
lean_dec(v_a_4632_);
v___y_4620_ = v___x_4644_;
goto v___jp_4619_;
}
}
}
}
else
{
lean_dec(v_a_4632_);
v___y_4620_ = v___x_4633_;
goto v___jp_4619_;
}
}
}
}
else
{
lean_object* v_a_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4658_; 
lean_dec(v_a_4618_);
lean_dec_ref(v_alt_4606_);
v_a_4651_ = lean_ctor_get(v___x_4631_, 0);
v_isSharedCheck_4658_ = !lean_is_exclusive(v___x_4631_);
if (v_isSharedCheck_4658_ == 0)
{
v___x_4653_ = v___x_4631_;
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_a_4651_);
lean_dec(v___x_4631_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4658_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
lean_object* v___x_4656_; 
if (v_isShared_4654_ == 0)
{
v___x_4656_ = v___x_4653_;
goto v_reusejp_4655_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_a_4651_);
v___x_4656_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4655_;
}
v_reusejp_4655_:
{
return v___x_4656_;
}
}
}
v___jp_4619_:
{
if (lean_obj_tag(v___y_4620_) == 0)
{
lean_object* v___x_4621_; 
lean_dec_ref_known(v___y_4620_, 1);
v___x_4621_ = l_Lean_Meta_mkEqMPR(v_a_4618_, v_alt_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
return v___x_4621_;
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
lean_dec(v_a_4618_);
lean_dec_ref(v_alt_4606_);
v_a_4622_ = lean_ctor_get(v___y_4620_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___y_4620_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___y_4620_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___y_4620_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4606_);
return v___x_4617_;
}
}
else
{
lean_dec_ref(v_alt_4606_);
return v___x_4614_;
}
}
else
{
lean_dec_ref(v_alt_4606_);
lean_dec_ref(v_expAltType_4604_);
return v___x_4612_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_inferMatchType___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_4602_ = stack[0].m_num;
lean_object* v___altIdx_4603_ = stack[1].m_obj;
lean_object* v_expAltType_4604_ = stack[2].m_obj;
lean_object* v___altFVars_4605_ = stack[3].m_obj;
lean_object* v_alt_4606_ = stack[4].m_obj;
lean_object* v___y_4607_ = stack[5].m_obj;
lean_object* v___y_4608_ = stack[6].m_obj;
lean_object* v___y_4609_ = stack[7].m_obj;
lean_object* v___y_4610_ = stack[8].m_obj;
lean_object* v_res_4659_;
v_res_4659_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_4602_, v___altIdx_4603_, v_expAltType_4604_, v___altFVars_4605_, v_alt_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
stack->m_obj
 = v_res_4659_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4660_, lean_object* v___altIdx_4661_, lean_object* v_expAltType_4662_, lean_object* v___altFVars_4663_, lean_object* v_alt_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
uint8_t v___x_32712__boxed_4670_; lean_object* v_res_4671_; 
v___x_32712__boxed_4670_ = lean_unbox(v___x_4660_);
v_res_4671_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32712__boxed_4670_, v___altIdx_4661_, v_expAltType_4662_, v___altFVars_4663_, v_alt_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec_ref(v___altFVars_4663_);
lean_dec(v___altIdx_4661_);
return v_res_4671_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4672_, lean_object* v_e_4673_){
_start:
{
uint8_t v___x_4674_; lean_object* v_d_4676_; lean_object* v_b_4677_; 
v___x_4674_ = l_Lean_Expr_hasFVar(v_e_4673_);
if (v___x_4674_ == 0)
{
return v___x_4674_;
}
else
{
switch(lean_obj_tag(v_e_4673_))
{
case 7:
{
lean_object* v_binderType_4680_; lean_object* v_body_4681_; 
v_binderType_4680_ = lean_ctor_get(v_e_4673_, 1);
v_body_4681_ = lean_ctor_get(v_e_4673_, 2);
v_d_4676_ = v_binderType_4680_;
v_b_4677_ = v_body_4681_;
goto v___jp_4675_;
}
case 6:
{
lean_object* v_binderType_4682_; lean_object* v_body_4683_; 
v_binderType_4682_ = lean_ctor_get(v_e_4673_, 1);
v_body_4683_ = lean_ctor_get(v_e_4673_, 2);
v_d_4676_ = v_binderType_4682_;
v_b_4677_ = v_body_4683_;
goto v___jp_4675_;
}
case 10:
{
lean_object* v_expr_4684_; 
v_expr_4684_ = lean_ctor_get(v_e_4673_, 1);
v_e_4673_ = v_expr_4684_;
goto _start;
}
case 8:
{
lean_object* v_type_4686_; lean_object* v_value_4687_; lean_object* v_body_4688_; uint8_t v___x_4689_; 
v_type_4686_ = lean_ctor_get(v_e_4673_, 1);
v_value_4687_ = lean_ctor_get(v_e_4673_, 2);
v_body_4688_ = lean_ctor_get(v_e_4673_, 3);
v___x_4689_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4672_, v_type_4686_);
if (v___x_4689_ == 0)
{
uint8_t v___x_4690_; 
v___x_4690_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4672_, v_value_4687_);
if (v___x_4690_ == 0)
{
v_e_4673_ = v_body_4688_;
goto _start;
}
else
{
return v___x_4674_;
}
}
else
{
return v___x_4674_;
}
}
case 5:
{
lean_object* v_fn_4692_; lean_object* v_arg_4693_; uint8_t v___x_4694_; 
v_fn_4692_ = lean_ctor_get(v_e_4673_, 0);
v_arg_4693_ = lean_ctor_get(v_e_4673_, 1);
v___x_4694_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4672_, v_fn_4692_);
if (v___x_4694_ == 0)
{
v_e_4673_ = v_arg_4693_;
goto _start;
}
else
{
return v___x_4674_;
}
}
case 11:
{
lean_object* v_struct_4696_; 
v_struct_4696_ = lean_ctor_get(v_e_4673_, 2);
v_e_4673_ = v_struct_4696_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4698_; lean_object* v___x_4699_; uint8_t v___x_4700_; 
v_fvarId_4698_ = lean_ctor_get(v_e_4673_, 0);
v___x_4699_ = l_Lean_Expr_fvarId_x21(v___x_4672_);
v___x_4700_ = l_Lean_instBEqFVarId_beq(v_fvarId_4698_, v___x_4699_);
lean_dec(v___x_4699_);
return v___x_4700_;
}
default: 
{
uint8_t v___x_4701_; 
v___x_4701_ = 0;
return v___x_4701_;
}
}
}
v___jp_4675_:
{
uint8_t v___x_4678_; 
v___x_4678_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4672_, v_d_4676_);
if (v___x_4678_ == 0)
{
v_e_4673_ = v_b_4677_;
goto _start;
}
else
{
return v___x_4674_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4672_ = stack[0].m_obj;
lean_object* v_e_4673_ = stack[1].m_obj;
uint8_t v_res_4702_;
v_res_4702_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4672_, v_e_4673_);
stack->m_num = v_res_4702_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4703_, lean_object* v_e_4704_){
_start:
{
uint8_t v_res_4705_; lean_object* v_r_4706_; 
v_res_4705_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4703_, v_e_4704_);
lean_dec_ref(v_e_4704_);
lean_dec_ref(v___x_4703_);
v_r_4706_ = lean_box(v_res_4705_);
return v_r_4706_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
v___x_4708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4709_ = l_Lean_stringToMessageData(v___x_4708_);
return v___x_4709_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4712_ = l_Lean_stringToMessageData(v___x_4711_);
return v___x_4712_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4714_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4715_ = l_Lean_stringToMessageData(v___x_4714_);
return v___x_4715_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4716_, lean_object* v_termAlt_4717_, lean_object* v_a_4718_, lean_object* v_b_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_){
_start:
{
lean_object* v_array_4725_; lean_object* v_start_4726_; lean_object* v_stop_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4755_; 
v_array_4725_ = lean_ctor_get(v_a_4718_, 0);
v_start_4726_ = lean_ctor_get(v_a_4718_, 1);
v_stop_4727_ = lean_ctor_get(v_a_4718_, 2);
v_isSharedCheck_4755_ = !lean_is_exclusive(v_a_4718_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4729_ = v_a_4718_;
v_isShared_4730_ = v_isSharedCheck_4755_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_stop_4727_);
lean_inc(v_start_4726_);
lean_inc(v_array_4725_);
lean_dec(v_a_4718_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4755_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
uint8_t v___x_4731_; 
v___x_4731_ = lean_nat_dec_lt(v_start_4726_, v_stop_4727_);
if (v___x_4731_ == 0)
{
lean_object* v___x_4732_; 
lean_del_object(v___x_4729_);
lean_dec(v_stop_4727_);
lean_dec(v_start_4726_);
lean_dec_ref(v_array_4725_);
lean_dec_ref(v_termAlt_4717_);
lean_dec_ref(v_a_4716_);
v___x_4732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4732_, 0, v_b_4719_);
return v___x_4732_;
}
else
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4737_; 
v___x_4733_ = lean_box(0);
v___x_4734_ = lean_unsigned_to_nat(1u);
v___x_4735_ = lean_nat_add(v_start_4726_, v___x_4734_);
lean_inc_ref(v_array_4725_);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 1, v___x_4735_);
v___x_4737_ = v___x_4729_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_array_4725_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v___x_4735_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_stop_4727_);
v___x_4737_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
lean_object* v___x_4738_; uint8_t v___x_4739_; 
v___x_4738_ = lean_array_fget(v_array_4725_, v_start_4726_);
lean_dec(v_start_4726_);
lean_dec_ref(v_array_4725_);
v___x_4739_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4738_, v_a_4716_);
if (v___x_4739_ == 0)
{
lean_dec(v___x_4738_);
v_a_4718_ = v___x_4737_;
v_b_4719_ = v___x_4733_;
goto _start;
}
else
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4741_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4716_);
v___x_4742_ = l_Lean_MessageData_ofExpr(v_a_4716_);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
v___x_4744_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4743_);
lean_ctor_set(v___x_4745_, 1, v___x_4744_);
lean_inc_ref(v_termAlt_4717_);
v___x_4746_ = l_Lean_MessageData_ofExpr(v_termAlt_4717_);
v___x_4747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4747_, 0, v___x_4745_);
lean_ctor_set(v___x_4747_, 1, v___x_4746_);
v___x_4748_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4747_);
lean_ctor_set(v___x_4749_, 1, v___x_4748_);
v___x_4750_ = l_Lean_MessageData_ofExpr(v___x_4738_);
v___x_4751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4749_);
lean_ctor_set(v___x_4751_, 1, v___x_4750_);
v___x_4752_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4751_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_dec_ref_known(v___x_4752_, 1);
v_a_4718_ = v___x_4737_;
v_b_4719_ = v___x_4733_;
goto _start;
}
else
{
lean_dec_ref(v___x_4737_);
lean_dec_ref(v_termAlt_4717_);
lean_dec_ref(v_a_4716_);
return v___x_4752_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_4716_ = stack[0].m_obj;
lean_object* v_termAlt_4717_ = stack[1].m_obj;
lean_object* v_a_4718_ = stack[2].m_obj;
lean_object* v_b_4719_ = stack[3].m_obj;
lean_object* v___y_4720_ = stack[4].m_obj;
lean_object* v___y_4721_ = stack[5].m_obj;
lean_object* v___y_4722_ = stack[6].m_obj;
lean_object* v___y_4723_ = stack[7].m_obj;
lean_object* v_res_4756_;
v_res_4756_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4716_, v_termAlt_4717_, v_a_4718_, v_b_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_);
stack->m_obj
 = v_res_4756_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4757_, lean_object* v_termAlt_4758_, lean_object* v_a_4759_, lean_object* v_b_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v_res_4766_; 
v_res_4766_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4757_, v_termAlt_4758_, v_a_4759_, v_b_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
return v_res_4766_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4767_, lean_object* v_v_4768_, uint8_t v___x_4769_, uint8_t v___x_4770_, uint8_t v___x_4771_, lean_object* v_xs_4772_, lean_object* v_termAltBody_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4779_ = lean_array_get_size(v_xs_4772_);
v___x_4780_ = lean_nat_sub(v___x_4779_, v_nExtra_4767_);
v___x_4781_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4780_);
lean_inc_ref(v_xs_4772_);
v___x_4782_ = l_Array_toSubarray___redArg(v_xs_4772_, v___x_4781_, v___x_4780_);
v___x_4783_ = l_Array_toSubarray___redArg(v_xs_4772_, v___x_4780_, v___x_4779_);
lean_inc(v___y_4777_);
lean_inc_ref(v___y_4776_);
lean_inc(v___y_4775_);
lean_inc_ref(v___y_4774_);
v___x_4784_ = lean_infer_type(v_termAltBody_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc_n(v_a_4785_, 2);
lean_dec_ref_known(v___x_4784_, 1);
v___x_4786_ = lean_box(0);
v___x_4787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4785_, v_v_4768_, v___x_4783_, v___x_4786_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
lean_dec_ref_known(v___x_4787_, 1);
v___x_4788_ = l_Subarray_copy___redArg(v___x_4782_);
v___x_4789_ = l_Lean_Meta_mkLambdaFVars(v___x_4788_, v_a_4785_, v___x_4769_, v___x_4770_, v___x_4769_, v___x_4770_, v___x_4771_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
lean_dec_ref(v___x_4788_);
return v___x_4789_;
}
else
{
lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec(v_a_4785_);
lean_dec_ref(v___x_4782_);
v_a_4790_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4787_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4787_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
}
else
{
lean_dec_ref(v___x_4783_);
lean_dec_ref(v___x_4782_);
lean_dec(v_v_4768_);
return v___x_4784_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_nExtra_4767_ = stack[0].m_obj;
lean_object* v_v_4768_ = stack[1].m_obj;
uint8_t v___x_4769_ = stack[2].m_num;
uint8_t v___x_4770_ = stack[3].m_num;
uint8_t v___x_4771_ = stack[4].m_num;
lean_object* v_xs_4772_ = stack[5].m_obj;
lean_object* v_termAltBody_4773_ = stack[6].m_obj;
lean_object* v___y_4774_ = stack[7].m_obj;
lean_object* v___y_4775_ = stack[8].m_obj;
lean_object* v___y_4776_ = stack[9].m_obj;
lean_object* v___y_4777_ = stack[10].m_obj;
lean_object* v_res_4798_;
v_res_4798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4767_, v_v_4768_, v___x_4769_, v___x_4770_, v___x_4771_, v_xs_4772_, v_termAltBody_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_);
stack->m_obj
 = v_res_4798_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4799_, lean_object* v_v_4800_, lean_object* v___x_4801_, lean_object* v___x_4802_, lean_object* v___x_4803_, lean_object* v_xs_4804_, lean_object* v_termAltBody_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_){
_start:
{
uint8_t v___x_33140__boxed_4811_; uint8_t v___x_33141__boxed_4812_; uint8_t v___x_33142__boxed_4813_; lean_object* v_res_4814_; 
v___x_33140__boxed_4811_ = lean_unbox(v___x_4801_);
v___x_33141__boxed_4812_ = lean_unbox(v___x_4802_);
v___x_33142__boxed_4813_ = lean_unbox(v___x_4803_);
v_res_4814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4799_, v_v_4800_, v___x_33140__boxed_4811_, v___x_33141__boxed_4812_, v___x_33142__boxed_4813_, v_xs_4804_, v_termAltBody_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_);
lean_dec(v___y_4809_);
lean_dec_ref(v___y_4808_);
lean_dec(v___y_4807_);
lean_dec_ref(v___y_4806_);
lean_dec(v_nExtra_4799_);
return v_res_4814_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4815_, size_t v_sz_4816_, size_t v_i_4817_, lean_object* v_bs_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
uint8_t v___x_4824_; 
v___x_4824_ = lean_usize_dec_lt(v_i_4817_, v_sz_4816_);
if (v___x_4824_ == 0)
{
lean_object* v___x_4825_; 
lean_dec(v_nExtra_4815_);
v___x_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4825_, 0, v_bs_4818_);
return v___x_4825_;
}
else
{
uint8_t v___x_4826_; uint8_t v___x_4827_; lean_object* v_v_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___f_4832_; lean_object* v___x_4833_; lean_object* v_bs_x27_4834_; lean_object* v___x_4835_; 
v___x_4826_ = 0;
v___x_4827_ = 1;
v_v_4828_ = lean_array_uget(v_bs_4818_, v_i_4817_);
v___x_4829_ = lean_box(v___x_4826_);
v___x_4830_ = lean_box(v___x_4824_);
v___x_4831_ = lean_box(v___x_4827_);
lean_inc(v_v_4828_);
lean_inc(v_nExtra_4815_);
v___f_4832_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4832_, 0, v_nExtra_4815_);
lean_closure_set(v___f_4832_, 1, v_v_4828_);
lean_closure_set(v___f_4832_, 2, v___x_4829_);
lean_closure_set(v___f_4832_, 3, v___x_4830_);
lean_closure_set(v___f_4832_, 4, v___x_4831_);
v___x_4833_ = lean_unsigned_to_nat(0u);
v_bs_x27_4834_ = lean_array_uset(v_bs_4818_, v_i_4817_, v___x_4833_);
v___x_4835_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4828_, v___f_4832_, v___x_4826_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; size_t v___x_4837_; size_t v___x_4838_; lean_object* v___x_4839_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref_known(v___x_4835_, 1);
v___x_4837_ = ((size_t)1ULL);
v___x_4838_ = lean_usize_add(v_i_4817_, v___x_4837_);
v___x_4839_ = lean_array_uset(v_bs_x27_4834_, v_i_4817_, v_a_4836_);
v_i_4817_ = v___x_4838_;
v_bs_4818_ = v___x_4839_;
goto _start;
}
else
{
lean_object* v_a_4841_; lean_object* v___x_4843_; uint8_t v_isShared_4844_; uint8_t v_isSharedCheck_4848_; 
lean_dec_ref(v_bs_x27_4834_);
lean_dec(v_nExtra_4815_);
v_a_4841_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4848_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4848_ == 0)
{
v___x_4843_ = v___x_4835_;
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
else
{
lean_inc(v_a_4841_);
lean_dec(v___x_4835_);
v___x_4843_ = lean_box(0);
v_isShared_4844_ = v_isSharedCheck_4848_;
goto v_resetjp_4842_;
}
v_resetjp_4842_:
{
lean_object* v___x_4846_; 
if (v_isShared_4844_ == 0)
{
v___x_4846_ = v___x_4843_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4841_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_nExtra_4815_ = stack[0].m_obj;
size_t v_sz_4816_ = stack[1].m_num;
size_t v_i_4817_ = stack[2].m_num;
lean_object* v_bs_4818_ = stack[3].m_obj;
lean_object* v___y_4819_ = stack[4].m_obj;
lean_object* v___y_4820_ = stack[5].m_obj;
lean_object* v___y_4821_ = stack[6].m_obj;
lean_object* v___y_4822_ = stack[7].m_obj;
lean_object* v_res_4849_;
v_res_4849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4815_, v_sz_4816_, v_i_4817_, v_bs_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
stack->m_obj
 = v_res_4849_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4850_, lean_object* v_sz_4851_, lean_object* v_i_4852_, lean_object* v_bs_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
size_t v_sz_boxed_4859_; size_t v_i_boxed_4860_; lean_object* v_res_4861_; 
v_sz_boxed_4859_ = lean_unbox_usize(v_sz_4851_);
lean_dec(v_sz_4851_);
v_i_boxed_4860_ = lean_unbox_usize(v_i_4852_);
lean_dec(v_i_4852_);
v_res_4861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4850_, v_sz_boxed_4859_, v_i_boxed_4860_, v_bs_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec_ref(v___y_4854_);
return v_res_4861_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = lean_box(0);
v___x_4863_ = l_Lean_Expr_sort___override(v___x_4862_);
return v___x_4863_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4864_; lean_object* v___x_4865_; 
v___x_4864_ = lean_box(0);
v___x_4865_ = l_Lean_Level_succ___override(v___x_4864_);
return v___x_4865_;
}
}
lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4866_, uint8_t v___x_4867_, uint8_t v___x_4868_, lean_object* v_alts_4869_, lean_object* v_toMatcherInfo_4870_, lean_object* v_matcherName_4871_, lean_object* v_params_4872_, lean_object* v_matcherLevels_4873_, lean_object* v_motiveArgs_4874_, lean_object* v_body_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v___x_4881_; 
lean_inc(v_nExtra_4866_);
v___x_4881_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4866_, v_body_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4883_; uint8_t v___x_4884_; lean_object* v___x_4885_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___x_4881_, 1);
v___x_4883_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4884_ = 1;
v___x_4885_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4874_, v___x_4883_, v___x_4867_, v___x_4868_, v___x_4867_, v___x_4868_, v___x_4884_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; size_t v_sz_4887_; size_t v___x_4888_; lean_object* v___x_4889_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref_known(v___x_4885_, 1);
v_sz_4887_ = lean_array_size(v_alts_4869_);
v___x_4888_ = ((size_t)0ULL);
v___x_4889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4866_, v_sz_4887_, v___x_4888_, v_alts_4869_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v_matcherLevels_4892_; lean_object* v___y_4893_; lean_object* v___y_4894_; lean_object* v_uElimPos_x3f_4899_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v_uElimPos_x3f_4899_ = lean_ctor_get(v_toMatcherInfo_4870_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4899_) == 0)
{
v_matcherLevels_4892_ = v_matcherLevels_4873_;
v___y_4893_ = v___y_4878_;
v___y_4894_ = v___y_4879_;
goto v___jp_4891_;
}
else
{
lean_object* v_val_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v_val_4900_ = lean_ctor_get(v_uElimPos_x3f_4899_, 0);
v___x_4901_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4902_ = lean_array_set(v_matcherLevels_4873_, v_val_4900_, v___x_4901_);
v_matcherLevels_4892_ = v___x_4902_;
v___y_4893_ = v___y_4878_;
v___y_4894_ = v___y_4879_;
goto v___jp_4891_;
}
v___jp_4891_:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4895_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4896_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4896_, 0, v_toMatcherInfo_4870_);
lean_ctor_set(v___x_4896_, 1, v_matcherName_4871_);
lean_ctor_set(v___x_4896_, 2, v_matcherLevels_4892_);
lean_ctor_set(v___x_4896_, 3, v_params_4872_);
lean_ctor_set(v___x_4896_, 4, v_a_4886_);
lean_ctor_set(v___x_4896_, 5, v_motiveArgs_4874_);
lean_ctor_set(v___x_4896_, 6, v_a_4890_);
lean_ctor_set(v___x_4896_, 7, v___x_4895_);
v___x_4897_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4896_);
v___x_4898_ = l_Lean_mkArrowN(v_a_4882_, v___x_4897_, v___y_4893_, v___y_4894_);
lean_dec(v_a_4882_);
return v___x_4898_;
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v_a_4886_);
lean_dec(v_a_4882_);
lean_dec_ref(v_motiveArgs_4874_);
lean_dec_ref(v_matcherLevels_4873_);
lean_dec_ref(v_params_4872_);
lean_dec(v_matcherName_4871_);
lean_dec_ref(v_toMatcherInfo_4870_);
v_a_4903_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4889_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4889_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
else
{
lean_dec(v_a_4882_);
lean_dec_ref(v_motiveArgs_4874_);
lean_dec_ref(v_matcherLevels_4873_);
lean_dec_ref(v_params_4872_);
lean_dec(v_matcherName_4871_);
lean_dec_ref(v_toMatcherInfo_4870_);
lean_dec_ref(v_alts_4869_);
lean_dec(v_nExtra_4866_);
return v___x_4885_;
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
lean_dec_ref(v_motiveArgs_4874_);
lean_dec_ref(v_matcherLevels_4873_);
lean_dec_ref(v_params_4872_);
lean_dec(v_matcherName_4871_);
lean_dec_ref(v_toMatcherInfo_4870_);
lean_dec_ref(v_alts_4869_);
lean_dec(v_nExtra_4866_);
v_a_4911_ = lean_ctor_get(v___x_4881_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4913_ = v___x_4881_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4881_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_inferMatchType___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_nExtra_4866_ = stack[0].m_obj;
uint8_t v___x_4867_ = stack[1].m_num;
uint8_t v___x_4868_ = stack[2].m_num;
lean_object* v_alts_4869_ = stack[3].m_obj;
lean_object* v_toMatcherInfo_4870_ = stack[4].m_obj;
lean_object* v_matcherName_4871_ = stack[5].m_obj;
lean_object* v_params_4872_ = stack[6].m_obj;
lean_object* v_matcherLevels_4873_ = stack[7].m_obj;
lean_object* v_motiveArgs_4874_ = stack[8].m_obj;
lean_object* v_body_4875_ = stack[9].m_obj;
lean_object* v___y_4876_ = stack[10].m_obj;
lean_object* v___y_4877_ = stack[11].m_obj;
lean_object* v___y_4878_ = stack[12].m_obj;
lean_object* v___y_4879_ = stack[13].m_obj;
lean_object* v_res_4919_;
v_res_4919_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4866_, v___x_4867_, v___x_4868_, v_alts_4869_, v_toMatcherInfo_4870_, v_matcherName_4871_, v_params_4872_, v_matcherLevels_4873_, v_motiveArgs_4874_, v_body_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_);
stack->m_obj
 = v_res_4919_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4920_, lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v_alts_4923_, lean_object* v_toMatcherInfo_4924_, lean_object* v_matcherName_4925_, lean_object* v_params_4926_, lean_object* v_matcherLevels_4927_, lean_object* v_motiveArgs_4928_, lean_object* v_body_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
uint8_t v___x_33343__boxed_4935_; uint8_t v___x_33344__boxed_4936_; lean_object* v_res_4937_; 
v___x_33343__boxed_4935_ = lean_unbox(v___x_4921_);
v___x_33344__boxed_4936_ = lean_unbox(v___x_4922_);
v_res_4937_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4920_, v___x_33343__boxed_4935_, v___x_33344__boxed_4936_, v_alts_4923_, v_toMatcherInfo_4924_, v_matcherName_4925_, v_params_4926_, v_matcherLevels_4927_, v_motiveArgs_4928_, v_body_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
return v_res_4937_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4938_, lean_object* v_ys_4939_, lean_object* v_args_4940_, lean_object* v___mask_4941_, lean_object* v___bodyType_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v___x_4948_; 
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
lean_inc(v___y_4944_);
lean_inc_ref(v___y_4943_);
v___x_4948_ = lean_apply_7(v_k_4938_, v_ys_4939_, v_args_4940_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, lean_box(0));
return v___x_4948_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_4938_ = stack[0].m_obj;
lean_object* v_ys_4939_ = stack[1].m_obj;
lean_object* v_args_4940_ = stack[2].m_obj;
lean_object* v___mask_4941_ = stack[3].m_obj;
lean_object* v___bodyType_4942_ = stack[4].m_obj;
lean_object* v___y_4943_ = stack[5].m_obj;
lean_object* v___y_4944_ = stack[6].m_obj;
lean_object* v___y_4945_ = stack[7].m_obj;
lean_object* v___y_4946_ = stack[8].m_obj;
lean_object* v_res_4949_;
v_res_4949_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4938_, v_ys_4939_, v_args_4940_, v___mask_4941_, v___bodyType_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
stack->m_obj
 = v_res_4949_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4950_, lean_object* v_ys_4951_, lean_object* v_args_4952_, lean_object* v___mask_4953_, lean_object* v___bodyType_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
lean_object* v_res_4960_; 
v_res_4960_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4950_, v_ys_4951_, v_args_4952_, v___mask_4953_, v___bodyType_4954_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_);
lean_dec(v___y_4958_);
lean_dec_ref(v___y_4957_);
lean_dec(v___y_4956_);
lean_dec_ref(v___y_4955_);
lean_dec_ref(v___bodyType_4954_);
lean_dec_ref(v___mask_4953_);
return v_res_4960_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4961_, lean_object* v_altInfo_4962_, lean_object* v_k_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
lean_object* v___f_4969_; lean_object* v___x_4970_; 
v___f_4969_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4969_, 0, v_k_4963_);
v___x_4970_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4961_, v_altInfo_4962_, v___f_4969_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_4978_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_4978_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_4978_ == 0)
{
v___x_4973_ = v___x_4970_;
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_a_4971_);
lean_dec(v___x_4970_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_4978_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4976_; 
if (v_isShared_4974_ == 0)
{
v___x_4976_ = v___x_4973_;
goto v_reusejp_4975_;
}
else
{
lean_object* v_reuseFailAlloc_4977_; 
v_reuseFailAlloc_4977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4977_, 0, v_a_4971_);
v___x_4976_ = v_reuseFailAlloc_4977_;
goto v_reusejp_4975_;
}
v_reusejp_4975_:
{
return v___x_4976_;
}
}
}
else
{
lean_object* v_a_4979_; lean_object* v___x_4981_; uint8_t v_isShared_4982_; uint8_t v_isSharedCheck_4986_; 
v_a_4979_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_4986_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_4986_ == 0)
{
v___x_4981_ = v___x_4970_;
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
else
{
lean_inc(v_a_4979_);
lean_dec(v___x_4970_);
v___x_4981_ = lean_box(0);
v_isShared_4982_ = v_isSharedCheck_4986_;
goto v_resetjp_4980_;
}
v_resetjp_4980_:
{
lean_object* v___x_4984_; 
if (v_isShared_4982_ == 0)
{
v___x_4984_ = v___x_4981_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_4985_; 
v_reuseFailAlloc_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4985_, 0, v_a_4979_);
v___x_4984_ = v_reuseFailAlloc_4985_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
return v___x_4984_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_origAltType_4961_ = stack[0].m_obj;
lean_object* v_altInfo_4962_ = stack[1].m_obj;
lean_object* v_k_4963_ = stack[2].m_obj;
lean_object* v___y_4964_ = stack[3].m_obj;
lean_object* v___y_4965_ = stack[4].m_obj;
lean_object* v___y_4966_ = stack[5].m_obj;
lean_object* v___y_4967_ = stack[6].m_obj;
lean_object* v_res_4987_;
v_res_4987_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4961_, v_altInfo_4962_, v_k_4963_, v___y_4964_, v___y_4965_, v___y_4966_, v___y_4967_);
stack->m_obj
 = v_res_4987_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4988_, lean_object* v_altInfo_4989_, lean_object* v_k_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_){
_start:
{
lean_object* v_res_4996_; 
v_res_4996_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4988_, v_altInfo_4989_, v_k_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
lean_dec(v___y_4994_);
lean_dec_ref(v___y_4993_);
lean_dec(v___y_4992_);
lean_dec_ref(v___y_4991_);
return v_res_4996_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4997_, lean_object* v___x_4998_, lean_object* v___f_4999_, lean_object* v_fst_5000_, lean_object* v___x_5001_, lean_object* v___x_5002_, lean_object* v___x_5003_, lean_object* v___x_5004_, lean_object* v___x_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_){
_start:
{
lean_object* v___x_5011_; 
v___x_5011_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4997_, v___x_4998_, v___f_4999_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5026_; 
v_a_5012_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5014_ = v___x_5011_;
v_isShared_5015_ = v_isSharedCheck_5026_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_5011_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5026_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5024_; 
v___x_5016_ = lean_array_push(v_fst_5000_, v_a_5012_);
v___x_5017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5017_, 0, v___x_5001_);
lean_ctor_set(v___x_5017_, 1, v___x_5002_);
v___x_5018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5003_);
lean_ctor_set(v___x_5018_, 1, v___x_5017_);
v___x_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5004_);
lean_ctor_set(v___x_5019_, 1, v___x_5018_);
v___x_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5020_, 0, v___x_5005_);
lean_ctor_set(v___x_5020_, 1, v___x_5019_);
v___x_5021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5016_);
lean_ctor_set(v___x_5021_, 1, v___x_5020_);
v___x_5022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5022_, 0, v___x_5021_);
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v___x_5022_);
v___x_5024_ = v___x_5014_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
else
{
lean_object* v_a_5027_; lean_object* v___x_5029_; uint8_t v_isShared_5030_; uint8_t v_isSharedCheck_5034_; 
lean_dec_ref(v___x_5005_);
lean_dec_ref(v___x_5004_);
lean_dec_ref(v___x_5003_);
lean_dec_ref(v___x_5002_);
lean_dec_ref(v___x_5001_);
lean_dec(v_fst_5000_);
v_a_5027_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5034_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5034_ == 0)
{
v___x_5029_ = v___x_5011_;
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
else
{
lean_inc(v_a_5027_);
lean_dec(v___x_5011_);
v___x_5029_ = lean_box(0);
v_isShared_5030_ = v_isSharedCheck_5034_;
goto v_resetjp_5028_;
}
v_resetjp_5028_:
{
lean_object* v___x_5032_; 
if (v_isShared_5030_ == 0)
{
v___x_5032_ = v___x_5029_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_a_5027_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
return v___x_5032_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4997_ = stack[0].m_obj;
lean_object* v___x_4998_ = stack[1].m_obj;
lean_object* v___f_4999_ = stack[2].m_obj;
lean_object* v_fst_5000_ = stack[3].m_obj;
lean_object* v___x_5001_ = stack[4].m_obj;
lean_object* v___x_5002_ = stack[5].m_obj;
lean_object* v___x_5003_ = stack[6].m_obj;
lean_object* v___x_5004_ = stack[7].m_obj;
lean_object* v___x_5005_ = stack[8].m_obj;
lean_object* v___y_5006_ = stack[9].m_obj;
lean_object* v___y_5007_ = stack[10].m_obj;
lean_object* v___y_5008_ = stack[11].m_obj;
lean_object* v___y_5009_ = stack[12].m_obj;
lean_object* v_res_5035_;
v_res_5035_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4997_, v___x_4998_, v___f_4999_, v_fst_5000_, v___x_5001_, v___x_5002_, v___x_5003_, v___x_5004_, v___x_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
stack->m_obj
 = v_res_5035_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_5036_, lean_object* v___x_5037_, lean_object* v___f_5038_, lean_object* v_fst_5039_, lean_object* v___x_5040_, lean_object* v___x_5041_, lean_object* v___x_5042_, lean_object* v___x_5043_, lean_object* v___x_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_){
_start:
{
lean_object* v_res_5050_; 
v_res_5050_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_5036_, v___x_5037_, v___f_5038_, v_fst_5039_, v___x_5040_, v___x_5041_, v___x_5042_, v___x_5043_, v___x_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
lean_dec(v___y_5048_);
lean_dec_ref(v___y_5047_);
lean_dec(v___y_5046_);
lean_dec_ref(v___y_5045_);
return v_res_5050_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_5051_, lean_object* v_ys_5052_, lean_object* v_ys2_5053_, lean_object* v_ys3_5054_, lean_object* v_onAlt_5055_, lean_object* v_a_5056_, uint8_t v___x_5057_, uint8_t v_useSplitter_5058_, lean_object* v___x_5059_, lean_object* v_ys4_5060_, lean_object* v_altType_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v___y_5068_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
lean_inc_ref(v_args_5051_);
v___x_5078_ = l_Array_append___redArg(v_args_5051_, v_ys3_5054_);
v___x_5079_ = l_Lean_Meta_instantiateLambda(v___x_5059_, v___x_5078_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
lean_dec_ref(v___x_5078_);
if (lean_obj_tag(v___x_5079_) == 0)
{
v___y_5068_ = v___x_5079_;
goto v___jp_5067_;
}
else
{
lean_object* v_a_5080_; uint8_t v___y_5082_; uint8_t v___x_5085_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
v___x_5085_ = l_Lean_Exception_isInterrupt(v_a_5080_);
if (v___x_5085_ == 0)
{
uint8_t v___x_5086_; 
lean_inc(v_a_5080_);
v___x_5086_ = l_Lean_Exception_isRuntime(v_a_5080_);
v___y_5082_ = v___x_5086_;
goto v___jp_5081_;
}
else
{
v___y_5082_ = v___x_5085_;
goto v___jp_5081_;
}
v___jp_5081_:
{
if (v___y_5082_ == 0)
{
lean_object* v___x_5083_; lean_object* v___x_5084_; 
lean_dec_ref_known(v___x_5079_, 1);
v___x_5083_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_5084_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5083_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
v___y_5068_ = v___x_5084_;
goto v___jp_5067_;
}
else
{
v___y_5068_ = v___x_5079_;
goto v___jp_5067_;
}
}
}
v___jp_5067_:
{
if (lean_obj_tag(v___y_5068_) == 0)
{
lean_object* v_a_5069_; lean_object* v___x_5070_; lean_object* v___x_5071_; 
v_a_5069_ = lean_ctor_get(v___y_5068_, 0);
lean_inc(v_a_5069_);
lean_dec_ref_known(v___y_5068_, 1);
lean_inc_ref(v_ys4_5060_);
lean_inc_ref(v_ys3_5054_);
lean_inc_ref(v_ys2_5053_);
lean_inc_ref(v_ys_5052_);
v___x_5070_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5070_, 0, v_args_5051_);
lean_ctor_set(v___x_5070_, 1, v_ys_5052_);
lean_ctor_set(v___x_5070_, 2, v_ys2_5053_);
lean_ctor_set(v___x_5070_, 3, v_ys3_5054_);
lean_ctor_set(v___x_5070_, 4, v_ys4_5060_);
lean_inc(v___y_5065_);
lean_inc_ref(v___y_5064_);
lean_inc(v___y_5063_);
lean_inc_ref(v___y_5062_);
v___x_5071_ = lean_apply_9(v_onAlt_5055_, v_a_5056_, v_altType_5061_, v___x_5070_, v_a_5069_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, lean_box(0));
if (lean_obj_tag(v___x_5071_) == 0)
{
lean_object* v_a_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; uint8_t v___x_5076_; lean_object* v___x_5077_; 
v_a_5072_ = lean_ctor_get(v___x_5071_, 0);
lean_inc(v_a_5072_);
lean_dec_ref_known(v___x_5071_, 1);
v___x_5073_ = l_Array_append___redArg(v_ys_5052_, v_ys2_5053_);
lean_dec_ref(v_ys2_5053_);
v___x_5074_ = l_Array_append___redArg(v___x_5073_, v_ys3_5054_);
lean_dec_ref(v_ys3_5054_);
v___x_5075_ = l_Array_append___redArg(v___x_5074_, v_ys4_5060_);
lean_dec_ref(v_ys4_5060_);
v___x_5076_ = 1;
v___x_5077_ = l_Lean_Meta_mkLambdaFVars(v___x_5075_, v_a_5072_, v___x_5057_, v_useSplitter_5058_, v___x_5057_, v_useSplitter_5058_, v___x_5076_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
lean_dec_ref(v___x_5075_);
return v___x_5077_;
}
else
{
lean_dec_ref(v_ys4_5060_);
lean_dec_ref(v_ys3_5054_);
lean_dec_ref(v_ys2_5053_);
lean_dec_ref(v_ys_5052_);
return v___x_5071_;
}
}
else
{
lean_dec_ref(v_altType_5061_);
lean_dec_ref(v_ys4_5060_);
lean_dec(v_a_5056_);
lean_dec_ref(v_onAlt_5055_);
lean_dec_ref(v_ys3_5054_);
lean_dec_ref(v_ys2_5053_);
lean_dec_ref(v_ys_5052_);
lean_dec_ref(v_args_5051_);
return v___y_5068_;
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_5051_ = stack[0].m_obj;
lean_object* v_ys_5052_ = stack[1].m_obj;
lean_object* v_ys2_5053_ = stack[2].m_obj;
lean_object* v_ys3_5054_ = stack[3].m_obj;
lean_object* v_onAlt_5055_ = stack[4].m_obj;
lean_object* v_a_5056_ = stack[5].m_obj;
uint8_t v___x_5057_ = stack[6].m_num;
uint8_t v_useSplitter_5058_ = stack[7].m_num;
lean_object* v___x_5059_ = stack[8].m_obj;
lean_object* v_ys4_5060_ = stack[9].m_obj;
lean_object* v_altType_5061_ = stack[10].m_obj;
lean_object* v___y_5062_ = stack[11].m_obj;
lean_object* v___y_5063_ = stack[12].m_obj;
lean_object* v___y_5064_ = stack[13].m_obj;
lean_object* v___y_5065_ = stack[14].m_obj;
lean_object* v_res_5087_;
v_res_5087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5051_, v_ys_5052_, v_ys2_5053_, v_ys3_5054_, v_onAlt_5055_, v_a_5056_, v___x_5057_, v_useSplitter_5058_, v___x_5059_, v_ys4_5060_, v_altType_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_);
stack->m_obj
 = v_res_5087_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5088_, lean_object* v_ys_5089_, lean_object* v_ys2_5090_, lean_object* v_ys3_5091_, lean_object* v_onAlt_5092_, lean_object* v_a_5093_, lean_object* v___x_5094_, lean_object* v_useSplitter_5095_, lean_object* v___x_5096_, lean_object* v_ys4_5097_, lean_object* v_altType_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
uint8_t v___x_33739__boxed_5104_; uint8_t v_useSplitter_boxed_5105_; lean_object* v_res_5106_; 
v___x_33739__boxed_5104_ = lean_unbox(v___x_5094_);
v_useSplitter_boxed_5105_ = lean_unbox(v_useSplitter_5095_);
v_res_5106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5088_, v_ys_5089_, v_ys2_5090_, v_ys3_5091_, v_onAlt_5092_, v_a_5093_, v___x_33739__boxed_5104_, v_useSplitter_boxed_5105_, v___x_5096_, v_ys4_5097_, v_altType_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
lean_dec(v___y_5100_);
lean_dec_ref(v___y_5099_);
return v_res_5106_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5107_, lean_object* v_ys_5108_, lean_object* v_ys2_5109_, lean_object* v_onAlt_5110_, lean_object* v_a_5111_, uint8_t v___x_5112_, uint8_t v_useSplitter_5113_, lean_object* v___x_5114_, lean_object* v_extraEqualities_5115_, lean_object* v_ys3_5116_, lean_object* v_altType_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___f_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5123_ = lean_box(v___x_5112_);
v___x_5124_ = lean_box(v_useSplitter_5113_);
v___f_5125_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5125_, 0, v_args_5107_);
lean_closure_set(v___f_5125_, 1, v_ys_5108_);
lean_closure_set(v___f_5125_, 2, v_ys2_5109_);
lean_closure_set(v___f_5125_, 3, v_ys3_5116_);
lean_closure_set(v___f_5125_, 4, v_onAlt_5110_);
lean_closure_set(v___f_5125_, 5, v_a_5111_);
lean_closure_set(v___f_5125_, 6, v___x_5123_);
lean_closure_set(v___f_5125_, 7, v___x_5124_);
lean_closure_set(v___f_5125_, 8, v___x_5114_);
v___x_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5126_, 0, v_extraEqualities_5115_);
v___x_5127_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5117_, v___x_5126_, v___f_5125_, v___x_5112_, v___x_5112_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
return v___x_5127_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_5107_ = stack[0].m_obj;
lean_object* v_ys_5108_ = stack[1].m_obj;
lean_object* v_ys2_5109_ = stack[2].m_obj;
lean_object* v_onAlt_5110_ = stack[3].m_obj;
lean_object* v_a_5111_ = stack[4].m_obj;
uint8_t v___x_5112_ = stack[5].m_num;
uint8_t v_useSplitter_5113_ = stack[6].m_num;
lean_object* v___x_5114_ = stack[7].m_obj;
lean_object* v_extraEqualities_5115_ = stack[8].m_obj;
lean_object* v_ys3_5116_ = stack[9].m_obj;
lean_object* v_altType_5117_ = stack[10].m_obj;
lean_object* v___y_5118_ = stack[11].m_obj;
lean_object* v___y_5119_ = stack[12].m_obj;
lean_object* v___y_5120_ = stack[13].m_obj;
lean_object* v___y_5121_ = stack[14].m_obj;
lean_object* v_res_5128_;
v_res_5128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5107_, v_ys_5108_, v_ys2_5109_, v_onAlt_5110_, v_a_5111_, v___x_5112_, v_useSplitter_5113_, v___x_5114_, v_extraEqualities_5115_, v_ys3_5116_, v_altType_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
stack->m_obj
 = v_res_5128_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5129_, lean_object* v_ys_5130_, lean_object* v_ys2_5131_, lean_object* v_onAlt_5132_, lean_object* v_a_5133_, lean_object* v___x_5134_, lean_object* v_useSplitter_5135_, lean_object* v___x_5136_, lean_object* v_extraEqualities_5137_, lean_object* v_ys3_5138_, lean_object* v_altType_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_){
_start:
{
uint8_t v___x_33838__boxed_5145_; uint8_t v_useSplitter_boxed_5146_; lean_object* v_res_5147_; 
v___x_33838__boxed_5145_ = lean_unbox(v___x_5134_);
v_useSplitter_boxed_5146_ = lean_unbox(v_useSplitter_5135_);
v_res_5147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5129_, v_ys_5130_, v_ys2_5131_, v_onAlt_5132_, v_a_5133_, v___x_33838__boxed_5145_, v_useSplitter_boxed_5146_, v___x_5136_, v_extraEqualities_5137_, v_ys3_5138_, v_altType_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_);
lean_dec(v___y_5143_);
lean_dec_ref(v___y_5142_);
lean_dec(v___y_5141_);
lean_dec_ref(v___y_5140_);
return v_res_5147_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5148_, lean_object* v_ys_5149_, lean_object* v_onAlt_5150_, lean_object* v_a_5151_, uint8_t v___x_5152_, uint8_t v_useSplitter_5153_, lean_object* v___x_5154_, lean_object* v_extraEqualities_5155_, lean_object* v_numDiscrEqs_5156_, lean_object* v_ys2_5157_, lean_object* v_altType_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_){
_start:
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___f_5166_; lean_object* v___x_5167_; lean_object* v___x_5168_; 
v___x_5164_ = lean_box(v___x_5152_);
v___x_5165_ = lean_box(v_useSplitter_5153_);
v___f_5166_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5166_, 0, v_args_5148_);
lean_closure_set(v___f_5166_, 1, v_ys_5149_);
lean_closure_set(v___f_5166_, 2, v_ys2_5157_);
lean_closure_set(v___f_5166_, 3, v_onAlt_5150_);
lean_closure_set(v___f_5166_, 4, v_a_5151_);
lean_closure_set(v___f_5166_, 5, v___x_5164_);
lean_closure_set(v___f_5166_, 6, v___x_5165_);
lean_closure_set(v___f_5166_, 7, v___x_5154_);
lean_closure_set(v___f_5166_, 8, v_extraEqualities_5155_);
v___x_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5167_, 0, v_numDiscrEqs_5156_);
v___x_5168_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5158_, v___x_5167_, v___f_5166_, v___x_5152_, v___x_5152_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
return v___x_5168_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_args_5148_ = stack[0].m_obj;
lean_object* v_ys_5149_ = stack[1].m_obj;
lean_object* v_onAlt_5150_ = stack[2].m_obj;
lean_object* v_a_5151_ = stack[3].m_obj;
uint8_t v___x_5152_ = stack[4].m_num;
uint8_t v_useSplitter_5153_ = stack[5].m_num;
lean_object* v___x_5154_ = stack[6].m_obj;
lean_object* v_extraEqualities_5155_ = stack[7].m_obj;
lean_object* v_numDiscrEqs_5156_ = stack[8].m_obj;
lean_object* v_ys2_5157_ = stack[9].m_obj;
lean_object* v_altType_5158_ = stack[10].m_obj;
lean_object* v___y_5159_ = stack[11].m_obj;
lean_object* v___y_5160_ = stack[12].m_obj;
lean_object* v___y_5161_ = stack[13].m_obj;
lean_object* v___y_5162_ = stack[14].m_obj;
lean_object* v_res_5169_;
v_res_5169_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5148_, v_ys_5149_, v_onAlt_5150_, v_a_5151_, v___x_5152_, v_useSplitter_5153_, v___x_5154_, v_extraEqualities_5155_, v_numDiscrEqs_5156_, v_ys2_5157_, v_altType_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
stack->m_obj
 = v_res_5169_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5170_, lean_object* v_ys_5171_, lean_object* v_onAlt_5172_, lean_object* v_a_5173_, lean_object* v___x_5174_, lean_object* v_useSplitter_5175_, lean_object* v___x_5176_, lean_object* v_extraEqualities_5177_, lean_object* v_numDiscrEqs_5178_, lean_object* v_ys2_5179_, lean_object* v_altType_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_, lean_object* v___y_5185_){
_start:
{
uint8_t v___x_33888__boxed_5186_; uint8_t v_useSplitter_boxed_5187_; lean_object* v_res_5188_; 
v___x_33888__boxed_5186_ = lean_unbox(v___x_5174_);
v_useSplitter_boxed_5187_ = lean_unbox(v_useSplitter_5175_);
v_res_5188_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5170_, v_ys_5171_, v_onAlt_5172_, v_a_5173_, v___x_33888__boxed_5186_, v_useSplitter_boxed_5187_, v___x_5176_, v_extraEqualities_5177_, v_numDiscrEqs_5178_, v_ys2_5179_, v_altType_5180_, v___y_5181_, v___y_5182_, v___y_5183_, v___y_5184_);
lean_dec(v___y_5184_);
lean_dec_ref(v___y_5183_);
lean_dec(v___y_5182_);
lean_dec_ref(v___y_5181_);
return v_res_5188_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0(void){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l_instMonadEIO___redArg();
return v___x_5189_;
}
}
lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_){
_start:
{
lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v_toApplicative_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5263_; 
v___x_5200_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5201_ = l_StateRefT_x27_instMonad___redArg(v___x_5200_);
v_toApplicative_5202_ = lean_ctor_get(v___x_5201_, 0);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5201_);
if (v_isSharedCheck_5263_ == 0)
{
lean_object* v_unused_5264_; 
v_unused_5264_ = lean_ctor_get(v___x_5201_, 1);
lean_dec(v_unused_5264_);
v___x_5204_ = v___x_5201_;
v_isShared_5205_ = v_isSharedCheck_5263_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_toApplicative_5202_);
lean_dec(v___x_5201_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5263_;
goto v_resetjp_5203_;
}
v_resetjp_5203_:
{
lean_object* v_toFunctor_5206_; lean_object* v_toSeq_5207_; lean_object* v_toSeqLeft_5208_; lean_object* v_toSeqRight_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5261_; 
v_toFunctor_5206_ = lean_ctor_get(v_toApplicative_5202_, 0);
v_toSeq_5207_ = lean_ctor_get(v_toApplicative_5202_, 2);
v_toSeqLeft_5208_ = lean_ctor_get(v_toApplicative_5202_, 3);
v_toSeqRight_5209_ = lean_ctor_get(v_toApplicative_5202_, 4);
v_isSharedCheck_5261_ = !lean_is_exclusive(v_toApplicative_5202_);
if (v_isSharedCheck_5261_ == 0)
{
lean_object* v_unused_5262_; 
v_unused_5262_ = lean_ctor_get(v_toApplicative_5202_, 1);
lean_dec(v_unused_5262_);
v___x_5211_ = v_toApplicative_5202_;
v_isShared_5212_ = v_isSharedCheck_5261_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_toSeqRight_5209_);
lean_inc(v_toSeqLeft_5208_);
lean_inc(v_toSeq_5207_);
lean_inc(v_toFunctor_5206_);
lean_dec(v_toApplicative_5202_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5261_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___f_5213_; lean_object* v___f_5214_; lean_object* v___f_5215_; lean_object* v___f_5216_; lean_object* v___x_5217_; lean_object* v___f_5218_; lean_object* v___f_5219_; lean_object* v___f_5220_; lean_object* v___x_5222_; 
v___f_5213_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5214_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5206_);
v___f_5215_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5215_, 0, v_toFunctor_5206_);
v___f_5216_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5216_, 0, v_toFunctor_5206_);
v___x_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___f_5215_);
lean_ctor_set(v___x_5217_, 1, v___f_5216_);
v___f_5218_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5218_, 0, v_toSeqRight_5209_);
v___f_5219_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5219_, 0, v_toSeqLeft_5208_);
v___f_5220_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5220_, 0, v_toSeq_5207_);
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 4, v___f_5218_);
lean_ctor_set(v___x_5211_, 3, v___f_5219_);
lean_ctor_set(v___x_5211_, 2, v___f_5220_);
lean_ctor_set(v___x_5211_, 1, v___f_5213_);
lean_ctor_set(v___x_5211_, 0, v___x_5217_);
v___x_5222_ = v___x_5211_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5217_);
lean_ctor_set(v_reuseFailAlloc_5260_, 1, v___f_5213_);
lean_ctor_set(v_reuseFailAlloc_5260_, 2, v___f_5220_);
lean_ctor_set(v_reuseFailAlloc_5260_, 3, v___f_5219_);
lean_ctor_set(v_reuseFailAlloc_5260_, 4, v___f_5218_);
v___x_5222_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5224_; 
if (v_isShared_5205_ == 0)
{
lean_ctor_set(v___x_5204_, 1, v___f_5214_);
lean_ctor_set(v___x_5204_, 0, v___x_5222_);
v___x_5224_ = v___x_5204_;
goto v_reusejp_5223_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5222_);
lean_ctor_set(v_reuseFailAlloc_5259_, 1, v___f_5214_);
v___x_5224_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5223_;
}
v_reusejp_5223_:
{
lean_object* v___x_5225_; lean_object* v_toApplicative_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5257_; 
v___x_5225_ = l_StateRefT_x27_instMonad___redArg(v___x_5224_);
v_toApplicative_5226_ = lean_ctor_get(v___x_5225_, 0);
v_isSharedCheck_5257_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5257_ == 0)
{
lean_object* v_unused_5258_; 
v_unused_5258_ = lean_ctor_get(v___x_5225_, 1);
lean_dec(v_unused_5258_);
v___x_5228_ = v___x_5225_;
v_isShared_5229_ = v_isSharedCheck_5257_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_toApplicative_5226_);
lean_dec(v___x_5225_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5257_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
lean_object* v_toFunctor_5230_; lean_object* v_toSeq_5231_; lean_object* v_toSeqLeft_5232_; lean_object* v_toSeqRight_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5255_; 
v_toFunctor_5230_ = lean_ctor_get(v_toApplicative_5226_, 0);
v_toSeq_5231_ = lean_ctor_get(v_toApplicative_5226_, 2);
v_toSeqLeft_5232_ = lean_ctor_get(v_toApplicative_5226_, 3);
v_toSeqRight_5233_ = lean_ctor_get(v_toApplicative_5226_, 4);
v_isSharedCheck_5255_ = !lean_is_exclusive(v_toApplicative_5226_);
if (v_isSharedCheck_5255_ == 0)
{
lean_object* v_unused_5256_; 
v_unused_5256_ = lean_ctor_get(v_toApplicative_5226_, 1);
lean_dec(v_unused_5256_);
v___x_5235_ = v_toApplicative_5226_;
v_isShared_5236_ = v_isSharedCheck_5255_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_toSeqRight_5233_);
lean_inc(v_toSeqLeft_5232_);
lean_inc(v_toSeq_5231_);
lean_inc(v_toFunctor_5230_);
lean_dec(v_toApplicative_5226_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5255_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___f_5237_; lean_object* v___f_5238_; lean_object* v___f_5239_; lean_object* v___f_5240_; lean_object* v___x_5241_; lean_object* v___f_5242_; lean_object* v___f_5243_; lean_object* v___f_5244_; lean_object* v___x_5246_; 
v___f_5237_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5238_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5230_);
v___f_5239_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5239_, 0, v_toFunctor_5230_);
v___f_5240_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5240_, 0, v_toFunctor_5230_);
v___x_5241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5241_, 0, v___f_5239_);
lean_ctor_set(v___x_5241_, 1, v___f_5240_);
v___f_5242_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5242_, 0, v_toSeqRight_5233_);
v___f_5243_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5243_, 0, v_toSeqLeft_5232_);
v___f_5244_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5244_, 0, v_toSeq_5231_);
if (v_isShared_5236_ == 0)
{
lean_ctor_set(v___x_5235_, 4, v___f_5242_);
lean_ctor_set(v___x_5235_, 3, v___f_5243_);
lean_ctor_set(v___x_5235_, 2, v___f_5244_);
lean_ctor_set(v___x_5235_, 1, v___f_5237_);
lean_ctor_set(v___x_5235_, 0, v___x_5241_);
v___x_5246_ = v___x_5235_;
goto v_reusejp_5245_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5241_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v___f_5237_);
lean_ctor_set(v_reuseFailAlloc_5254_, 2, v___f_5244_);
lean_ctor_set(v_reuseFailAlloc_5254_, 3, v___f_5243_);
lean_ctor_set(v_reuseFailAlloc_5254_, 4, v___f_5242_);
v___x_5246_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5245_;
}
v_reusejp_5245_:
{
lean_object* v___x_5248_; 
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 1, v___f_5238_);
lean_ctor_set(v___x_5228_, 0, v___x_5246_);
v___x_5248_ = v___x_5228_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v___x_5246_);
lean_ctor_set(v_reuseFailAlloc_5253_, 1, v___f_5238_);
v___x_5248_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_27317__overap_5251_; lean_object* v___x_5252_; 
v___x_5249_ = l_Lean_instInhabitedExpr;
v___x_5250_ = l_instInhabitedOfMonad___redArg(v___x_5248_, v___x_5249_);
v___x_27317__overap_5251_ = lean_panic_fn_borrowed(v___x_5250_, v_msg_5194_);
lean_dec(v___x_5250_);
lean_inc(v___y_5198_);
lean_inc_ref(v___y_5197_);
lean_inc(v___y_5196_);
lean_inc_ref(v___y_5195_);
v___x_5252_ = lean_apply_5(v___x_27317__overap_5251_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_, lean_box(0));
return v___x_5252_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5194_ = stack[0].m_obj;
lean_object* v___y_5195_ = stack[1].m_obj;
lean_object* v___y_5196_ = stack[2].m_obj;
lean_object* v___y_5197_ = stack[3].m_obj;
lean_object* v___y_5198_ = stack[4].m_obj;
lean_object* v_res_5265_;
v_res_5265_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
stack->m_obj
 = v_res_5265_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_, lean_object* v___y_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_){
_start:
{
lean_object* v_res_5272_; 
v_res_5272_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
return v_res_5272_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5273_, lean_object* v_onAlt_5274_, lean_object* v_a_5275_, uint8_t v___x_5276_, uint8_t v_useSplitter_5277_, lean_object* v___x_5278_, lean_object* v_extraEqualities_5279_, lean_object* v_numDiscrEqs_5280_, lean_object* v___x_5281_, lean_object* v___x_5282_, lean_object* v___x_5283_, lean_object* v_ys_5284_, lean_object* v_args_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_){
_start:
{
lean_object* v_numFields_5291_; lean_object* v_numOverlaps_5292_; uint8_t v_hasUnitThunk_5293_; lean_object* v___x_5294_; uint8_t v___x_5295_; 
v_numFields_5291_ = lean_ctor_get(v___x_5273_, 0);
v_numOverlaps_5292_ = lean_ctor_get(v___x_5273_, 1);
v_hasUnitThunk_5293_ = lean_ctor_get_uint8(v___x_5273_, sizeof(void*)*2);
v___x_5294_ = lean_array_get_size(v_ys_5284_);
v___x_5295_ = lean_nat_dec_eq(v___x_5294_, v_numFields_5291_);
if (v___x_5295_ == 0)
{
lean_object* v___x_5296_; lean_object* v___x_5297_; 
lean_dec_ref(v_args_5285_);
lean_dec_ref(v_ys_5284_);
lean_dec_ref(v___x_5281_);
lean_dec(v_numDiscrEqs_5280_);
lean_dec(v_extraEqualities_5279_);
lean_dec_ref(v___x_5278_);
lean_dec(v_a_5275_);
lean_dec_ref(v_onAlt_5274_);
v___x_5296_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5297_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v___x_5296_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
return v___x_5297_;
}
else
{
lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___f_5300_; lean_object* v_altType_5302_; lean_object* v___y_5303_; lean_object* v___y_5304_; lean_object* v___y_5305_; lean_object* v___y_5306_; lean_object* v___x_5316_; 
v___x_5298_ = lean_box(v___x_5276_);
v___x_5299_ = lean_box(v_useSplitter_5277_);
lean_inc_ref(v_ys_5284_);
v___f_5300_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5300_, 0, v_args_5285_);
lean_closure_set(v___f_5300_, 1, v_ys_5284_);
lean_closure_set(v___f_5300_, 2, v_onAlt_5274_);
lean_closure_set(v___f_5300_, 3, v_a_5275_);
lean_closure_set(v___f_5300_, 4, v___x_5298_);
lean_closure_set(v___f_5300_, 5, v___x_5299_);
lean_closure_set(v___f_5300_, 6, v___x_5278_);
lean_closure_set(v___f_5300_, 7, v_extraEqualities_5279_);
lean_closure_set(v___f_5300_, 8, v_numDiscrEqs_5280_);
v___x_5316_ = l_Lean_Meta_instantiateForall(v___x_5281_, v_ys_5284_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
lean_dec_ref(v_ys_5284_);
if (lean_obj_tag(v___x_5316_) == 0)
{
uint8_t v_hasUnitThunk_5317_; 
v_hasUnitThunk_5317_ = lean_ctor_get_uint8(v___x_5282_, sizeof(void*)*2);
if (v_hasUnitThunk_5317_ == 0)
{
lean_object* v_a_5318_; 
v_a_5318_ = lean_ctor_get(v___x_5316_, 0);
lean_inc(v_a_5318_);
lean_dec_ref_known(v___x_5316_, 1);
v_altType_5302_ = v_a_5318_;
v___y_5303_ = v___y_5286_;
v___y_5304_ = v___y_5287_;
v___y_5305_ = v___y_5288_;
v___y_5306_ = v___y_5289_;
goto v___jp_5301_;
}
else
{
lean_object* v_a_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5323_; 
v_a_5319_ = lean_ctor_get(v___x_5316_, 0);
lean_inc(v_a_5319_);
lean_dec_ref_known(v___x_5316_, 1);
v___x_5320_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5321_ = lean_mk_empty_array_with_capacity(v___x_5283_);
v___x_5322_ = lean_array_push(v___x_5321_, v___x_5320_);
v___x_5323_ = l_Lean_Meta_instantiateForall(v_a_5319_, v___x_5322_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
lean_dec_ref(v___x_5322_);
if (lean_obj_tag(v___x_5323_) == 0)
{
lean_object* v_a_5324_; 
v_a_5324_ = lean_ctor_get(v___x_5323_, 0);
lean_inc(v_a_5324_);
lean_dec_ref_known(v___x_5323_, 1);
v_altType_5302_ = v_a_5324_;
v___y_5303_ = v___y_5286_;
v___y_5304_ = v___y_5287_;
v___y_5305_ = v___y_5288_;
v___y_5306_ = v___y_5289_;
goto v___jp_5301_;
}
else
{
lean_dec_ref(v___f_5300_);
return v___x_5323_;
}
}
}
else
{
lean_dec_ref(v___f_5300_);
return v___x_5316_;
}
v___jp_5301_:
{
lean_object* v___x_5307_; lean_object* v___x_5308_; 
lean_inc(v_numOverlaps_5292_);
v___x_5307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5307_, 0, v_numOverlaps_5292_);
v___x_5308_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5302_, v___x_5307_, v___f_5300_, v___x_5276_, v___x_5276_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_);
if (lean_obj_tag(v___x_5308_) == 0)
{
if (v_hasUnitThunk_5293_ == 0)
{
return v___x_5308_;
}
else
{
lean_object* v_a_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v_a_5309_ = lean_ctor_get(v___x_5308_, 0);
lean_inc(v_a_5309_);
lean_dec_ref_known(v___x_5308_, 1);
v___x_5310_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5311_ = lean_unsigned_to_nat(2u);
v___x_5312_ = lean_mk_empty_array_with_capacity(v___x_5311_);
lean_dec_ref(v___x_5312_);
v___x_5313_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5314_ = lean_array_push(v___x_5313_, v_a_5309_);
v___x_5315_ = l_Lean_Meta_mkAppM(v___x_5310_, v___x_5314_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_);
return v___x_5315_;
}
}
else
{
return v___x_5308_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5273_ = stack[0].m_obj;
lean_object* v_onAlt_5274_ = stack[1].m_obj;
lean_object* v_a_5275_ = stack[2].m_obj;
uint8_t v___x_5276_ = stack[3].m_num;
uint8_t v_useSplitter_5277_ = stack[4].m_num;
lean_object* v___x_5278_ = stack[5].m_obj;
lean_object* v_extraEqualities_5279_ = stack[6].m_obj;
lean_object* v_numDiscrEqs_5280_ = stack[7].m_obj;
lean_object* v___x_5281_ = stack[8].m_obj;
lean_object* v___x_5282_ = stack[9].m_obj;
lean_object* v___x_5283_ = stack[10].m_obj;
lean_object* v_ys_5284_ = stack[11].m_obj;
lean_object* v_args_5285_ = stack[12].m_obj;
lean_object* v___y_5286_ = stack[13].m_obj;
lean_object* v___y_5287_ = stack[14].m_obj;
lean_object* v___y_5288_ = stack[15].m_obj;
lean_object* v___y_5289_ = stack[16].m_obj;
lean_object* v_res_5325_;
v_res_5325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5273_, v_onAlt_5274_, v_a_5275_, v___x_5276_, v_useSplitter_5277_, v___x_5278_, v_extraEqualities_5279_, v_numDiscrEqs_5280_, v___x_5281_, v___x_5282_, v___x_5283_, v_ys_5284_, v_args_5285_, v___y_5286_, v___y_5287_, v___y_5288_, v___y_5289_);
stack->m_obj
 = v_res_5325_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5326_ = _args[0];
lean_object* v_onAlt_5327_ = _args[1];
lean_object* v_a_5328_ = _args[2];
lean_object* v___x_5329_ = _args[3];
lean_object* v_useSplitter_5330_ = _args[4];
lean_object* v___x_5331_ = _args[5];
lean_object* v_extraEqualities_5332_ = _args[6];
lean_object* v_numDiscrEqs_5333_ = _args[7];
lean_object* v___x_5334_ = _args[8];
lean_object* v___x_5335_ = _args[9];
lean_object* v___x_5336_ = _args[10];
lean_object* v_ys_5337_ = _args[11];
lean_object* v_args_5338_ = _args[12];
lean_object* v___y_5339_ = _args[13];
lean_object* v___y_5340_ = _args[14];
lean_object* v___y_5341_ = _args[15];
lean_object* v___y_5342_ = _args[16];
lean_object* v___y_5343_ = _args[17];
_start:
{
uint8_t v___x_34178__boxed_5344_; uint8_t v_useSplitter_boxed_5345_; lean_object* v_res_5346_; 
v___x_34178__boxed_5344_ = lean_unbox(v___x_5329_);
v_useSplitter_boxed_5345_ = lean_unbox(v_useSplitter_5330_);
v_res_5346_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5326_, v_onAlt_5327_, v_a_5328_, v___x_34178__boxed_5344_, v_useSplitter_boxed_5345_, v___x_5331_, v_extraEqualities_5332_, v_numDiscrEqs_5333_, v___x_5334_, v___x_5335_, v___x_5336_, v_ys_5337_, v_args_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v___x_5336_);
lean_dec_ref(v___x_5335_);
lean_dec_ref(v___x_5326_);
return v_res_5346_;
}
}
lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v_toApplicative_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5416_; 
v___x_5353_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5354_ = l_StateRefT_x27_instMonad___redArg(v___x_5353_);
v_toApplicative_5355_ = lean_ctor_get(v___x_5354_, 0);
v_isSharedCheck_5416_ = !lean_is_exclusive(v___x_5354_);
if (v_isSharedCheck_5416_ == 0)
{
lean_object* v_unused_5417_; 
v_unused_5417_ = lean_ctor_get(v___x_5354_, 1);
lean_dec(v_unused_5417_);
v___x_5357_ = v___x_5354_;
v_isShared_5358_ = v_isSharedCheck_5416_;
goto v_resetjp_5356_;
}
else
{
lean_inc(v_toApplicative_5355_);
lean_dec(v___x_5354_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5416_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v_toFunctor_5359_; lean_object* v_toSeq_5360_; lean_object* v_toSeqLeft_5361_; lean_object* v_toSeqRight_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5414_; 
v_toFunctor_5359_ = lean_ctor_get(v_toApplicative_5355_, 0);
v_toSeq_5360_ = lean_ctor_get(v_toApplicative_5355_, 2);
v_toSeqLeft_5361_ = lean_ctor_get(v_toApplicative_5355_, 3);
v_toSeqRight_5362_ = lean_ctor_get(v_toApplicative_5355_, 4);
v_isSharedCheck_5414_ = !lean_is_exclusive(v_toApplicative_5355_);
if (v_isSharedCheck_5414_ == 0)
{
lean_object* v_unused_5415_; 
v_unused_5415_ = lean_ctor_get(v_toApplicative_5355_, 1);
lean_dec(v_unused_5415_);
v___x_5364_ = v_toApplicative_5355_;
v_isShared_5365_ = v_isSharedCheck_5414_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_toSeqRight_5362_);
lean_inc(v_toSeqLeft_5361_);
lean_inc(v_toSeq_5360_);
lean_inc(v_toFunctor_5359_);
lean_dec(v_toApplicative_5355_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5414_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___f_5366_; lean_object* v___f_5367_; lean_object* v___f_5368_; lean_object* v___f_5369_; lean_object* v___x_5370_; lean_object* v___f_5371_; lean_object* v___f_5372_; lean_object* v___f_5373_; lean_object* v___x_5375_; 
v___f_5366_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5367_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5359_);
v___f_5368_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5368_, 0, v_toFunctor_5359_);
v___f_5369_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5369_, 0, v_toFunctor_5359_);
v___x_5370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5370_, 0, v___f_5368_);
lean_ctor_set(v___x_5370_, 1, v___f_5369_);
v___f_5371_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5371_, 0, v_toSeqRight_5362_);
v___f_5372_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5372_, 0, v_toSeqLeft_5361_);
v___f_5373_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5373_, 0, v_toSeq_5360_);
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 4, v___f_5371_);
lean_ctor_set(v___x_5364_, 3, v___f_5372_);
lean_ctor_set(v___x_5364_, 2, v___f_5373_);
lean_ctor_set(v___x_5364_, 1, v___f_5366_);
lean_ctor_set(v___x_5364_, 0, v___x_5370_);
v___x_5375_ = v___x_5364_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5370_);
lean_ctor_set(v_reuseFailAlloc_5413_, 1, v___f_5366_);
lean_ctor_set(v_reuseFailAlloc_5413_, 2, v___f_5373_);
lean_ctor_set(v_reuseFailAlloc_5413_, 3, v___f_5372_);
lean_ctor_set(v_reuseFailAlloc_5413_, 4, v___f_5371_);
v___x_5375_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
lean_object* v___x_5377_; 
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 1, v___f_5367_);
lean_ctor_set(v___x_5357_, 0, v___x_5375_);
v___x_5377_ = v___x_5357_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5412_; 
v_reuseFailAlloc_5412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5412_, 0, v___x_5375_);
lean_ctor_set(v_reuseFailAlloc_5412_, 1, v___f_5367_);
v___x_5377_ = v_reuseFailAlloc_5412_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
lean_object* v___x_5378_; lean_object* v_toApplicative_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5410_; 
v___x_5378_ = l_StateRefT_x27_instMonad___redArg(v___x_5377_);
v_toApplicative_5379_ = lean_ctor_get(v___x_5378_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5378_);
if (v_isSharedCheck_5410_ == 0)
{
lean_object* v_unused_5411_; 
v_unused_5411_ = lean_ctor_get(v___x_5378_, 1);
lean_dec(v_unused_5411_);
v___x_5381_ = v___x_5378_;
v_isShared_5382_ = v_isSharedCheck_5410_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_toApplicative_5379_);
lean_dec(v___x_5378_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5410_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v_toFunctor_5383_; lean_object* v_toSeq_5384_; lean_object* v_toSeqLeft_5385_; lean_object* v_toSeqRight_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5408_; 
v_toFunctor_5383_ = lean_ctor_get(v_toApplicative_5379_, 0);
v_toSeq_5384_ = lean_ctor_get(v_toApplicative_5379_, 2);
v_toSeqLeft_5385_ = lean_ctor_get(v_toApplicative_5379_, 3);
v_toSeqRight_5386_ = lean_ctor_get(v_toApplicative_5379_, 4);
v_isSharedCheck_5408_ = !lean_is_exclusive(v_toApplicative_5379_);
if (v_isSharedCheck_5408_ == 0)
{
lean_object* v_unused_5409_; 
v_unused_5409_ = lean_ctor_get(v_toApplicative_5379_, 1);
lean_dec(v_unused_5409_);
v___x_5388_ = v_toApplicative_5379_;
v_isShared_5389_ = v_isSharedCheck_5408_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_toSeqRight_5386_);
lean_inc(v_toSeqLeft_5385_);
lean_inc(v_toSeq_5384_);
lean_inc(v_toFunctor_5383_);
lean_dec(v_toApplicative_5379_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5408_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___f_5390_; lean_object* v___f_5391_; lean_object* v___f_5392_; lean_object* v___f_5393_; lean_object* v___x_5394_; lean_object* v___f_5395_; lean_object* v___f_5396_; lean_object* v___f_5397_; lean_object* v___x_5399_; 
v___f_5390_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5391_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5383_);
v___f_5392_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5392_, 0, v_toFunctor_5383_);
v___f_5393_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5393_, 0, v_toFunctor_5383_);
v___x_5394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5394_, 0, v___f_5392_);
lean_ctor_set(v___x_5394_, 1, v___f_5393_);
v___f_5395_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5395_, 0, v_toSeqRight_5386_);
v___f_5396_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5396_, 0, v_toSeqLeft_5385_);
v___f_5397_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5397_, 0, v_toSeq_5384_);
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 4, v___f_5395_);
lean_ctor_set(v___x_5388_, 3, v___f_5396_);
lean_ctor_set(v___x_5388_, 2, v___f_5397_);
lean_ctor_set(v___x_5388_, 1, v___f_5390_);
lean_ctor_set(v___x_5388_, 0, v___x_5394_);
v___x_5399_ = v___x_5388_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5394_);
lean_ctor_set(v_reuseFailAlloc_5407_, 1, v___f_5390_);
lean_ctor_set(v_reuseFailAlloc_5407_, 2, v___f_5397_);
lean_ctor_set(v_reuseFailAlloc_5407_, 3, v___f_5396_);
lean_ctor_set(v_reuseFailAlloc_5407_, 4, v___f_5395_);
v___x_5399_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
lean_object* v___x_5401_; 
if (v_isShared_5382_ == 0)
{
lean_ctor_set(v___x_5381_, 1, v___f_5391_);
lean_ctor_set(v___x_5381_, 0, v___x_5399_);
v___x_5401_ = v___x_5381_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v___x_5399_);
lean_ctor_set(v_reuseFailAlloc_5406_, 1, v___f_5391_);
v___x_5401_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_27337__overap_5404_; lean_object* v___x_5405_; 
v___x_5402_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
v___x_5403_ = l_instInhabitedOfMonad___redArg(v___x_5401_, v___x_5402_);
v___x_27337__overap_5404_ = lean_panic_fn_borrowed(v___x_5403_, v_msg_5347_);
lean_dec(v___x_5403_);
lean_inc(v___y_5351_);
lean_inc_ref(v___y_5350_);
lean_inc(v___y_5349_);
lean_inc_ref(v___y_5348_);
v___x_5405_ = lean_apply_5(v___x_27337__overap_5404_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_, lean_box(0));
return v___x_5405_;
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
LEAN_EXPORT void l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_5347_ = stack[0].m_obj;
lean_object* v___y_5348_ = stack[1].m_obj;
lean_object* v___y_5349_ = stack[2].m_obj;
lean_object* v___y_5350_ = stack[3].m_obj;
lean_object* v___y_5351_ = stack[4].m_obj;
lean_object* v_res_5418_;
v_res_5418_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
stack->m_obj
 = v_res_5418_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
return v_res_5425_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v___x_5432_; 
v___x_5432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5432_, 0, v___x_5426_);
return v___x_5432_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_5426_ = stack[0].m_obj;
lean_object* v___y_5427_ = stack[1].m_obj;
lean_object* v___y_5428_ = stack[2].m_obj;
lean_object* v___y_5429_ = stack[3].m_obj;
lean_object* v___y_5430_ = stack[4].m_obj;
lean_object* v_res_5433_;
v_res_5433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_);
stack->m_obj
 = v_res_5433_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
return v_res_5440_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5441_, lean_object* v_onAlt_5442_, uint8_t v_useSplitter_5443_, lean_object* v_extraEqualities_5444_, lean_object* v_numDiscrEqs_5445_, lean_object* v_a_5446_, lean_object* v_b_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_){
_start:
{
lean_object* v___y_5454_; uint8_t v___x_5477_; 
v___x_5477_ = lean_nat_dec_lt(v_a_5446_, v_upperBound_5441_);
if (v___x_5477_ == 0)
{
lean_object* v___x_5478_; 
lean_dec(v_a_5446_);
lean_dec(v_numDiscrEqs_5445_);
lean_dec(v_extraEqualities_5444_);
lean_dec_ref(v_onAlt_5442_);
v___x_5478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5478_, 0, v_b_5447_);
return v___x_5478_;
}
else
{
lean_object* v_snd_5479_; lean_object* v_snd_5480_; lean_object* v_snd_5481_; lean_object* v_snd_5482_; lean_object* v_snd_5483_; lean_object* v_fst_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5688_; 
v_snd_5479_ = lean_ctor_get(v_b_5447_, 1);
lean_inc(v_snd_5479_);
v_snd_5480_ = lean_ctor_get(v_snd_5479_, 1);
lean_inc(v_snd_5480_);
v_snd_5481_ = lean_ctor_get(v_snd_5480_, 1);
lean_inc(v_snd_5481_);
v_snd_5482_ = lean_ctor_get(v_snd_5481_, 1);
lean_inc(v_snd_5482_);
v_snd_5483_ = lean_ctor_get(v_snd_5482_, 1);
lean_inc(v_snd_5483_);
v_fst_5484_ = lean_ctor_get(v_b_5447_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v_b_5447_);
if (v_isSharedCheck_5688_ == 0)
{
lean_object* v_unused_5689_; 
v_unused_5689_ = lean_ctor_get(v_b_5447_, 1);
lean_dec(v_unused_5689_);
v___x_5486_ = v_b_5447_;
v_isShared_5487_ = v_isSharedCheck_5688_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_fst_5484_);
lean_dec(v_b_5447_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5688_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v_fst_5488_; lean_object* v___x_5490_; uint8_t v_isShared_5491_; uint8_t v_isSharedCheck_5686_; 
v_fst_5488_ = lean_ctor_get(v_snd_5479_, 0);
v_isSharedCheck_5686_ = !lean_is_exclusive(v_snd_5479_);
if (v_isSharedCheck_5686_ == 0)
{
lean_object* v_unused_5687_; 
v_unused_5687_ = lean_ctor_get(v_snd_5479_, 1);
lean_dec(v_unused_5687_);
v___x_5490_ = v_snd_5479_;
v_isShared_5491_ = v_isSharedCheck_5686_;
goto v_resetjp_5489_;
}
else
{
lean_inc(v_fst_5488_);
lean_dec(v_snd_5479_);
v___x_5490_ = lean_box(0);
v_isShared_5491_ = v_isSharedCheck_5686_;
goto v_resetjp_5489_;
}
v_resetjp_5489_:
{
lean_object* v_fst_5492_; lean_object* v___x_5494_; uint8_t v_isShared_5495_; uint8_t v_isSharedCheck_5684_; 
v_fst_5492_ = lean_ctor_get(v_snd_5480_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v_snd_5480_);
if (v_isSharedCheck_5684_ == 0)
{
lean_object* v_unused_5685_; 
v_unused_5685_ = lean_ctor_get(v_snd_5480_, 1);
lean_dec(v_unused_5685_);
v___x_5494_ = v_snd_5480_;
v_isShared_5495_ = v_isSharedCheck_5684_;
goto v_resetjp_5493_;
}
else
{
lean_inc(v_fst_5492_);
lean_dec(v_snd_5480_);
v___x_5494_ = lean_box(0);
v_isShared_5495_ = v_isSharedCheck_5684_;
goto v_resetjp_5493_;
}
v_resetjp_5493_:
{
lean_object* v_fst_5496_; lean_object* v___x_5498_; uint8_t v_isShared_5499_; uint8_t v_isSharedCheck_5682_; 
v_fst_5496_ = lean_ctor_get(v_snd_5481_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v_snd_5481_);
if (v_isSharedCheck_5682_ == 0)
{
lean_object* v_unused_5683_; 
v_unused_5683_ = lean_ctor_get(v_snd_5481_, 1);
lean_dec(v_unused_5683_);
v___x_5498_ = v_snd_5481_;
v_isShared_5499_ = v_isSharedCheck_5682_;
goto v_resetjp_5497_;
}
else
{
lean_inc(v_fst_5496_);
lean_dec(v_snd_5481_);
v___x_5498_ = lean_box(0);
v_isShared_5499_ = v_isSharedCheck_5682_;
goto v_resetjp_5497_;
}
v_resetjp_5497_:
{
lean_object* v_fst_5500_; lean_object* v___x_5502_; uint8_t v_isShared_5503_; uint8_t v_isSharedCheck_5680_; 
v_fst_5500_ = lean_ctor_get(v_snd_5482_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v_snd_5482_);
if (v_isSharedCheck_5680_ == 0)
{
lean_object* v_unused_5681_; 
v_unused_5681_ = lean_ctor_get(v_snd_5482_, 1);
lean_dec(v_unused_5681_);
v___x_5502_ = v_snd_5482_;
v_isShared_5503_ = v_isSharedCheck_5680_;
goto v_resetjp_5501_;
}
else
{
lean_inc(v_fst_5500_);
lean_dec(v_snd_5482_);
v___x_5502_ = lean_box(0);
v_isShared_5503_ = v_isSharedCheck_5680_;
goto v_resetjp_5501_;
}
v_resetjp_5501_:
{
lean_object* v_array_5504_; lean_object* v_start_5505_; lean_object* v_stop_5506_; uint8_t v___x_5507_; 
v_array_5504_ = lean_ctor_get(v_snd_5483_, 0);
v_start_5505_ = lean_ctor_get(v_snd_5483_, 1);
v_stop_5506_ = lean_ctor_get(v_snd_5483_, 2);
v___x_5507_ = lean_nat_dec_lt(v_start_5505_, v_stop_5506_);
if (v___x_5507_ == 0)
{
lean_object* v___x_5509_; 
if (v_isShared_5503_ == 0)
{
v___x_5509_ = v___x_5502_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_fst_5500_);
lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_snd_5483_);
v___x_5509_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5511_; 
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 1, v___x_5509_);
v___x_5511_ = v___x_5498_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_fst_5496_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v___x_5509_);
v___x_5511_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
lean_object* v___x_5513_; 
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 1, v___x_5511_);
v___x_5513_ = v___x_5494_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v_fst_5492_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v___x_5511_);
v___x_5513_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
lean_object* v___x_5515_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 1, v___x_5513_);
v___x_5515_ = v___x_5490_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v_fst_5488_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v___x_5513_);
v___x_5515_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
lean_object* v___x_5517_; 
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 1, v___x_5515_);
v___x_5517_ = v___x_5486_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_fst_5484_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v___x_5515_);
v___x_5517_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
lean_object* v___x_5518_; lean_object* v___f_5519_; 
v___x_5518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5518_, 0, v___x_5517_);
v___f_5519_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5519_, 0, v___x_5518_);
v___y_5454_ = v___f_5519_;
goto v___jp_5453_;
}
}
}
}
}
}
else
{
lean_object* v___x_5526_; uint8_t v_isShared_5527_; uint8_t v_isSharedCheck_5676_; 
lean_inc(v_stop_5506_);
lean_inc(v_start_5505_);
lean_inc_ref(v_array_5504_);
v_isSharedCheck_5676_ = !lean_is_exclusive(v_snd_5483_);
if (v_isSharedCheck_5676_ == 0)
{
lean_object* v_unused_5677_; lean_object* v_unused_5678_; lean_object* v_unused_5679_; 
v_unused_5677_ = lean_ctor_get(v_snd_5483_, 2);
lean_dec(v_unused_5677_);
v_unused_5678_ = lean_ctor_get(v_snd_5483_, 1);
lean_dec(v_unused_5678_);
v_unused_5679_ = lean_ctor_get(v_snd_5483_, 0);
lean_dec(v_unused_5679_);
v___x_5526_ = v_snd_5483_;
v_isShared_5527_ = v_isSharedCheck_5676_;
goto v_resetjp_5525_;
}
else
{
lean_dec(v_snd_5483_);
v___x_5526_ = lean_box(0);
v_isShared_5527_ = v_isSharedCheck_5676_;
goto v_resetjp_5525_;
}
v_resetjp_5525_:
{
lean_object* v_array_5528_; lean_object* v_start_5529_; lean_object* v_stop_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5535_; 
v_array_5528_ = lean_ctor_get(v_fst_5500_, 0);
v_start_5529_ = lean_ctor_get(v_fst_5500_, 1);
v_stop_5530_ = lean_ctor_get(v_fst_5500_, 2);
v___x_5531_ = lean_array_fget(v_array_5504_, v_start_5505_);
v___x_5532_ = lean_unsigned_to_nat(1u);
v___x_5533_ = lean_nat_add(v_start_5505_, v___x_5532_);
lean_dec(v_start_5505_);
if (v_isShared_5527_ == 0)
{
lean_ctor_set(v___x_5526_, 1, v___x_5533_);
v___x_5535_ = v___x_5526_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v_array_5504_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v___x_5533_);
lean_ctor_set(v_reuseFailAlloc_5675_, 2, v_stop_5506_);
v___x_5535_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
uint8_t v___x_5536_; 
v___x_5536_ = lean_nat_dec_lt(v_start_5529_, v_stop_5530_);
if (v___x_5536_ == 0)
{
lean_object* v___x_5538_; 
lean_dec(v___x_5531_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 1, v___x_5535_);
v___x_5538_ = v___x_5502_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_fst_5500_);
lean_ctor_set(v_reuseFailAlloc_5553_, 1, v___x_5535_);
v___x_5538_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
lean_object* v___x_5540_; 
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 1, v___x_5538_);
v___x_5540_ = v___x_5498_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_fst_5496_);
lean_ctor_set(v_reuseFailAlloc_5552_, 1, v___x_5538_);
v___x_5540_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
lean_object* v___x_5542_; 
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 1, v___x_5540_);
v___x_5542_ = v___x_5494_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_fst_5492_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v___x_5540_);
v___x_5542_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5544_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 1, v___x_5542_);
v___x_5544_ = v___x_5490_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v_fst_5488_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v___x_5542_);
v___x_5544_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
lean_object* v___x_5546_; 
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 1, v___x_5544_);
v___x_5546_ = v___x_5486_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_fst_5484_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v___x_5544_);
v___x_5546_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5547_; lean_object* v___f_5548_; 
v___x_5547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5547_, 0, v___x_5546_);
v___f_5548_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5548_, 0, v___x_5547_);
v___y_5454_ = v___f_5548_;
goto v___jp_5453_;
}
}
}
}
}
}
else
{
lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5671_; 
lean_inc(v_stop_5530_);
lean_inc(v_start_5529_);
lean_inc_ref(v_array_5528_);
v_isSharedCheck_5671_ = !lean_is_exclusive(v_fst_5500_);
if (v_isSharedCheck_5671_ == 0)
{
lean_object* v_unused_5672_; lean_object* v_unused_5673_; lean_object* v_unused_5674_; 
v_unused_5672_ = lean_ctor_get(v_fst_5500_, 2);
lean_dec(v_unused_5672_);
v_unused_5673_ = lean_ctor_get(v_fst_5500_, 1);
lean_dec(v_unused_5673_);
v_unused_5674_ = lean_ctor_get(v_fst_5500_, 0);
lean_dec(v_unused_5674_);
v___x_5555_ = v_fst_5500_;
v_isShared_5556_ = v_isSharedCheck_5671_;
goto v_resetjp_5554_;
}
else
{
lean_dec(v_fst_5500_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5671_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v_array_5557_; lean_object* v_start_5558_; lean_object* v_stop_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5563_; 
v_array_5557_ = lean_ctor_get(v_fst_5496_, 0);
v_start_5558_ = lean_ctor_get(v_fst_5496_, 1);
v_stop_5559_ = lean_ctor_get(v_fst_5496_, 2);
v___x_5560_ = lean_array_fget(v_array_5528_, v_start_5529_);
v___x_5561_ = lean_nat_add(v_start_5529_, v___x_5532_);
lean_dec(v_start_5529_);
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 1, v___x_5561_);
v___x_5563_ = v___x_5555_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_array_5528_);
lean_ctor_set(v_reuseFailAlloc_5670_, 1, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5670_, 2, v_stop_5530_);
v___x_5563_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
uint8_t v___x_5564_; 
v___x_5564_ = lean_nat_dec_lt(v_start_5558_, v_stop_5559_);
if (v___x_5564_ == 0)
{
lean_object* v___x_5566_; 
lean_dec(v___x_5560_);
lean_dec(v___x_5531_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 1, v___x_5535_);
lean_ctor_set(v___x_5502_, 0, v___x_5563_);
v___x_5566_ = v___x_5502_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5581_, 1, v___x_5535_);
v___x_5566_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 1, v___x_5566_);
v___x_5568_ = v___x_5498_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_fst_5496_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v___x_5566_);
v___x_5568_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
lean_object* v___x_5570_; 
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 1, v___x_5568_);
v___x_5570_ = v___x_5494_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_fst_5492_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
lean_object* v___x_5572_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 1, v___x_5570_);
v___x_5572_ = v___x_5490_;
goto v_reusejp_5571_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_fst_5488_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v___x_5570_);
v___x_5572_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5571_;
}
v_reusejp_5571_:
{
lean_object* v___x_5574_; 
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 1, v___x_5572_);
v___x_5574_ = v___x_5486_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_fst_5484_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v___x_5572_);
v___x_5574_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
lean_object* v___x_5575_; lean_object* v___f_5576_; 
v___x_5575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5575_, 0, v___x_5574_);
v___f_5576_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5576_, 0, v___x_5575_);
v___y_5454_ = v___f_5576_;
goto v___jp_5453_;
}
}
}
}
}
}
else
{
lean_object* v___x_5583_; uint8_t v_isShared_5584_; uint8_t v_isSharedCheck_5666_; 
lean_inc(v_stop_5559_);
lean_inc(v_start_5558_);
lean_inc_ref(v_array_5557_);
v_isSharedCheck_5666_ = !lean_is_exclusive(v_fst_5496_);
if (v_isSharedCheck_5666_ == 0)
{
lean_object* v_unused_5667_; lean_object* v_unused_5668_; lean_object* v_unused_5669_; 
v_unused_5667_ = lean_ctor_get(v_fst_5496_, 2);
lean_dec(v_unused_5667_);
v_unused_5668_ = lean_ctor_get(v_fst_5496_, 1);
lean_dec(v_unused_5668_);
v_unused_5669_ = lean_ctor_get(v_fst_5496_, 0);
lean_dec(v_unused_5669_);
v___x_5583_ = v_fst_5496_;
v_isShared_5584_ = v_isSharedCheck_5666_;
goto v_resetjp_5582_;
}
else
{
lean_dec(v_fst_5496_);
v___x_5583_ = lean_box(0);
v_isShared_5584_ = v_isSharedCheck_5666_;
goto v_resetjp_5582_;
}
v_resetjp_5582_:
{
lean_object* v_array_5585_; lean_object* v_start_5586_; lean_object* v_stop_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; lean_object* v___x_5591_; 
v_array_5585_ = lean_ctor_get(v_fst_5492_, 0);
v_start_5586_ = lean_ctor_get(v_fst_5492_, 1);
v_stop_5587_ = lean_ctor_get(v_fst_5492_, 2);
v___x_5588_ = lean_array_fget(v_array_5557_, v_start_5558_);
v___x_5589_ = lean_nat_add(v_start_5558_, v___x_5532_);
lean_dec(v_start_5558_);
if (v_isShared_5584_ == 0)
{
lean_ctor_set(v___x_5583_, 1, v___x_5589_);
v___x_5591_ = v___x_5583_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_array_5557_);
lean_ctor_set(v_reuseFailAlloc_5665_, 1, v___x_5589_);
lean_ctor_set(v_reuseFailAlloc_5665_, 2, v_stop_5559_);
v___x_5591_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
uint8_t v___x_5592_; 
v___x_5592_ = lean_nat_dec_lt(v_start_5586_, v_stop_5587_);
if (v___x_5592_ == 0)
{
lean_object* v___x_5594_; 
lean_dec(v___x_5588_);
lean_dec(v___x_5560_);
lean_dec(v___x_5531_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 1, v___x_5535_);
lean_ctor_set(v___x_5502_, 0, v___x_5563_);
v___x_5594_ = v___x_5502_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5609_; 
v_reuseFailAlloc_5609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5609_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5609_, 1, v___x_5535_);
v___x_5594_ = v_reuseFailAlloc_5609_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
lean_object* v___x_5596_; 
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 1, v___x_5594_);
lean_ctor_set(v___x_5498_, 0, v___x_5591_);
v___x_5596_ = v___x_5498_;
goto v_reusejp_5595_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v___x_5591_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v___x_5594_);
v___x_5596_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5595_;
}
v_reusejp_5595_:
{
lean_object* v___x_5598_; 
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 1, v___x_5596_);
v___x_5598_ = v___x_5494_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_fst_5492_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v___x_5596_);
v___x_5598_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5600_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 1, v___x_5598_);
v___x_5600_ = v___x_5490_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_fst_5488_);
lean_ctor_set(v_reuseFailAlloc_5606_, 1, v___x_5598_);
v___x_5600_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
lean_object* v___x_5602_; 
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 1, v___x_5600_);
v___x_5602_ = v___x_5486_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_fst_5484_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v___x_5600_);
v___x_5602_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
lean_object* v___x_5603_; lean_object* v___f_5604_; 
v___x_5603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5603_, 0, v___x_5602_);
v___f_5604_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5604_, 0, v___x_5603_);
v___y_5454_ = v___f_5604_;
goto v___jp_5453_;
}
}
}
}
}
}
else
{
lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5661_; 
lean_inc(v_stop_5587_);
lean_inc(v_start_5586_);
lean_inc_ref(v_array_5585_);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_fst_5492_);
if (v_isSharedCheck_5661_ == 0)
{
lean_object* v_unused_5662_; lean_object* v_unused_5663_; lean_object* v_unused_5664_; 
v_unused_5662_ = lean_ctor_get(v_fst_5492_, 2);
lean_dec(v_unused_5662_);
v_unused_5663_ = lean_ctor_get(v_fst_5492_, 1);
lean_dec(v_unused_5663_);
v_unused_5664_ = lean_ctor_get(v_fst_5492_, 0);
lean_dec(v_unused_5664_);
v___x_5611_ = v_fst_5492_;
v_isShared_5612_ = v_isSharedCheck_5661_;
goto v_resetjp_5610_;
}
else
{
lean_dec(v_fst_5492_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5661_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v_array_5613_; lean_object* v_start_5614_; lean_object* v_stop_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5619_; 
v_array_5613_ = lean_ctor_get(v_fst_5488_, 0);
v_start_5614_ = lean_ctor_get(v_fst_5488_, 1);
v_stop_5615_ = lean_ctor_get(v_fst_5488_, 2);
v___x_5616_ = lean_array_fget(v_array_5585_, v_start_5586_);
v___x_5617_ = lean_nat_add(v_start_5586_, v___x_5532_);
lean_dec(v_start_5586_);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 1, v___x_5617_);
v___x_5619_ = v___x_5611_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_array_5585_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5660_, 2, v_stop_5587_);
v___x_5619_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
uint8_t v___x_5620_; 
v___x_5620_ = lean_nat_dec_lt(v_start_5614_, v_stop_5615_);
if (v___x_5620_ == 0)
{
lean_object* v___x_5622_; 
lean_dec(v___x_5616_);
lean_dec(v___x_5588_);
lean_dec(v___x_5560_);
lean_dec(v___x_5531_);
if (v_isShared_5503_ == 0)
{
lean_ctor_set(v___x_5502_, 1, v___x_5535_);
lean_ctor_set(v___x_5502_, 0, v___x_5563_);
v___x_5622_ = v___x_5502_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5637_; 
v_reuseFailAlloc_5637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5637_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5637_, 1, v___x_5535_);
v___x_5622_ = v_reuseFailAlloc_5637_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
lean_object* v___x_5624_; 
if (v_isShared_5499_ == 0)
{
lean_ctor_set(v___x_5498_, 1, v___x_5622_);
lean_ctor_set(v___x_5498_, 0, v___x_5591_);
v___x_5624_ = v___x_5498_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v___x_5591_);
lean_ctor_set(v_reuseFailAlloc_5636_, 1, v___x_5622_);
v___x_5624_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
lean_object* v___x_5626_; 
if (v_isShared_5495_ == 0)
{
lean_ctor_set(v___x_5494_, 1, v___x_5624_);
lean_ctor_set(v___x_5494_, 0, v___x_5619_);
v___x_5626_ = v___x_5494_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5635_, 1, v___x_5624_);
v___x_5626_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
lean_object* v___x_5628_; 
if (v_isShared_5491_ == 0)
{
lean_ctor_set(v___x_5490_, 1, v___x_5626_);
v___x_5628_ = v___x_5490_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_fst_5488_);
lean_ctor_set(v_reuseFailAlloc_5634_, 1, v___x_5626_);
v___x_5628_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
lean_object* v___x_5630_; 
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 1, v___x_5628_);
v___x_5630_ = v___x_5486_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_fst_5484_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v___x_5628_);
v___x_5630_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
lean_object* v___x_5631_; lean_object* v___f_5632_; 
v___x_5631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5631_, 0, v___x_5630_);
v___f_5632_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5632_, 0, v___x_5631_);
v___y_5454_ = v___f_5632_;
goto v___jp_5453_;
}
}
}
}
}
}
else
{
lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5656_; 
lean_inc(v_stop_5615_);
lean_inc(v_start_5614_);
lean_inc_ref(v_array_5613_);
lean_del_object(v___x_5502_);
lean_del_object(v___x_5498_);
lean_del_object(v___x_5494_);
lean_del_object(v___x_5490_);
lean_del_object(v___x_5486_);
v_isSharedCheck_5656_ = !lean_is_exclusive(v_fst_5488_);
if (v_isSharedCheck_5656_ == 0)
{
lean_object* v_unused_5657_; lean_object* v_unused_5658_; lean_object* v_unused_5659_; 
v_unused_5657_ = lean_ctor_get(v_fst_5488_, 2);
lean_dec(v_unused_5657_);
v_unused_5658_ = lean_ctor_get(v_fst_5488_, 1);
lean_dec(v_unused_5658_);
v_unused_5659_ = lean_ctor_get(v_fst_5488_, 0);
lean_dec(v_unused_5659_);
v___x_5639_ = v_fst_5488_;
v_isShared_5640_ = v_isSharedCheck_5656_;
goto v_resetjp_5638_;
}
else
{
lean_dec(v_fst_5488_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5656_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v_numOverlaps_5641_; lean_object* v___x_5642_; uint8_t v___x_5643_; 
v_numOverlaps_5641_ = lean_ctor_get(v___x_5616_, 1);
v___x_5642_ = lean_unsigned_to_nat(0u);
v___x_5643_ = lean_nat_dec_eq(v_numOverlaps_5641_, v___x_5642_);
if (v___x_5643_ == 0)
{
lean_object* v___x_5644_; lean_object* v___x_5645_; 
lean_del_object(v___x_5639_);
lean_dec_ref(v___x_5619_);
lean_dec(v___x_5616_);
lean_dec(v_stop_5615_);
lean_dec(v_start_5614_);
lean_dec_ref(v_array_5613_);
lean_dec_ref(v___x_5591_);
lean_dec(v___x_5588_);
lean_dec_ref(v___x_5563_);
lean_dec(v___x_5560_);
lean_dec_ref(v___x_5535_);
lean_dec(v___x_5531_);
lean_dec(v_fst_5484_);
v___x_5644_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_5645_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed), 6, 1);
lean_closure_set(v___x_5645_, 0, v___x_5644_);
v___y_5454_ = v___x_5645_;
goto v___jp_5453_;
}
else
{
uint8_t v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___f_5650_; lean_object* v___x_5651_; lean_object* v___x_5653_; 
v___x_5646_ = 0;
v___x_5647_ = lean_array_fget_borrowed(v_array_5613_, v_start_5614_);
v___x_5648_ = lean_box(v___x_5646_);
v___x_5649_ = lean_box(v_useSplitter_5443_);
lean_inc(v___x_5616_);
lean_inc(v_numDiscrEqs_5445_);
lean_inc(v_extraEqualities_5444_);
lean_inc(v___x_5647_);
lean_inc(v_a_5446_);
lean_inc_ref(v_onAlt_5442_);
v___f_5650_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5650_, 0, v___x_5588_);
lean_closure_set(v___f_5650_, 1, v_onAlt_5442_);
lean_closure_set(v___f_5650_, 2, v_a_5446_);
lean_closure_set(v___f_5650_, 3, v___x_5648_);
lean_closure_set(v___f_5650_, 4, v___x_5649_);
lean_closure_set(v___f_5650_, 5, v___x_5647_);
lean_closure_set(v___f_5650_, 6, v_extraEqualities_5444_);
lean_closure_set(v___f_5650_, 7, v_numDiscrEqs_5445_);
lean_closure_set(v___f_5650_, 8, v___x_5531_);
lean_closure_set(v___f_5650_, 9, v___x_5616_);
lean_closure_set(v___f_5650_, 10, v___x_5532_);
v___x_5651_ = lean_nat_add(v_start_5614_, v___x_5532_);
lean_dec(v_start_5614_);
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 1, v___x_5651_);
v___x_5653_ = v___x_5639_;
goto v_reusejp_5652_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_array_5613_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v___x_5651_);
lean_ctor_set(v_reuseFailAlloc_5655_, 2, v_stop_5615_);
v___x_5653_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5652_;
}
v_reusejp_5652_:
{
lean_object* v___f_5654_; 
v___f_5654_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5654_, 0, v___x_5560_);
lean_closure_set(v___f_5654_, 1, v___x_5616_);
lean_closure_set(v___f_5654_, 2, v___f_5650_);
lean_closure_set(v___f_5654_, 3, v_fst_5484_);
lean_closure_set(v___f_5654_, 4, v___x_5563_);
lean_closure_set(v___f_5654_, 5, v___x_5535_);
lean_closure_set(v___f_5654_, 6, v___x_5591_);
lean_closure_set(v___f_5654_, 7, v___x_5619_);
lean_closure_set(v___f_5654_, 8, v___x_5653_);
v___y_5454_ = v___f_5654_;
goto v___jp_5453_;
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
}
}
}
}
}
}
}
}
v___jp_5453_:
{
lean_object* v___x_5455_; 
lean_inc(v___y_5451_);
lean_inc_ref(v___y_5450_);
lean_inc(v___y_5449_);
lean_inc_ref(v___y_5448_);
v___x_5455_ = lean_apply_5(v___y_5454_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, lean_box(0));
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5468_; 
v_a_5456_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5458_ = v___x_5455_;
v_isShared_5459_ = v_isSharedCheck_5468_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v___x_5455_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5468_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
if (lean_obj_tag(v_a_5456_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5462_; 
lean_dec(v_a_5446_);
lean_dec(v_numDiscrEqs_5445_);
lean_dec(v_extraEqualities_5444_);
lean_dec_ref(v_onAlt_5442_);
v_a_5460_ = lean_ctor_get(v_a_5456_, 0);
lean_inc(v_a_5460_);
lean_dec_ref_known(v_a_5456_, 1);
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 0, v_a_5460_);
v___x_5462_ = v___x_5458_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5460_);
v___x_5462_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
return v___x_5462_;
}
}
else
{
lean_object* v_a_5464_; lean_object* v___x_5465_; lean_object* v___x_5466_; 
lean_del_object(v___x_5458_);
v_a_5464_ = lean_ctor_get(v_a_5456_, 0);
lean_inc(v_a_5464_);
lean_dec_ref_known(v_a_5456_, 1);
v___x_5465_ = lean_unsigned_to_nat(1u);
v___x_5466_ = lean_nat_add(v_a_5446_, v___x_5465_);
lean_dec(v_a_5446_);
v_a_5446_ = v___x_5466_;
v_b_5447_ = v_a_5464_;
goto _start;
}
}
}
else
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5476_; 
lean_dec(v_a_5446_);
lean_dec(v_numDiscrEqs_5445_);
lean_dec(v_extraEqualities_5444_);
lean_dec_ref(v_onAlt_5442_);
v_a_5469_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5471_ = v___x_5455_;
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5455_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5474_; 
if (v_isShared_5472_ == 0)
{
v___x_5474_ = v___x_5471_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_5441_ = stack[0].m_obj;
lean_object* v_onAlt_5442_ = stack[1].m_obj;
uint8_t v_useSplitter_5443_ = stack[2].m_num;
lean_object* v_extraEqualities_5444_ = stack[3].m_obj;
lean_object* v_numDiscrEqs_5445_ = stack[4].m_obj;
lean_object* v_a_5446_ = stack[5].m_obj;
lean_object* v_b_5447_ = stack[6].m_obj;
lean_object* v___y_5448_ = stack[7].m_obj;
lean_object* v___y_5449_ = stack[8].m_obj;
lean_object* v___y_5450_ = stack[9].m_obj;
lean_object* v___y_5451_ = stack[10].m_obj;
lean_object* v_res_5690_;
v_res_5690_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5441_, v_onAlt_5442_, v_useSplitter_5443_, v_extraEqualities_5444_, v_numDiscrEqs_5445_, v_a_5446_, v_b_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_);
stack->m_obj
 = v_res_5690_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5691_, lean_object* v_onAlt_5692_, lean_object* v_useSplitter_5693_, lean_object* v_extraEqualities_5694_, lean_object* v_numDiscrEqs_5695_, lean_object* v_a_5696_, lean_object* v_b_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_, lean_object* v___y_5702_){
_start:
{
uint8_t v_useSplitter_boxed_5703_; lean_object* v_res_5704_; 
v_useSplitter_boxed_5703_ = lean_unbox(v_useSplitter_5693_);
v_res_5704_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5691_, v_onAlt_5692_, v_useSplitter_boxed_5703_, v_extraEqualities_5694_, v_numDiscrEqs_5695_, v_a_5696_, v_b_5697_, v___y_5698_, v___y_5699_, v___y_5700_, v___y_5701_);
lean_dec(v___y_5701_);
lean_dec_ref(v___y_5700_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
lean_dec(v_upperBound_5691_);
return v_res_5704_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5705_, lean_object* v_as_5706_, size_t v_sz_5707_, size_t v_i_5708_, lean_object* v_b_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_){
_start:
{
lean_object* v_a_5716_; uint8_t v___x_5720_; 
v___x_5720_ = lean_usize_dec_lt(v_i_5708_, v_sz_5707_);
if (v___x_5720_ == 0)
{
lean_object* v___x_5721_; 
v___x_5721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5721_, 0, v_b_5709_);
return v___x_5721_;
}
else
{
lean_object* v_snd_5722_; lean_object* v_snd_5723_; lean_object* v_snd_5724_; lean_object* v_snd_5725_; lean_object* v_fst_5726_; lean_object* v___x_5728_; uint8_t v_isShared_5729_; uint8_t v_isSharedCheck_5872_; 
v_snd_5722_ = lean_ctor_get(v_b_5709_, 1);
lean_inc(v_snd_5722_);
v_snd_5723_ = lean_ctor_get(v_snd_5722_, 1);
lean_inc(v_snd_5723_);
v_snd_5724_ = lean_ctor_get(v_snd_5723_, 1);
lean_inc(v_snd_5724_);
v_snd_5725_ = lean_ctor_get(v_snd_5724_, 1);
lean_inc(v_snd_5725_);
v_fst_5726_ = lean_ctor_get(v_b_5709_, 0);
v_isSharedCheck_5872_ = !lean_is_exclusive(v_b_5709_);
if (v_isSharedCheck_5872_ == 0)
{
lean_object* v_unused_5873_; 
v_unused_5873_ = lean_ctor_get(v_b_5709_, 1);
lean_dec(v_unused_5873_);
v___x_5728_ = v_b_5709_;
v_isShared_5729_ = v_isSharedCheck_5872_;
goto v_resetjp_5727_;
}
else
{
lean_inc(v_fst_5726_);
lean_dec(v_b_5709_);
v___x_5728_ = lean_box(0);
v_isShared_5729_ = v_isSharedCheck_5872_;
goto v_resetjp_5727_;
}
v_resetjp_5727_:
{
lean_object* v_fst_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5870_; 
v_fst_5730_ = lean_ctor_get(v_snd_5722_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v_snd_5722_);
if (v_isSharedCheck_5870_ == 0)
{
lean_object* v_unused_5871_; 
v_unused_5871_ = lean_ctor_get(v_snd_5722_, 1);
lean_dec(v_unused_5871_);
v___x_5732_ = v_snd_5722_;
v_isShared_5733_ = v_isSharedCheck_5870_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_fst_5730_);
lean_dec(v_snd_5722_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5870_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v_fst_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5868_; 
v_fst_5734_ = lean_ctor_get(v_snd_5723_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v_snd_5723_);
if (v_isSharedCheck_5868_ == 0)
{
lean_object* v_unused_5869_; 
v_unused_5869_ = lean_ctor_get(v_snd_5723_, 1);
lean_dec(v_unused_5869_);
v___x_5736_ = v_snd_5723_;
v_isShared_5737_ = v_isSharedCheck_5868_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_fst_5734_);
lean_dec(v_snd_5723_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5868_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_fst_5738_; lean_object* v___x_5740_; uint8_t v_isShared_5741_; uint8_t v_isSharedCheck_5866_; 
v_fst_5738_ = lean_ctor_get(v_snd_5724_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v_snd_5724_);
if (v_isSharedCheck_5866_ == 0)
{
lean_object* v_unused_5867_; 
v_unused_5867_ = lean_ctor_get(v_snd_5724_, 1);
lean_dec(v_unused_5867_);
v___x_5740_ = v_snd_5724_;
v_isShared_5741_ = v_isSharedCheck_5866_;
goto v_resetjp_5739_;
}
else
{
lean_inc(v_fst_5738_);
lean_dec(v_snd_5724_);
v___x_5740_ = lean_box(0);
v_isShared_5741_ = v_isSharedCheck_5866_;
goto v_resetjp_5739_;
}
v_resetjp_5739_:
{
lean_object* v_array_5742_; lean_object* v_start_5743_; lean_object* v_stop_5744_; uint8_t v___x_5745_; 
v_array_5742_ = lean_ctor_get(v_snd_5725_, 0);
v_start_5743_ = lean_ctor_get(v_snd_5725_, 1);
v_stop_5744_ = lean_ctor_get(v_snd_5725_, 2);
v___x_5745_ = lean_nat_dec_lt(v_start_5743_, v_stop_5744_);
if (v___x_5745_ == 0)
{
lean_object* v___x_5747_; 
if (v_isShared_5741_ == 0)
{
v___x_5747_ = v___x_5740_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_fst_5738_);
lean_ctor_set(v_reuseFailAlloc_5758_, 1, v_snd_5725_);
v___x_5747_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
lean_object* v___x_5749_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5747_);
v___x_5749_ = v___x_5736_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5757_; 
v_reuseFailAlloc_5757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_fst_5734_);
lean_ctor_set(v_reuseFailAlloc_5757_, 1, v___x_5747_);
v___x_5749_ = v_reuseFailAlloc_5757_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
lean_object* v___x_5751_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5749_);
v___x_5751_ = v___x_5732_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v_fst_5730_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v___x_5749_);
v___x_5751_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
lean_object* v___x_5753_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5751_);
v___x_5753_ = v___x_5728_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5755_, 1, v___x_5751_);
v___x_5753_ = v_reuseFailAlloc_5755_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
lean_object* v___x_5754_; 
v___x_5754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5753_);
return v___x_5754_;
}
}
}
}
}
else
{
lean_object* v___x_5760_; uint8_t v_isShared_5761_; uint8_t v_isSharedCheck_5862_; 
lean_inc(v_stop_5744_);
lean_inc(v_start_5743_);
lean_inc_ref(v_array_5742_);
v_isSharedCheck_5862_ = !lean_is_exclusive(v_snd_5725_);
if (v_isSharedCheck_5862_ == 0)
{
lean_object* v_unused_5863_; lean_object* v_unused_5864_; lean_object* v_unused_5865_; 
v_unused_5863_ = lean_ctor_get(v_snd_5725_, 2);
lean_dec(v_unused_5863_);
v_unused_5864_ = lean_ctor_get(v_snd_5725_, 1);
lean_dec(v_unused_5864_);
v_unused_5865_ = lean_ctor_get(v_snd_5725_, 0);
lean_dec(v_unused_5865_);
v___x_5760_ = v_snd_5725_;
v_isShared_5761_ = v_isSharedCheck_5862_;
goto v_resetjp_5759_;
}
else
{
lean_dec(v_snd_5725_);
v___x_5760_ = lean_box(0);
v_isShared_5761_ = v_isSharedCheck_5862_;
goto v_resetjp_5759_;
}
v_resetjp_5759_:
{
lean_object* v_array_5762_; lean_object* v_start_5763_; lean_object* v_stop_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5769_; 
v_array_5762_ = lean_ctor_get(v_fst_5738_, 0);
v_start_5763_ = lean_ctor_get(v_fst_5738_, 1);
v_stop_5764_ = lean_ctor_get(v_fst_5738_, 2);
v___x_5765_ = lean_array_fget(v_array_5742_, v_start_5743_);
v___x_5766_ = lean_unsigned_to_nat(1u);
v___x_5767_ = lean_nat_add(v_start_5743_, v___x_5766_);
lean_dec(v_start_5743_);
if (v_isShared_5761_ == 0)
{
lean_ctor_set(v___x_5760_, 1, v___x_5767_);
v___x_5769_ = v___x_5760_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_array_5742_);
lean_ctor_set(v_reuseFailAlloc_5861_, 1, v___x_5767_);
lean_ctor_set(v_reuseFailAlloc_5861_, 2, v_stop_5744_);
v___x_5769_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
uint8_t v___x_5770_; 
v___x_5770_ = lean_nat_dec_lt(v_start_5763_, v_stop_5764_);
if (v___x_5770_ == 0)
{
lean_object* v___x_5772_; 
lean_dec(v___x_5765_);
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 1, v___x_5769_);
v___x_5772_ = v___x_5740_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_fst_5738_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v___x_5769_);
v___x_5772_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
lean_object* v___x_5774_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5772_);
v___x_5774_ = v___x_5736_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_fst_5734_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5772_);
v___x_5774_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
lean_object* v___x_5776_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5774_);
v___x_5776_ = v___x_5732_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_fst_5730_);
lean_ctor_set(v_reuseFailAlloc_5781_, 1, v___x_5774_);
v___x_5776_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5778_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5776_);
v___x_5778_ = v___x_5728_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5776_);
v___x_5778_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5779_; 
v___x_5779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5779_, 0, v___x_5778_);
return v___x_5779_;
}
}
}
}
}
else
{
lean_object* v___x_5785_; uint8_t v_isShared_5786_; uint8_t v_isSharedCheck_5857_; 
lean_inc(v_stop_5764_);
lean_inc(v_start_5763_);
lean_inc_ref(v_array_5762_);
v_isSharedCheck_5857_ = !lean_is_exclusive(v_fst_5738_);
if (v_isSharedCheck_5857_ == 0)
{
lean_object* v_unused_5858_; lean_object* v_unused_5859_; lean_object* v_unused_5860_; 
v_unused_5858_ = lean_ctor_get(v_fst_5738_, 2);
lean_dec(v_unused_5858_);
v_unused_5859_ = lean_ctor_get(v_fst_5738_, 1);
lean_dec(v_unused_5859_);
v_unused_5860_ = lean_ctor_get(v_fst_5738_, 0);
lean_dec(v_unused_5860_);
v___x_5785_ = v_fst_5738_;
v_isShared_5786_ = v_isSharedCheck_5857_;
goto v_resetjp_5784_;
}
else
{
lean_dec(v_fst_5738_);
v___x_5785_ = lean_box(0);
v_isShared_5786_ = v_isSharedCheck_5857_;
goto v_resetjp_5784_;
}
v_resetjp_5784_:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5790_; 
v___x_5787_ = lean_array_fget(v_array_5762_, v_start_5763_);
v___x_5788_ = lean_nat_add(v_start_5763_, v___x_5766_);
lean_dec(v_start_5763_);
if (v_isShared_5786_ == 0)
{
lean_ctor_set(v___x_5785_, 1, v___x_5788_);
v___x_5790_ = v___x_5785_;
goto v_reusejp_5789_;
}
else
{
lean_object* v_reuseFailAlloc_5856_; 
v_reuseFailAlloc_5856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_array_5762_);
lean_ctor_set(v_reuseFailAlloc_5856_, 1, v___x_5788_);
lean_ctor_set(v_reuseFailAlloc_5856_, 2, v_stop_5764_);
v___x_5790_ = v_reuseFailAlloc_5856_;
goto v_reusejp_5789_;
}
v_reusejp_5789_:
{
if (v_addEqualities_5705_ == 0)
{
lean_dec(v___x_5787_);
goto v___jp_5791_;
}
else
{
if (lean_obj_tag(v___x_5765_) == 0)
{
lean_object* v_a_5807_; lean_object* v___x_5808_; 
lean_del_object(v___x_5740_);
lean_del_object(v___x_5736_);
lean_del_object(v___x_5732_);
lean_del_object(v___x_5728_);
v_a_5807_ = lean_array_uget_borrowed(v_as_5706_, v_i_5708_);
lean_inc(v_a_5807_);
v___x_5808_ = l_Lean_Meta_isProof(v_a_5807_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_);
if (lean_obj_tag(v___x_5808_) == 0)
{
lean_object* v_a_5809_; uint8_t v___x_5810_; 
v_a_5809_ = lean_ctor_get(v___x_5808_, 0);
lean_inc(v_a_5809_);
lean_dec_ref_known(v___x_5808_, 1);
v___x_5810_ = lean_unbox(v_a_5809_);
lean_dec(v_a_5809_);
if (v___x_5810_ == 0)
{
lean_object* v___x_5811_; 
lean_inc(v_a_5807_);
v___x_5811_ = l_Lean_Meta_mkEqHEq(v___x_5787_, v_a_5807_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v___x_5813_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
lean_inc_n(v_a_5812_, 2);
lean_dec_ref_known(v___x_5811_, 1);
v___x_5813_ = l_Lean_mkArrow(v_a_5812_, v_fst_5726_, v___y_5712_, v___y_5713_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; uint8_t v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5814_);
lean_dec_ref_known(v___x_5813_, 1);
v___x_5815_ = l_Lean_Expr_isHEq(v_a_5812_);
lean_dec(v_a_5812_);
v___x_5816_ = lean_box(v___x_5815_);
v___x_5817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5817_, 0, v___x_5816_);
v___x_5818_ = lean_array_push(v_fst_5730_, v___x_5817_);
v___x_5819_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_5820_ = lean_array_push(v_fst_5734_, v___x_5819_);
v___x_5821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5790_);
lean_ctor_set(v___x_5821_, 1, v___x_5769_);
v___x_5822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5822_, 0, v___x_5820_);
lean_ctor_set(v___x_5822_, 1, v___x_5821_);
v___x_5823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5823_, 0, v___x_5818_);
lean_ctor_set(v___x_5823_, 1, v___x_5822_);
v___x_5824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5824_, 0, v_a_5814_);
lean_ctor_set(v___x_5824_, 1, v___x_5823_);
v_a_5716_ = v___x_5824_;
goto v___jp_5715_;
}
else
{
lean_object* v_a_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5832_; 
lean_dec(v_a_5812_);
lean_dec_ref(v___x_5790_);
lean_dec_ref(v___x_5769_);
lean_dec(v_fst_5734_);
lean_dec(v_fst_5730_);
v_a_5825_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5832_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5832_ == 0)
{
v___x_5827_ = v___x_5813_;
v_isShared_5828_ = v_isSharedCheck_5832_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_a_5825_);
lean_dec(v___x_5813_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5832_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v___x_5830_; 
if (v_isShared_5828_ == 0)
{
v___x_5830_ = v___x_5827_;
goto v_reusejp_5829_;
}
else
{
lean_object* v_reuseFailAlloc_5831_; 
v_reuseFailAlloc_5831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5831_, 0, v_a_5825_);
v___x_5830_ = v_reuseFailAlloc_5831_;
goto v_reusejp_5829_;
}
v_reusejp_5829_:
{
return v___x_5830_;
}
}
}
}
else
{
lean_object* v_a_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5840_; 
lean_dec_ref(v___x_5790_);
lean_dec_ref(v___x_5769_);
lean_dec(v_fst_5734_);
lean_dec(v_fst_5730_);
lean_dec(v_fst_5726_);
v_a_5833_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5840_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5840_ == 0)
{
v___x_5835_ = v___x_5811_;
v_isShared_5836_ = v_isSharedCheck_5840_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_a_5833_);
lean_dec(v___x_5811_);
v___x_5835_ = lean_box(0);
v_isShared_5836_ = v_isSharedCheck_5840_;
goto v_resetjp_5834_;
}
v_resetjp_5834_:
{
lean_object* v___x_5838_; 
if (v_isShared_5836_ == 0)
{
v___x_5838_ = v___x_5835_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5839_; 
v_reuseFailAlloc_5839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5839_, 0, v_a_5833_);
v___x_5838_ = v_reuseFailAlloc_5839_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
return v___x_5838_;
}
}
}
}
else
{
lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; lean_object* v___x_5844_; lean_object* v___x_5845_; lean_object* v___x_5846_; lean_object* v___x_5847_; 
lean_dec(v___x_5787_);
v___x_5841_ = lean_box(0);
v___x_5842_ = lean_array_push(v_fst_5730_, v___x_5841_);
v___x_5843_ = lean_array_push(v_fst_5734_, v___x_5765_);
v___x_5844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5844_, 0, v___x_5790_);
lean_ctor_set(v___x_5844_, 1, v___x_5769_);
v___x_5845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5845_, 0, v___x_5843_);
lean_ctor_set(v___x_5845_, 1, v___x_5844_);
v___x_5846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5846_, 0, v___x_5842_);
lean_ctor_set(v___x_5846_, 1, v___x_5845_);
v___x_5847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5847_, 0, v_fst_5726_);
lean_ctor_set(v___x_5847_, 1, v___x_5846_);
v_a_5716_ = v___x_5847_;
goto v___jp_5715_;
}
}
else
{
lean_object* v_a_5848_; lean_object* v___x_5850_; uint8_t v_isShared_5851_; uint8_t v_isSharedCheck_5855_; 
lean_dec_ref(v___x_5790_);
lean_dec(v___x_5787_);
lean_dec_ref(v___x_5769_);
lean_dec(v_fst_5734_);
lean_dec(v_fst_5730_);
lean_dec(v_fst_5726_);
v_a_5848_ = lean_ctor_get(v___x_5808_, 0);
v_isSharedCheck_5855_ = !lean_is_exclusive(v___x_5808_);
if (v_isSharedCheck_5855_ == 0)
{
v___x_5850_ = v___x_5808_;
v_isShared_5851_ = v_isSharedCheck_5855_;
goto v_resetjp_5849_;
}
else
{
lean_inc(v_a_5848_);
lean_dec(v___x_5808_);
v___x_5850_ = lean_box(0);
v_isShared_5851_ = v_isSharedCheck_5855_;
goto v_resetjp_5849_;
}
v_resetjp_5849_:
{
lean_object* v___x_5853_; 
if (v_isShared_5851_ == 0)
{
v___x_5853_ = v___x_5850_;
goto v_reusejp_5852_;
}
else
{
lean_object* v_reuseFailAlloc_5854_; 
v_reuseFailAlloc_5854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_a_5848_);
v___x_5853_ = v_reuseFailAlloc_5854_;
goto v_reusejp_5852_;
}
v_reusejp_5852_:
{
return v___x_5853_;
}
}
}
}
else
{
lean_dec(v___x_5787_);
goto v___jp_5791_;
}
}
v___jp_5791_:
{
lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5796_; 
v___x_5792_ = lean_box(0);
v___x_5793_ = lean_array_push(v_fst_5730_, v___x_5792_);
v___x_5794_ = lean_array_push(v_fst_5734_, v___x_5765_);
if (v_isShared_5741_ == 0)
{
lean_ctor_set(v___x_5740_, 1, v___x_5769_);
lean_ctor_set(v___x_5740_, 0, v___x_5790_);
v___x_5796_ = v___x_5740_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5806_; 
v_reuseFailAlloc_5806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5806_, 0, v___x_5790_);
lean_ctor_set(v_reuseFailAlloc_5806_, 1, v___x_5769_);
v___x_5796_ = v_reuseFailAlloc_5806_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
lean_object* v___x_5798_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 1, v___x_5796_);
lean_ctor_set(v___x_5736_, 0, v___x_5794_);
v___x_5798_ = v___x_5736_;
goto v_reusejp_5797_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v___x_5794_);
lean_ctor_set(v_reuseFailAlloc_5805_, 1, v___x_5796_);
v___x_5798_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5797_;
}
v_reusejp_5797_:
{
lean_object* v___x_5800_; 
if (v_isShared_5733_ == 0)
{
lean_ctor_set(v___x_5732_, 1, v___x_5798_);
lean_ctor_set(v___x_5732_, 0, v___x_5793_);
v___x_5800_ = v___x_5732_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5804_; 
v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5804_, 0, v___x_5793_);
lean_ctor_set(v_reuseFailAlloc_5804_, 1, v___x_5798_);
v___x_5800_ = v_reuseFailAlloc_5804_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
lean_object* v___x_5802_; 
if (v_isShared_5729_ == 0)
{
lean_ctor_set(v___x_5728_, 1, v___x_5800_);
v___x_5802_ = v___x_5728_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v_fst_5726_);
lean_ctor_set(v_reuseFailAlloc_5803_, 1, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
v_a_5716_ = v___x_5802_;
goto v___jp_5715_;
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
}
}
v___jp_5715_:
{
size_t v___x_5717_; size_t v___x_5718_; 
v___x_5717_ = ((size_t)1ULL);
v___x_5718_ = lean_usize_add(v_i_5708_, v___x_5717_);
v_i_5708_ = v___x_5718_;
v_b_5709_ = v_a_5716_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7_0interp(lean_interpreter_value* stack)
{
uint8_t v_addEqualities_5705_ = stack[0].m_num;
lean_object* v_as_5706_ = stack[1].m_obj;
size_t v_sz_5707_ = stack[2].m_num;
size_t v_i_5708_ = stack[3].m_num;
lean_object* v_b_5709_ = stack[4].m_obj;
lean_object* v___y_5710_ = stack[5].m_obj;
lean_object* v___y_5711_ = stack[6].m_obj;
lean_object* v___y_5712_ = stack[7].m_obj;
lean_object* v___y_5713_ = stack[8].m_obj;
lean_object* v_res_5874_;
v_res_5874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5705_, v_as_5706_, v_sz_5707_, v_i_5708_, v_b_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_);
stack->m_obj
 = v_res_5874_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5875_, lean_object* v_as_5876_, lean_object* v_sz_5877_, lean_object* v_i_5878_, lean_object* v_b_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_){
_start:
{
uint8_t v_addEqualities_boxed_5885_; size_t v_sz_boxed_5886_; size_t v_i_boxed_5887_; lean_object* v_res_5888_; 
v_addEqualities_boxed_5885_ = lean_unbox(v_addEqualities_5875_);
v_sz_boxed_5886_ = lean_unbox_usize(v_sz_5877_);
lean_dec(v_sz_5877_);
v_i_boxed_5887_ = lean_unbox_usize(v_i_5878_);
lean_dec(v_i_5878_);
v_res_5888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5885_, v_as_5876_, v_sz_boxed_5886_, v_i_boxed_5887_, v_b_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_);
lean_dec(v___y_5883_);
lean_dec_ref(v___y_5882_);
lean_dec(v___y_5881_);
lean_dec_ref(v___y_5880_);
lean_dec_ref(v_as_5876_);
return v_res_5888_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5889_, lean_object* v_toMatcherInfo_5890_, lean_object* v_a_5891_, uint8_t v_addEqualities_5892_, size_t v___x_5893_, lean_object* v_discrs_5894_, lean_object* v_motiveArgs_5895_, lean_object* v_motiveBody_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_){
_start:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; uint8_t v___x_5996_; 
v___x_5994_ = lean_array_get_size(v_motiveArgs_5895_);
v___x_5995_ = lean_array_get_size(v_discrs_5894_);
v___x_5996_ = lean_nat_dec_eq(v___x_5994_, v___x_5995_);
if (v___x_5996_ == 0)
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6012_; 
lean_dec_ref(v_motiveBody_5896_);
lean_dec_ref(v_motiveArgs_5895_);
lean_dec_ref(v_a_5891_);
lean_dec_ref(v_toMatcherInfo_5890_);
lean_dec_ref(v_onMotive_5889_);
v___x_5997_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5998_ = l_Nat_reprFast(v___x_5995_);
v___x_5999_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5999_, 0, v___x_5998_);
v___x_6000_ = l_Lean_MessageData_ofFormat(v___x_5999_);
v___x_6001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6001_, 0, v___x_5997_);
lean_ctor_set(v___x_6001_, 1, v___x_6000_);
v___x_6002_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_6003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6003_, 0, v___x_6001_);
lean_ctor_set(v___x_6003_, 1, v___x_6002_);
v___x_6004_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6003_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
v_a_6005_ = lean_ctor_get(v___x_6004_, 0);
v_isSharedCheck_6012_ = !lean_is_exclusive(v___x_6004_);
if (v_isSharedCheck_6012_ == 0)
{
v___x_6007_ = v___x_6004_;
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___x_6004_);
v___x_6007_ = lean_box(0);
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
v_resetjp_6006_:
{
lean_object* v___x_6010_; 
if (v_isShared_6008_ == 0)
{
v___x_6010_ = v___x_6007_;
goto v_reusejp_6009_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_a_6005_);
v___x_6010_ = v_reuseFailAlloc_6011_;
goto v_reusejp_6009_;
}
v_reusejp_6009_:
{
return v___x_6010_;
}
}
}
else
{
goto v___jp_5902_;
}
v___jp_5902_:
{
lean_object* v___x_5903_; 
lean_inc(v___y_5900_);
lean_inc_ref(v___y_5899_);
lean_inc(v___y_5898_);
lean_inc_ref(v___y_5897_);
lean_inc_ref(v_motiveArgs_5895_);
v___x_5903_ = lean_apply_7(v_onMotive_5889_, v_motiveArgs_5895_, v_motiveBody_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_, lean_box(0));
if (lean_obj_tag(v___x_5903_) == 0)
{
lean_object* v_a_5904_; lean_object* v_discrInfos_5905_; lean_object* v___x_5906_; lean_object* v_addHEqualities_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; size_t v_sz_5916_; lean_object* v___x_5917_; 
v_a_5904_ = lean_ctor_get(v___x_5903_, 0);
lean_inc(v_a_5904_);
lean_dec_ref_known(v___x_5903_, 1);
v_discrInfos_5905_ = lean_ctor_get(v_toMatcherInfo_5890_, 4);
lean_inc_ref(v_discrInfos_5905_);
lean_dec_ref(v_toMatcherInfo_5890_);
v___x_5906_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5907_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5908_ = lean_array_get_size(v_a_5891_);
v___x_5909_ = l_Array_toSubarray___redArg(v_a_5891_, v___x_5906_, v___x_5908_);
v___x_5910_ = lean_array_get_size(v_discrInfos_5905_);
v___x_5911_ = l_Array_toSubarray___redArg(v_discrInfos_5905_, v___x_5906_, v___x_5910_);
v___x_5912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5909_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5913_, 0, v_addHEqualities_5907_);
lean_ctor_set(v___x_5913_, 1, v___x_5912_);
v___x_5914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5914_, 0, v_addHEqualities_5907_);
lean_ctor_set(v___x_5914_, 1, v___x_5913_);
v___x_5915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5915_, 0, v_a_5904_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v_sz_5916_ = lean_array_size(v_motiveArgs_5895_);
v___x_5917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5892_, v_motiveArgs_5895_, v_sz_5916_, v___x_5893_, v___x_5915_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
if (lean_obj_tag(v___x_5917_) == 0)
{
lean_object* v_a_5918_; lean_object* v_snd_5919_; lean_object* v_snd_5920_; lean_object* v_fst_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5976_; 
v_a_5918_ = lean_ctor_get(v___x_5917_, 0);
lean_inc(v_a_5918_);
lean_dec_ref_known(v___x_5917_, 1);
v_snd_5919_ = lean_ctor_get(v_a_5918_, 1);
lean_inc(v_snd_5919_);
v_snd_5920_ = lean_ctor_get(v_snd_5919_, 1);
lean_inc(v_snd_5920_);
v_fst_5921_ = lean_ctor_get(v_a_5918_, 0);
v_isSharedCheck_5976_ = !lean_is_exclusive(v_a_5918_);
if (v_isSharedCheck_5976_ == 0)
{
lean_object* v_unused_5977_; 
v_unused_5977_ = lean_ctor_get(v_a_5918_, 1);
lean_dec(v_unused_5977_);
v___x_5923_ = v_a_5918_;
v_isShared_5924_ = v_isSharedCheck_5976_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_fst_5921_);
lean_dec(v_a_5918_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5976_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
lean_object* v_fst_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5974_; 
v_fst_5925_ = lean_ctor_get(v_snd_5919_, 0);
v_isSharedCheck_5974_ = !lean_is_exclusive(v_snd_5919_);
if (v_isSharedCheck_5974_ == 0)
{
lean_object* v_unused_5975_; 
v_unused_5975_ = lean_ctor_get(v_snd_5919_, 1);
lean_dec(v_unused_5975_);
v___x_5927_ = v_snd_5919_;
v_isShared_5928_ = v_isSharedCheck_5974_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_fst_5925_);
lean_dec(v_snd_5919_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5974_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v_fst_5929_; lean_object* v___x_5931_; uint8_t v_isShared_5932_; uint8_t v_isSharedCheck_5972_; 
v_fst_5929_ = lean_ctor_get(v_snd_5920_, 0);
v_isSharedCheck_5972_ = !lean_is_exclusive(v_snd_5920_);
if (v_isSharedCheck_5972_ == 0)
{
lean_object* v_unused_5973_; 
v_unused_5973_ = lean_ctor_get(v_snd_5920_, 1);
lean_dec(v_unused_5973_);
v___x_5931_ = v_snd_5920_;
v_isShared_5932_ = v_isSharedCheck_5972_;
goto v_resetjp_5930_;
}
else
{
lean_inc(v_fst_5929_);
lean_dec(v_snd_5920_);
v___x_5931_ = lean_box(0);
v_isShared_5932_ = v_isSharedCheck_5972_;
goto v_resetjp_5930_;
}
v_resetjp_5930_:
{
uint8_t v___x_5933_; uint8_t v___x_5934_; uint8_t v___x_5935_; lean_object* v___x_5936_; 
v___x_5933_ = 0;
v___x_5934_ = 1;
v___x_5935_ = 1;
lean_inc(v_fst_5921_);
v___x_5936_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5895_, v_fst_5921_, v___x_5933_, v___x_5934_, v___x_5933_, v___x_5934_, v___x_5935_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
lean_dec_ref(v_motiveArgs_5895_);
if (lean_obj_tag(v___x_5936_) == 0)
{
lean_object* v_a_5937_; lean_object* v___x_5938_; 
v_a_5937_ = lean_ctor_get(v___x_5936_, 0);
lean_inc(v_a_5937_);
lean_dec_ref_known(v___x_5936_, 1);
v___x_5938_ = l_Lean_Meta_getLevel(v_fst_5921_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
if (lean_obj_tag(v___x_5938_) == 0)
{
lean_object* v_a_5939_; lean_object* v___x_5941_; uint8_t v_isShared_5942_; uint8_t v_isSharedCheck_5955_; 
v_a_5939_ = lean_ctor_get(v___x_5938_, 0);
v_isSharedCheck_5955_ = !lean_is_exclusive(v___x_5938_);
if (v_isSharedCheck_5955_ == 0)
{
v___x_5941_ = v___x_5938_;
v_isShared_5942_ = v_isSharedCheck_5955_;
goto v_resetjp_5940_;
}
else
{
lean_inc(v_a_5939_);
lean_dec(v___x_5938_);
v___x_5941_ = lean_box(0);
v_isShared_5942_ = v_isSharedCheck_5955_;
goto v_resetjp_5940_;
}
v_resetjp_5940_:
{
lean_object* v___x_5944_; 
if (v_isShared_5932_ == 0)
{
lean_ctor_set(v___x_5931_, 1, v_fst_5929_);
lean_ctor_set(v___x_5931_, 0, v_fst_5925_);
v___x_5944_ = v___x_5931_;
goto v_reusejp_5943_;
}
else
{
lean_object* v_reuseFailAlloc_5954_; 
v_reuseFailAlloc_5954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5954_, 0, v_fst_5925_);
lean_ctor_set(v_reuseFailAlloc_5954_, 1, v_fst_5929_);
v___x_5944_ = v_reuseFailAlloc_5954_;
goto v_reusejp_5943_;
}
v_reusejp_5943_:
{
lean_object* v___x_5946_; 
if (v_isShared_5928_ == 0)
{
lean_ctor_set(v___x_5927_, 1, v___x_5944_);
lean_ctor_set(v___x_5927_, 0, v_a_5939_);
v___x_5946_ = v___x_5927_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5953_; 
v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5953_, 0, v_a_5939_);
lean_ctor_set(v_reuseFailAlloc_5953_, 1, v___x_5944_);
v___x_5946_ = v_reuseFailAlloc_5953_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
lean_object* v___x_5948_; 
if (v_isShared_5924_ == 0)
{
lean_ctor_set(v___x_5923_, 1, v___x_5946_);
lean_ctor_set(v___x_5923_, 0, v_a_5937_);
v___x_5948_ = v___x_5923_;
goto v_reusejp_5947_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5937_);
lean_ctor_set(v_reuseFailAlloc_5952_, 1, v___x_5946_);
v___x_5948_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5947_;
}
v_reusejp_5947_:
{
lean_object* v___x_5950_; 
if (v_isShared_5942_ == 0)
{
lean_ctor_set(v___x_5941_, 0, v___x_5948_);
v___x_5950_ = v___x_5941_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5951_; 
v_reuseFailAlloc_5951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5951_, 0, v___x_5948_);
v___x_5950_ = v_reuseFailAlloc_5951_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
return v___x_5950_;
}
}
}
}
}
}
else
{
lean_object* v_a_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5963_; 
lean_dec(v_a_5937_);
lean_del_object(v___x_5931_);
lean_dec(v_fst_5929_);
lean_del_object(v___x_5927_);
lean_dec(v_fst_5925_);
lean_del_object(v___x_5923_);
v_a_5956_ = lean_ctor_get(v___x_5938_, 0);
v_isSharedCheck_5963_ = !lean_is_exclusive(v___x_5938_);
if (v_isSharedCheck_5963_ == 0)
{
v___x_5958_ = v___x_5938_;
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_a_5956_);
lean_dec(v___x_5938_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5963_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5961_; 
if (v_isShared_5959_ == 0)
{
v___x_5961_ = v___x_5958_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v_a_5956_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
}
}
else
{
lean_object* v_a_5964_; lean_object* v___x_5966_; uint8_t v_isShared_5967_; uint8_t v_isSharedCheck_5971_; 
lean_del_object(v___x_5931_);
lean_dec(v_fst_5929_);
lean_del_object(v___x_5927_);
lean_dec(v_fst_5925_);
lean_del_object(v___x_5923_);
lean_dec(v_fst_5921_);
v_a_5964_ = lean_ctor_get(v___x_5936_, 0);
v_isSharedCheck_5971_ = !lean_is_exclusive(v___x_5936_);
if (v_isSharedCheck_5971_ == 0)
{
v___x_5966_ = v___x_5936_;
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
else
{
lean_inc(v_a_5964_);
lean_dec(v___x_5936_);
v___x_5966_ = lean_box(0);
v_isShared_5967_ = v_isSharedCheck_5971_;
goto v_resetjp_5965_;
}
v_resetjp_5965_:
{
lean_object* v___x_5969_; 
if (v_isShared_5967_ == 0)
{
v___x_5969_ = v___x_5966_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_a_5964_);
v___x_5969_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
return v___x_5969_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5978_; lean_object* v___x_5980_; uint8_t v_isShared_5981_; uint8_t v_isSharedCheck_5985_; 
lean_dec_ref(v_motiveArgs_5895_);
v_a_5978_ = lean_ctor_get(v___x_5917_, 0);
v_isSharedCheck_5985_ = !lean_is_exclusive(v___x_5917_);
if (v_isSharedCheck_5985_ == 0)
{
v___x_5980_ = v___x_5917_;
v_isShared_5981_ = v_isSharedCheck_5985_;
goto v_resetjp_5979_;
}
else
{
lean_inc(v_a_5978_);
lean_dec(v___x_5917_);
v___x_5980_ = lean_box(0);
v_isShared_5981_ = v_isSharedCheck_5985_;
goto v_resetjp_5979_;
}
v_resetjp_5979_:
{
lean_object* v___x_5983_; 
if (v_isShared_5981_ == 0)
{
v___x_5983_ = v___x_5980_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_a_5978_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
return v___x_5983_;
}
}
}
}
else
{
lean_object* v_a_5986_; lean_object* v___x_5988_; uint8_t v_isShared_5989_; uint8_t v_isSharedCheck_5993_; 
lean_dec_ref(v_motiveArgs_5895_);
lean_dec_ref(v_a_5891_);
lean_dec_ref(v_toMatcherInfo_5890_);
v_a_5986_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_5993_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_5993_ == 0)
{
v___x_5988_ = v___x_5903_;
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
else
{
lean_inc(v_a_5986_);
lean_dec(v___x_5903_);
v___x_5988_ = lean_box(0);
v_isShared_5989_ = v_isSharedCheck_5993_;
goto v_resetjp_5987_;
}
v_resetjp_5987_:
{
lean_object* v___x_5991_; 
if (v_isShared_5989_ == 0)
{
v___x_5991_ = v___x_5988_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_a_5986_);
v___x_5991_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
return v___x_5991_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_onMotive_5889_ = stack[0].m_obj;
lean_object* v_toMatcherInfo_5890_ = stack[1].m_obj;
lean_object* v_a_5891_ = stack[2].m_obj;
uint8_t v_addEqualities_5892_ = stack[3].m_num;
size_t v___x_5893_ = stack[4].m_num;
lean_object* v_discrs_5894_ = stack[5].m_obj;
lean_object* v_motiveArgs_5895_ = stack[6].m_obj;
lean_object* v_motiveBody_5896_ = stack[7].m_obj;
lean_object* v___y_5897_ = stack[8].m_obj;
lean_object* v___y_5898_ = stack[9].m_obj;
lean_object* v___y_5899_ = stack[10].m_obj;
lean_object* v___y_5900_ = stack[11].m_obj;
lean_object* v_res_6013_;
v_res_6013_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5889_, v_toMatcherInfo_5890_, v_a_5891_, v_addEqualities_5892_, v___x_5893_, v_discrs_5894_, v_motiveArgs_5895_, v_motiveBody_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
stack->m_obj
 = v_res_6013_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_6014_, lean_object* v_toMatcherInfo_6015_, lean_object* v_a_6016_, lean_object* v_addEqualities_6017_, lean_object* v___x_6018_, lean_object* v_discrs_6019_, lean_object* v_motiveArgs_6020_, lean_object* v_motiveBody_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_){
_start:
{
uint8_t v_addEqualities_boxed_6027_; size_t v___x_35734__boxed_6028_; lean_object* v_res_6029_; 
v_addEqualities_boxed_6027_ = lean_unbox(v_addEqualities_6017_);
v___x_35734__boxed_6028_ = lean_unbox_usize(v___x_6018_);
lean_dec(v___x_6018_);
v_res_6029_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_6014_, v_toMatcherInfo_6015_, v_a_6016_, v_addEqualities_boxed_6027_, v___x_35734__boxed_6028_, v_discrs_6019_, v_motiveArgs_6020_, v_motiveBody_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_);
lean_dec(v___y_6025_);
lean_dec_ref(v___y_6024_);
lean_dec(v___y_6023_);
lean_dec_ref(v___y_6022_);
lean_dec_ref(v_discrs_6019_);
return v_res_6029_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_6030_, size_t v_sz_6031_, size_t v_i_6032_, lean_object* v_b_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_){
_start:
{
lean_object* v_a_6040_; uint8_t v___x_6044_; 
v___x_6044_ = lean_usize_dec_lt(v_i_6032_, v_sz_6031_);
if (v___x_6044_ == 0)
{
lean_object* v___x_6045_; 
v___x_6045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6045_, 0, v_b_6033_);
return v___x_6045_;
}
else
{
lean_object* v_snd_6046_; lean_object* v_snd_6047_; lean_object* v_fst_6048_; lean_object* v___x_6050_; uint8_t v_isShared_6051_; uint8_t v_isSharedCheck_6108_; 
v_snd_6046_ = lean_ctor_get(v_b_6033_, 1);
lean_inc(v_snd_6046_);
v_snd_6047_ = lean_ctor_get(v_snd_6046_, 1);
lean_inc(v_snd_6047_);
v_fst_6048_ = lean_ctor_get(v_b_6033_, 0);
v_isSharedCheck_6108_ = !lean_is_exclusive(v_b_6033_);
if (v_isSharedCheck_6108_ == 0)
{
lean_object* v_unused_6109_; 
v_unused_6109_ = lean_ctor_get(v_b_6033_, 1);
lean_dec(v_unused_6109_);
v___x_6050_ = v_b_6033_;
v_isShared_6051_ = v_isSharedCheck_6108_;
goto v_resetjp_6049_;
}
else
{
lean_inc(v_fst_6048_);
lean_dec(v_b_6033_);
v___x_6050_ = lean_box(0);
v_isShared_6051_ = v_isSharedCheck_6108_;
goto v_resetjp_6049_;
}
v_resetjp_6049_:
{
lean_object* v_fst_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6106_; 
v_fst_6052_ = lean_ctor_get(v_snd_6046_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v_snd_6046_);
if (v_isSharedCheck_6106_ == 0)
{
lean_object* v_unused_6107_; 
v_unused_6107_ = lean_ctor_get(v_snd_6046_, 1);
lean_dec(v_unused_6107_);
v___x_6054_ = v_snd_6046_;
v_isShared_6055_ = v_isSharedCheck_6106_;
goto v_resetjp_6053_;
}
else
{
lean_inc(v_fst_6052_);
lean_dec(v_snd_6046_);
v___x_6054_ = lean_box(0);
v_isShared_6055_ = v_isSharedCheck_6106_;
goto v_resetjp_6053_;
}
v_resetjp_6053_:
{
lean_object* v_array_6056_; lean_object* v_start_6057_; lean_object* v_stop_6058_; uint8_t v___x_6059_; 
v_array_6056_ = lean_ctor_get(v_snd_6047_, 0);
v_start_6057_ = lean_ctor_get(v_snd_6047_, 1);
v_stop_6058_ = lean_ctor_get(v_snd_6047_, 2);
v___x_6059_ = lean_nat_dec_lt(v_start_6057_, v_stop_6058_);
if (v___x_6059_ == 0)
{
lean_object* v___x_6061_; 
if (v_isShared_6055_ == 0)
{
v___x_6061_ = v___x_6054_;
goto v_reusejp_6060_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_fst_6052_);
lean_ctor_set(v_reuseFailAlloc_6066_, 1, v_snd_6047_);
v___x_6061_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6060_;
}
v_reusejp_6060_:
{
lean_object* v___x_6063_; 
if (v_isShared_6051_ == 0)
{
lean_ctor_set(v___x_6050_, 1, v___x_6061_);
v___x_6063_ = v___x_6050_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_fst_6048_);
lean_ctor_set(v_reuseFailAlloc_6065_, 1, v___x_6061_);
v___x_6063_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
lean_object* v___x_6064_; 
v___x_6064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6064_, 0, v___x_6063_);
return v___x_6064_;
}
}
}
else
{
lean_object* v___x_6068_; uint8_t v_isShared_6069_; uint8_t v_isSharedCheck_6102_; 
lean_inc(v_stop_6058_);
lean_inc(v_start_6057_);
lean_inc_ref(v_array_6056_);
v_isSharedCheck_6102_ = !lean_is_exclusive(v_snd_6047_);
if (v_isSharedCheck_6102_ == 0)
{
lean_object* v_unused_6103_; lean_object* v_unused_6104_; lean_object* v_unused_6105_; 
v_unused_6103_ = lean_ctor_get(v_snd_6047_, 2);
lean_dec(v_unused_6103_);
v_unused_6104_ = lean_ctor_get(v_snd_6047_, 1);
lean_dec(v_unused_6104_);
v_unused_6105_ = lean_ctor_get(v_snd_6047_, 0);
lean_dec(v_unused_6105_);
v___x_6068_ = v_snd_6047_;
v_isShared_6069_ = v_isSharedCheck_6102_;
goto v_resetjp_6067_;
}
else
{
lean_dec(v_snd_6047_);
v___x_6068_ = lean_box(0);
v_isShared_6069_ = v_isSharedCheck_6102_;
goto v_resetjp_6067_;
}
v_resetjp_6067_:
{
lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6074_; 
v___x_6070_ = lean_array_fget(v_array_6056_, v_start_6057_);
v___x_6071_ = lean_unsigned_to_nat(1u);
v___x_6072_ = lean_nat_add(v_start_6057_, v___x_6071_);
lean_dec(v_start_6057_);
if (v_isShared_6069_ == 0)
{
lean_ctor_set(v___x_6068_, 1, v___x_6072_);
v___x_6074_ = v___x_6068_;
goto v_reusejp_6073_;
}
else
{
lean_object* v_reuseFailAlloc_6101_; 
v_reuseFailAlloc_6101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6101_, 0, v_array_6056_);
lean_ctor_set(v_reuseFailAlloc_6101_, 1, v___x_6072_);
lean_ctor_set(v_reuseFailAlloc_6101_, 2, v_stop_6058_);
v___x_6074_ = v_reuseFailAlloc_6101_;
goto v_reusejp_6073_;
}
v_reusejp_6073_:
{
lean_object* v___y_6076_; 
if (lean_obj_tag(v___x_6070_) == 0)
{
lean_object* v___x_6094_; lean_object* v___x_6095_; 
lean_del_object(v___x_6054_);
lean_del_object(v___x_6050_);
v___x_6094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6094_, 0, v_fst_6052_);
lean_ctor_set(v___x_6094_, 1, v___x_6074_);
v___x_6095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6095_, 0, v_fst_6048_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v_a_6040_ = v___x_6095_;
goto v___jp_6039_;
}
else
{
lean_object* v_val_6096_; lean_object* v_a_6097_; uint8_t v___x_6098_; 
v_val_6096_ = lean_ctor_get(v___x_6070_, 0);
lean_inc(v_val_6096_);
lean_dec_ref_known(v___x_6070_, 1);
v_a_6097_ = lean_array_uget_borrowed(v_as_6030_, v_i_6032_);
v___x_6098_ = lean_unbox(v_val_6096_);
lean_dec(v_val_6096_);
if (v___x_6098_ == 0)
{
lean_object* v___x_6099_; 
lean_inc(v_a_6097_);
v___x_6099_ = l_Lean_Meta_mkEqRefl(v_a_6097_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
v___y_6076_ = v___x_6099_;
goto v___jp_6075_;
}
else
{
lean_object* v___x_6100_; 
lean_inc(v_a_6097_);
v___x_6100_ = l_Lean_Meta_mkHEqRefl(v_a_6097_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
v___y_6076_ = v___x_6100_;
goto v___jp_6075_;
}
}
v___jp_6075_:
{
if (lean_obj_tag(v___y_6076_) == 0)
{
lean_object* v_a_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6081_; 
v_a_6077_ = lean_ctor_get(v___y_6076_, 0);
lean_inc(v_a_6077_);
lean_dec_ref_known(v___y_6076_, 1);
v___x_6078_ = lean_array_push(v_fst_6048_, v_a_6077_);
v___x_6079_ = lean_nat_add(v_fst_6052_, v___x_6071_);
lean_dec(v_fst_6052_);
if (v_isShared_6055_ == 0)
{
lean_ctor_set(v___x_6054_, 1, v___x_6074_);
lean_ctor_set(v___x_6054_, 0, v___x_6079_);
v___x_6081_ = v___x_6054_;
goto v_reusejp_6080_;
}
else
{
lean_object* v_reuseFailAlloc_6085_; 
v_reuseFailAlloc_6085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6085_, 0, v___x_6079_);
lean_ctor_set(v_reuseFailAlloc_6085_, 1, v___x_6074_);
v___x_6081_ = v_reuseFailAlloc_6085_;
goto v_reusejp_6080_;
}
v_reusejp_6080_:
{
lean_object* v___x_6083_; 
if (v_isShared_6051_ == 0)
{
lean_ctor_set(v___x_6050_, 1, v___x_6081_);
lean_ctor_set(v___x_6050_, 0, v___x_6078_);
v___x_6083_ = v___x_6050_;
goto v_reusejp_6082_;
}
else
{
lean_object* v_reuseFailAlloc_6084_; 
v_reuseFailAlloc_6084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6084_, 0, v___x_6078_);
lean_ctor_set(v_reuseFailAlloc_6084_, 1, v___x_6081_);
v___x_6083_ = v_reuseFailAlloc_6084_;
goto v_reusejp_6082_;
}
v_reusejp_6082_:
{
v_a_6040_ = v___x_6083_;
goto v___jp_6039_;
}
}
}
else
{
lean_object* v_a_6086_; lean_object* v___x_6088_; uint8_t v_isShared_6089_; uint8_t v_isSharedCheck_6093_; 
lean_dec_ref(v___x_6074_);
lean_del_object(v___x_6054_);
lean_dec(v_fst_6052_);
lean_del_object(v___x_6050_);
lean_dec(v_fst_6048_);
v_a_6086_ = lean_ctor_get(v___y_6076_, 0);
v_isSharedCheck_6093_ = !lean_is_exclusive(v___y_6076_);
if (v_isSharedCheck_6093_ == 0)
{
v___x_6088_ = v___y_6076_;
v_isShared_6089_ = v_isSharedCheck_6093_;
goto v_resetjp_6087_;
}
else
{
lean_inc(v_a_6086_);
lean_dec(v___y_6076_);
v___x_6088_ = lean_box(0);
v_isShared_6089_ = v_isSharedCheck_6093_;
goto v_resetjp_6087_;
}
v_resetjp_6087_:
{
lean_object* v___x_6091_; 
if (v_isShared_6089_ == 0)
{
v___x_6091_ = v___x_6088_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6092_; 
v_reuseFailAlloc_6092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6092_, 0, v_a_6086_);
v___x_6091_ = v_reuseFailAlloc_6092_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
return v___x_6091_;
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
v___jp_6039_:
{
size_t v___x_6041_; size_t v___x_6042_; 
v___x_6041_ = ((size_t)1ULL);
v___x_6042_ = lean_usize_add(v_i_6032_, v___x_6041_);
v_i_6032_ = v___x_6042_;
v_b_6033_ = v_a_6040_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_6030_ = stack[0].m_obj;
size_t v_sz_6031_ = stack[1].m_num;
size_t v_i_6032_ = stack[2].m_num;
lean_object* v_b_6033_ = stack[3].m_obj;
lean_object* v___y_6034_ = stack[4].m_obj;
lean_object* v___y_6035_ = stack[5].m_obj;
lean_object* v___y_6036_ = stack[6].m_obj;
lean_object* v___y_6037_ = stack[7].m_obj;
lean_object* v_res_6110_;
v_res_6110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6030_, v_sz_6031_, v_i_6032_, v_b_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
stack->m_obj
 = v_res_6110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6111_, lean_object* v_sz_6112_, lean_object* v_i_6113_, lean_object* v_b_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_){
_start:
{
size_t v_sz_boxed_6120_; size_t v_i_boxed_6121_; lean_object* v_res_6122_; 
v_sz_boxed_6120_ = lean_unbox_usize(v_sz_6112_);
lean_dec(v_sz_6112_);
v_i_boxed_6121_ = lean_unbox_usize(v_i_6113_);
lean_dec(v_i_6113_);
v_res_6122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6111_, v_sz_boxed_6120_, v_i_boxed_6121_, v_b_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_);
lean_dec(v___y_6118_);
lean_dec_ref(v___y_6117_);
lean_dec(v___y_6116_);
lean_dec_ref(v___y_6115_);
lean_dec_ref(v_as_6111_);
return v_res_6122_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_){
_start:
{
lean_object* v___x_6129_; 
v___x_6129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6123_);
return v___x_6129_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_6123_ = stack[0].m_obj;
lean_object* v___y_6124_ = stack[1].m_obj;
lean_object* v___y_6125_ = stack[2].m_obj;
lean_object* v___y_6126_ = stack[3].m_obj;
lean_object* v___y_6127_ = stack[4].m_obj;
lean_object* v_res_6130_;
v_res_6130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_);
stack->m_obj
 = v_res_6130_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_){
_start:
{
lean_object* v_res_6137_; 
v_res_6137_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6131_, v___y_6132_, v___y_6133_, v___y_6134_, v___y_6135_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
lean_dec(v___y_6133_);
lean_dec_ref(v___y_6132_);
return v_res_6137_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6138_, size_t v_i_6139_, lean_object* v_bs_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_){
_start:
{
uint8_t v___x_6145_; 
v___x_6145_ = lean_usize_dec_lt(v_i_6139_, v_sz_6138_);
if (v___x_6145_ == 0)
{
lean_object* v___x_6146_; 
v___x_6146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6146_, 0, v_bs_6140_);
return v___x_6146_;
}
else
{
lean_object* v_v_6147_; lean_object* v___x_6148_; lean_object* v_bs_x27_6149_; lean_object* v___x_6150_; lean_object* v___x_6151_; 
v_v_6147_ = lean_array_uget(v_bs_6140_, v_i_6139_);
v___x_6148_ = lean_unsigned_to_nat(0u);
v_bs_x27_6149_ = lean_array_uset(v_bs_6140_, v_i_6139_, v___x_6148_);
v___x_6150_ = l_Lean_Expr_fvarId_x21(v_v_6147_);
lean_dec(v_v_6147_);
v___x_6151_ = l_Lean_FVarId_getUserName___redArg(v___x_6150_, v___y_6141_, v___y_6142_, v___y_6143_);
if (lean_obj_tag(v___x_6151_) == 0)
{
lean_object* v_a_6152_; size_t v___x_6153_; size_t v___x_6154_; lean_object* v___x_6155_; 
v_a_6152_ = lean_ctor_get(v___x_6151_, 0);
lean_inc(v_a_6152_);
lean_dec_ref_known(v___x_6151_, 1);
v___x_6153_ = ((size_t)1ULL);
v___x_6154_ = lean_usize_add(v_i_6139_, v___x_6153_);
v___x_6155_ = lean_array_uset(v_bs_x27_6149_, v_i_6139_, v_a_6152_);
v_i_6139_ = v___x_6154_;
v_bs_6140_ = v___x_6155_;
goto _start;
}
else
{
lean_object* v_a_6157_; lean_object* v___x_6159_; uint8_t v_isShared_6160_; uint8_t v_isSharedCheck_6164_; 
lean_dec_ref(v_bs_x27_6149_);
v_a_6157_ = lean_ctor_get(v___x_6151_, 0);
v_isSharedCheck_6164_ = !lean_is_exclusive(v___x_6151_);
if (v_isSharedCheck_6164_ == 0)
{
v___x_6159_ = v___x_6151_;
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
else
{
lean_inc(v_a_6157_);
lean_dec(v___x_6151_);
v___x_6159_ = lean_box(0);
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
v_resetjp_6158_:
{
lean_object* v___x_6162_; 
if (v_isShared_6160_ == 0)
{
v___x_6162_ = v___x_6159_;
goto v_reusejp_6161_;
}
else
{
lean_object* v_reuseFailAlloc_6163_; 
v_reuseFailAlloc_6163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_a_6157_);
v___x_6162_ = v_reuseFailAlloc_6163_;
goto v_reusejp_6161_;
}
v_reusejp_6161_:
{
return v___x_6162_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_sz_6138_ = stack[0].m_num;
size_t v_i_6139_ = stack[1].m_num;
lean_object* v_bs_6140_ = stack[2].m_obj;
lean_object* v___y_6141_ = stack[3].m_obj;
lean_object* v___y_6142_ = stack[4].m_obj;
lean_object* v___y_6143_ = stack[5].m_obj;
lean_object* v_res_6165_;
v_res_6165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6138_, v_i_6139_, v_bs_6140_, v___y_6141_, v___y_6142_, v___y_6143_);
stack->m_obj
 = v_res_6165_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6166_, lean_object* v_i_6167_, lean_object* v_bs_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_){
_start:
{
size_t v_sz_boxed_6173_; size_t v_i_boxed_6174_; lean_object* v_res_6175_; 
v_sz_boxed_6173_ = lean_unbox_usize(v_sz_6166_);
lean_dec(v_sz_6166_);
v_i_boxed_6174_ = lean_unbox_usize(v_i_6167_);
lean_dec(v_i_6167_);
v_res_6175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6173_, v_i_boxed_6174_, v_bs_6168_, v___y_6169_, v___y_6170_, v___y_6171_);
lean_dec(v___y_6171_);
lean_dec_ref(v___y_6170_);
lean_dec_ref(v___y_6169_);
return v_res_6175_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6176_, lean_object* v_x_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_){
_start:
{
size_t v_sz_6183_; size_t v___x_6184_; lean_object* v___x_6185_; 
v_sz_6183_ = lean_array_size(v_xs_6176_);
v___x_6184_ = ((size_t)0ULL);
v___x_6185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6183_, v___x_6184_, v_xs_6176_, v___y_6178_, v___y_6180_, v___y_6181_);
return v___x_6185_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_6176_ = stack[0].m_obj;
lean_object* v_x_6177_ = stack[1].m_obj;
lean_object* v___y_6178_ = stack[2].m_obj;
lean_object* v___y_6179_ = stack[3].m_obj;
lean_object* v___y_6180_ = stack[4].m_obj;
lean_object* v___y_6181_ = stack[5].m_obj;
lean_object* v_res_6186_;
v_res_6186_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6176_, v_x_6177_, v___y_6178_, v___y_6179_, v___y_6180_, v___y_6181_);
stack->m_obj
 = v_res_6186_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6187_, lean_object* v_x_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_){
_start:
{
lean_object* v_res_6194_; 
v_res_6194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6187_, v_x_6188_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec_ref(v_x_6188_);
return v_res_6194_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6195_, lean_object* v___x_6196_, lean_object* v___f_6197_, uint8_t v___x_6198_, lean_object* v_fst_6199_, lean_object* v___x_6200_, lean_object* v___x_6201_, lean_object* v___x_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_){
_start:
{
lean_object* v___x_6208_; 
v___x_6208_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v___x_6195_, v___x_6196_, v___f_6197_, v___x_6198_, v___x_6198_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_);
if (lean_obj_tag(v___x_6208_) == 0)
{
lean_object* v_a_6209_; lean_object* v___x_6211_; uint8_t v_isShared_6212_; uint8_t v_isSharedCheck_6221_; 
v_a_6209_ = lean_ctor_get(v___x_6208_, 0);
v_isSharedCheck_6221_ = !lean_is_exclusive(v___x_6208_);
if (v_isSharedCheck_6221_ == 0)
{
v___x_6211_ = v___x_6208_;
v_isShared_6212_ = v_isSharedCheck_6221_;
goto v_resetjp_6210_;
}
else
{
lean_inc(v_a_6209_);
lean_dec(v___x_6208_);
v___x_6211_ = lean_box(0);
v_isShared_6212_ = v_isSharedCheck_6221_;
goto v_resetjp_6210_;
}
v_resetjp_6210_:
{
lean_object* v___x_6213_; lean_object* v___x_6214_; lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; lean_object* v___x_6219_; 
v___x_6213_ = lean_array_push(v_fst_6199_, v_a_6209_);
v___x_6214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6214_, 0, v___x_6200_);
lean_ctor_set(v___x_6214_, 1, v___x_6201_);
v___x_6215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6215_, 0, v___x_6202_);
lean_ctor_set(v___x_6215_, 1, v___x_6214_);
v___x_6216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6216_, 0, v___x_6213_);
lean_ctor_set(v___x_6216_, 1, v___x_6215_);
v___x_6217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6216_);
if (v_isShared_6212_ == 0)
{
lean_ctor_set(v___x_6211_, 0, v___x_6217_);
v___x_6219_ = v___x_6211_;
goto v_reusejp_6218_;
}
else
{
lean_object* v_reuseFailAlloc_6220_; 
v_reuseFailAlloc_6220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6220_, 0, v___x_6217_);
v___x_6219_ = v_reuseFailAlloc_6220_;
goto v_reusejp_6218_;
}
v_reusejp_6218_:
{
return v___x_6219_;
}
}
}
else
{
lean_object* v_a_6222_; lean_object* v___x_6224_; uint8_t v_isShared_6225_; uint8_t v_isSharedCheck_6229_; 
lean_dec_ref(v___x_6202_);
lean_dec_ref(v___x_6201_);
lean_dec_ref(v___x_6200_);
lean_dec(v_fst_6199_);
v_a_6222_ = lean_ctor_get(v___x_6208_, 0);
v_isSharedCheck_6229_ = !lean_is_exclusive(v___x_6208_);
if (v_isSharedCheck_6229_ == 0)
{
v___x_6224_ = v___x_6208_;
v_isShared_6225_ = v_isSharedCheck_6229_;
goto v_resetjp_6223_;
}
else
{
lean_inc(v_a_6222_);
lean_dec(v___x_6208_);
v___x_6224_ = lean_box(0);
v_isShared_6225_ = v_isSharedCheck_6229_;
goto v_resetjp_6223_;
}
v_resetjp_6223_:
{
lean_object* v___x_6227_; 
if (v_isShared_6225_ == 0)
{
v___x_6227_ = v___x_6224_;
goto v_reusejp_6226_;
}
else
{
lean_object* v_reuseFailAlloc_6228_; 
v_reuseFailAlloc_6228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_a_6222_);
v___x_6227_ = v_reuseFailAlloc_6228_;
goto v_reusejp_6226_;
}
v_reusejp_6226_:
{
return v___x_6227_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_6195_ = stack[0].m_obj;
lean_object* v___x_6196_ = stack[1].m_obj;
lean_object* v___f_6197_ = stack[2].m_obj;
uint8_t v___x_6198_ = stack[3].m_num;
lean_object* v_fst_6199_ = stack[4].m_obj;
lean_object* v___x_6200_ = stack[5].m_obj;
lean_object* v___x_6201_ = stack[6].m_obj;
lean_object* v___x_6202_ = stack[7].m_obj;
lean_object* v___y_6203_ = stack[8].m_obj;
lean_object* v___y_6204_ = stack[9].m_obj;
lean_object* v___y_6205_ = stack[10].m_obj;
lean_object* v___y_6206_ = stack[11].m_obj;
lean_object* v_res_6230_;
v_res_6230_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6195_, v___x_6196_, v___f_6197_, v___x_6198_, v_fst_6199_, v___x_6200_, v___x_6201_, v___x_6202_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_);
stack->m_obj
 = v_res_6230_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6231_, lean_object* v___x_6232_, lean_object* v___f_6233_, lean_object* v___x_6234_, lean_object* v_fst_6235_, lean_object* v___x_6236_, lean_object* v___x_6237_, lean_object* v___x_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_){
_start:
{
uint8_t v___x_36440__boxed_6244_; lean_object* v_res_6245_; 
v___x_36440__boxed_6244_ = lean_unbox(v___x_6234_);
v_res_6245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6231_, v___x_6232_, v___f_6233_, v___x_36440__boxed_6244_, v_fst_6235_, v___x_6236_, v___x_6237_, v___x_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_);
lean_dec(v___y_6242_);
lean_dec_ref(v___y_6241_);
lean_dec(v___y_6240_);
lean_dec_ref(v___y_6239_);
return v_res_6245_;
}
}
lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6246_, lean_object* v_names_6247_, lean_object* v_k_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
lean_object* v___x_6254_; 
v___x_6254_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6246_, v_names_6247_, v_k_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_);
if (lean_obj_tag(v___x_6254_) == 0)
{
lean_object* v_a_6255_; lean_object* v___x_6257_; uint8_t v_isShared_6258_; uint8_t v_isSharedCheck_6262_; 
v_a_6255_ = lean_ctor_get(v___x_6254_, 0);
v_isSharedCheck_6262_ = !lean_is_exclusive(v___x_6254_);
if (v_isSharedCheck_6262_ == 0)
{
v___x_6257_ = v___x_6254_;
v_isShared_6258_ = v_isSharedCheck_6262_;
goto v_resetjp_6256_;
}
else
{
lean_inc(v_a_6255_);
lean_dec(v___x_6254_);
v___x_6257_ = lean_box(0);
v_isShared_6258_ = v_isSharedCheck_6262_;
goto v_resetjp_6256_;
}
v_resetjp_6256_:
{
lean_object* v___x_6260_; 
if (v_isShared_6258_ == 0)
{
v___x_6260_ = v___x_6257_;
goto v_reusejp_6259_;
}
else
{
lean_object* v_reuseFailAlloc_6261_; 
v_reuseFailAlloc_6261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_a_6255_);
v___x_6260_ = v_reuseFailAlloc_6261_;
goto v_reusejp_6259_;
}
v_reusejp_6259_:
{
return v___x_6260_;
}
}
}
else
{
lean_object* v_a_6263_; lean_object* v___x_6265_; uint8_t v_isShared_6266_; uint8_t v_isSharedCheck_6270_; 
v_a_6263_ = lean_ctor_get(v___x_6254_, 0);
v_isSharedCheck_6270_ = !lean_is_exclusive(v___x_6254_);
if (v_isSharedCheck_6270_ == 0)
{
v___x_6265_ = v___x_6254_;
v_isShared_6266_ = v_isSharedCheck_6270_;
goto v_resetjp_6264_;
}
else
{
lean_inc(v_a_6263_);
lean_dec(v___x_6254_);
v___x_6265_ = lean_box(0);
v_isShared_6266_ = v_isSharedCheck_6270_;
goto v_resetjp_6264_;
}
v_resetjp_6264_:
{
lean_object* v___x_6268_; 
if (v_isShared_6266_ == 0)
{
v___x_6268_ = v___x_6265_;
goto v_reusejp_6267_;
}
else
{
lean_object* v_reuseFailAlloc_6269_; 
v_reuseFailAlloc_6269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6269_, 0, v_a_6263_);
v___x_6268_ = v_reuseFailAlloc_6269_;
goto v_reusejp_6267_;
}
v_reusejp_6267_:
{
return v___x_6268_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_6246_ = stack[0].m_obj;
lean_object* v_names_6247_ = stack[1].m_obj;
lean_object* v_k_6248_ = stack[2].m_obj;
lean_object* v___y_6249_ = stack[3].m_obj;
lean_object* v___y_6250_ = stack[4].m_obj;
lean_object* v___y_6251_ = stack[5].m_obj;
lean_object* v___y_6252_ = stack[6].m_obj;
lean_object* v_res_6271_;
v_res_6271_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6246_, v_names_6247_, v_k_6248_, v___y_6249_, v___y_6250_, v___y_6251_, v___y_6252_);
stack->m_obj
 = v_res_6271_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6272_, lean_object* v_names_6273_, lean_object* v_k_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_){
_start:
{
lean_object* v_res_6280_; 
v_res_6280_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6272_, v_names_6273_, v_k_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_);
lean_dec(v___y_6278_);
lean_dec_ref(v___y_6277_);
lean_dec(v___y_6276_);
lean_dec_ref(v___y_6275_);
lean_dec_ref(v_names_6273_);
lean_dec_ref(v_fvars_6272_);
return v_res_6280_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6281_, lean_object* v_xs_6282_, lean_object* v_remaining_x27_6283_, lean_object* v_ys4_6284_, lean_object* v_onAlt_6285_, lean_object* v_a_6286_, lean_object* v_altType_6287_, uint8_t v___x_6288_, uint8_t v___x_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_){
_start:
{
lean_object* v___x_6295_; 
v___x_6295_ = l_Lean_Meta_instantiateLambda(v___x_6281_, v_xs_6282_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
if (lean_obj_tag(v___x_6295_) == 0)
{
lean_object* v_a_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; 
v_a_6296_ = lean_ctor_get(v___x_6295_, 0);
lean_inc(v_a_6296_);
lean_dec_ref_known(v___x_6295_, 1);
lean_inc_ref(v_ys4_6284_);
lean_inc_ref(v_remaining_x27_6283_);
lean_inc_ref_n(v_xs_6282_, 2);
v___x_6297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6297_, 0, v_xs_6282_);
lean_ctor_set(v___x_6297_, 1, v_xs_6282_);
lean_ctor_set(v___x_6297_, 2, v_remaining_x27_6283_);
lean_ctor_set(v___x_6297_, 3, v_remaining_x27_6283_);
lean_ctor_set(v___x_6297_, 4, v_ys4_6284_);
lean_inc(v___y_6293_);
lean_inc_ref(v___y_6292_);
lean_inc(v___y_6291_);
lean_inc_ref(v___y_6290_);
v___x_6298_ = lean_apply_9(v_onAlt_6285_, v_a_6286_, v_altType_6287_, v___x_6297_, v_a_6296_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_, lean_box(0));
if (lean_obj_tag(v___x_6298_) == 0)
{
lean_object* v_a_6299_; lean_object* v___x_6300_; uint8_t v___x_6301_; lean_object* v___x_6302_; 
v_a_6299_ = lean_ctor_get(v___x_6298_, 0);
lean_inc(v_a_6299_);
lean_dec_ref_known(v___x_6298_, 1);
v___x_6300_ = l_Array_append___redArg(v_xs_6282_, v_ys4_6284_);
lean_dec_ref(v_ys4_6284_);
v___x_6301_ = 1;
v___x_6302_ = l_Lean_Meta_mkLambdaFVars(v___x_6300_, v_a_6299_, v___x_6288_, v___x_6289_, v___x_6288_, v___x_6289_, v___x_6301_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
lean_dec(v___y_6293_);
lean_dec_ref(v___y_6292_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
lean_dec_ref(v___x_6300_);
return v___x_6302_;
}
else
{
lean_dec(v___y_6293_);
lean_dec_ref(v___y_6292_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
lean_dec_ref(v_ys4_6284_);
lean_dec_ref(v_xs_6282_);
return v___x_6298_;
}
}
else
{
lean_dec(v___y_6293_);
lean_dec_ref(v___y_6292_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
lean_dec_ref(v_altType_6287_);
lean_dec(v_a_6286_);
lean_dec_ref(v_onAlt_6285_);
lean_dec_ref(v_ys4_6284_);
lean_dec_ref(v_remaining_x27_6283_);
lean_dec_ref(v_xs_6282_);
return v___x_6295_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_6281_ = stack[0].m_obj;
lean_object* v_xs_6282_ = stack[1].m_obj;
lean_object* v_remaining_x27_6283_ = stack[2].m_obj;
lean_object* v_ys4_6284_ = stack[3].m_obj;
lean_object* v_onAlt_6285_ = stack[4].m_obj;
lean_object* v_a_6286_ = stack[5].m_obj;
lean_object* v_altType_6287_ = stack[6].m_obj;
uint8_t v___x_6288_ = stack[7].m_num;
uint8_t v___x_6289_ = stack[8].m_num;
lean_object* v___y_6290_ = stack[9].m_obj;
lean_object* v___y_6291_ = stack[10].m_obj;
lean_object* v___y_6292_ = stack[11].m_obj;
lean_object* v___y_6293_ = stack[12].m_obj;
lean_object* v_res_6303_;
v_res_6303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6281_, v_xs_6282_, v_remaining_x27_6283_, v_ys4_6284_, v_onAlt_6285_, v_a_6286_, v_altType_6287_, v___x_6288_, v___x_6289_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
stack->m_obj
 = v_res_6303_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6304_, lean_object* v_xs_6305_, lean_object* v_remaining_x27_6306_, lean_object* v_ys4_6307_, lean_object* v_onAlt_6308_, lean_object* v_a_6309_, lean_object* v_altType_6310_, lean_object* v___x_6311_, lean_object* v___x_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_){
_start:
{
uint8_t v___x_36640__boxed_6318_; uint8_t v___x_36641__boxed_6319_; lean_object* v_res_6320_; 
v___x_36640__boxed_6318_ = lean_unbox(v___x_6311_);
v___x_36641__boxed_6319_ = lean_unbox(v___x_6312_);
v_res_6320_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6304_, v_xs_6305_, v_remaining_x27_6306_, v_ys4_6307_, v_onAlt_6308_, v_a_6309_, v_altType_6310_, v___x_36640__boxed_6318_, v___x_36641__boxed_6319_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_);
return v_res_6320_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6321_, lean_object* v_xs_6322_, lean_object* v_remaining_x27_6323_, lean_object* v_onAlt_6324_, lean_object* v_a_6325_, uint8_t v___x_6326_, uint8_t v___x_6327_, lean_object* v___f_6328_, lean_object* v_ys4_6329_, lean_object* v_altType_6330_, lean_object* v___y_6331_, lean_object* v___y_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_){
_start:
{
lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___f_6338_; lean_object* v___x_6339_; 
v___x_6336_ = lean_box(v___x_6326_);
v___x_6337_ = lean_box(v___x_6327_);
lean_inc_ref(v_xs_6322_);
lean_inc_ref(v___x_6321_);
v___f_6338_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6338_, 0, v___x_6321_);
lean_closure_set(v___f_6338_, 1, v_xs_6322_);
lean_closure_set(v___f_6338_, 2, v_remaining_x27_6323_);
lean_closure_set(v___f_6338_, 3, v_ys4_6329_);
lean_closure_set(v___f_6338_, 4, v_onAlt_6324_);
lean_closure_set(v___f_6338_, 5, v_a_6325_);
lean_closure_set(v___f_6338_, 6, v_altType_6330_);
lean_closure_set(v___f_6338_, 7, v___x_6336_);
lean_closure_set(v___f_6338_, 8, v___x_6337_);
v___x_6339_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6321_, v___f_6328_, v___x_6326_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
if (lean_obj_tag(v___x_6339_) == 0)
{
lean_object* v_a_6340_; lean_object* v___x_6341_; 
v_a_6340_ = lean_ctor_get(v___x_6339_, 0);
lean_inc(v_a_6340_);
lean_dec_ref_known(v___x_6339_, 1);
v___x_6341_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6322_, v_a_6340_, v___f_6338_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
lean_dec(v_a_6340_);
lean_dec_ref(v_xs_6322_);
return v___x_6341_;
}
else
{
lean_object* v_a_6342_; lean_object* v___x_6344_; uint8_t v_isShared_6345_; uint8_t v_isSharedCheck_6349_; 
lean_dec_ref(v___f_6338_);
lean_dec_ref(v_xs_6322_);
v_a_6342_ = lean_ctor_get(v___x_6339_, 0);
v_isSharedCheck_6349_ = !lean_is_exclusive(v___x_6339_);
if (v_isSharedCheck_6349_ == 0)
{
v___x_6344_ = v___x_6339_;
v_isShared_6345_ = v_isSharedCheck_6349_;
goto v_resetjp_6343_;
}
else
{
lean_inc(v_a_6342_);
lean_dec(v___x_6339_);
v___x_6344_ = lean_box(0);
v_isShared_6345_ = v_isSharedCheck_6349_;
goto v_resetjp_6343_;
}
v_resetjp_6343_:
{
lean_object* v___x_6347_; 
if (v_isShared_6345_ == 0)
{
v___x_6347_ = v___x_6344_;
goto v_reusejp_6346_;
}
else
{
lean_object* v_reuseFailAlloc_6348_; 
v_reuseFailAlloc_6348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6348_, 0, v_a_6342_);
v___x_6347_ = v_reuseFailAlloc_6348_;
goto v_reusejp_6346_;
}
v_reusejp_6346_:
{
return v___x_6347_;
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_6321_ = stack[0].m_obj;
lean_object* v_xs_6322_ = stack[1].m_obj;
lean_object* v_remaining_x27_6323_ = stack[2].m_obj;
lean_object* v_onAlt_6324_ = stack[3].m_obj;
lean_object* v_a_6325_ = stack[4].m_obj;
uint8_t v___x_6326_ = stack[5].m_num;
uint8_t v___x_6327_ = stack[6].m_num;
lean_object* v___f_6328_ = stack[7].m_obj;
lean_object* v_ys4_6329_ = stack[8].m_obj;
lean_object* v_altType_6330_ = stack[9].m_obj;
lean_object* v___y_6331_ = stack[10].m_obj;
lean_object* v___y_6332_ = stack[11].m_obj;
lean_object* v___y_6333_ = stack[12].m_obj;
lean_object* v___y_6334_ = stack[13].m_obj;
lean_object* v_res_6350_;
v_res_6350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6321_, v_xs_6322_, v_remaining_x27_6323_, v_onAlt_6324_, v_a_6325_, v___x_6326_, v___x_6327_, v___f_6328_, v_ys4_6329_, v_altType_6330_, v___y_6331_, v___y_6332_, v___y_6333_, v___y_6334_);
stack->m_obj
 = v_res_6350_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6351_, lean_object* v_xs_6352_, lean_object* v_remaining_x27_6353_, lean_object* v_onAlt_6354_, lean_object* v_a_6355_, lean_object* v___x_6356_, lean_object* v___x_6357_, lean_object* v___f_6358_, lean_object* v_ys4_6359_, lean_object* v_altType_6360_, lean_object* v___y_6361_, lean_object* v___y_6362_, lean_object* v___y_6363_, lean_object* v___y_6364_, lean_object* v___y_6365_){
_start:
{
uint8_t v___x_36706__boxed_6366_; uint8_t v___x_36707__boxed_6367_; lean_object* v_res_6368_; 
v___x_36706__boxed_6366_ = lean_unbox(v___x_6356_);
v___x_36707__boxed_6367_ = lean_unbox(v___x_6357_);
v_res_6368_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6351_, v_xs_6352_, v_remaining_x27_6353_, v_onAlt_6354_, v_a_6355_, v___x_36706__boxed_6366_, v___x_36707__boxed_6367_, v___f_6358_, v_ys4_6359_, v_altType_6360_, v___y_6361_, v___y_6362_, v___y_6363_, v___y_6364_);
lean_dec(v___y_6364_);
lean_dec_ref(v___y_6363_);
lean_dec(v___y_6362_);
lean_dec_ref(v___y_6361_);
return v_res_6368_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6369_, lean_object* v_remaining_x27_6370_, lean_object* v_onAlt_6371_, lean_object* v_a_6372_, uint8_t v___x_6373_, uint8_t v___x_6374_, lean_object* v___f_6375_, lean_object* v_extraEqualities_6376_, lean_object* v_xs_6377_, lean_object* v_altType_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_){
_start:
{
lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___f_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; 
v___x_6384_ = lean_box(v___x_6373_);
v___x_6385_ = lean_box(v___x_6374_);
v___f_6386_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6386_, 0, v___x_6369_);
lean_closure_set(v___f_6386_, 1, v_xs_6377_);
lean_closure_set(v___f_6386_, 2, v_remaining_x27_6370_);
lean_closure_set(v___f_6386_, 3, v_onAlt_6371_);
lean_closure_set(v___f_6386_, 4, v_a_6372_);
lean_closure_set(v___f_6386_, 5, v___x_6384_);
lean_closure_set(v___f_6386_, 6, v___x_6385_);
lean_closure_set(v___f_6386_, 7, v___f_6375_);
v___x_6387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6387_, 0, v_extraEqualities_6376_);
v___x_6388_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_6378_, v___x_6387_, v___f_6386_, v___x_6373_, v___x_6373_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
return v___x_6388_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_6369_ = stack[0].m_obj;
lean_object* v_remaining_x27_6370_ = stack[1].m_obj;
lean_object* v_onAlt_6371_ = stack[2].m_obj;
lean_object* v_a_6372_ = stack[3].m_obj;
uint8_t v___x_6373_ = stack[4].m_num;
uint8_t v___x_6374_ = stack[5].m_num;
lean_object* v___f_6375_ = stack[6].m_obj;
lean_object* v_extraEqualities_6376_ = stack[7].m_obj;
lean_object* v_xs_6377_ = stack[8].m_obj;
lean_object* v_altType_6378_ = stack[9].m_obj;
lean_object* v___y_6379_ = stack[10].m_obj;
lean_object* v___y_6380_ = stack[11].m_obj;
lean_object* v___y_6381_ = stack[12].m_obj;
lean_object* v___y_6382_ = stack[13].m_obj;
lean_object* v_res_6389_;
v_res_6389_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6369_, v_remaining_x27_6370_, v_onAlt_6371_, v_a_6372_, v___x_6373_, v___x_6374_, v___f_6375_, v_extraEqualities_6376_, v_xs_6377_, v_altType_6378_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_);
stack->m_obj
 = v_res_6389_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6390_, lean_object* v_remaining_x27_6391_, lean_object* v_onAlt_6392_, lean_object* v_a_6393_, lean_object* v___x_6394_, lean_object* v___x_6395_, lean_object* v___f_6396_, lean_object* v_extraEqualities_6397_, lean_object* v_xs_6398_, lean_object* v_altType_6399_, lean_object* v___y_6400_, lean_object* v___y_6401_, lean_object* v___y_6402_, lean_object* v___y_6403_, lean_object* v___y_6404_){
_start:
{
uint8_t v___x_36793__boxed_6405_; uint8_t v___x_36794__boxed_6406_; lean_object* v_res_6407_; 
v___x_36793__boxed_6405_ = lean_unbox(v___x_6394_);
v___x_36794__boxed_6406_ = lean_unbox(v___x_6395_);
v_res_6407_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6390_, v_remaining_x27_6391_, v_onAlt_6392_, v_a_6393_, v___x_36793__boxed_6405_, v___x_36794__boxed_6406_, v___f_6396_, v_extraEqualities_6397_, v_xs_6398_, v_altType_6399_, v___y_6400_, v___y_6401_, v___y_6402_, v___y_6403_);
lean_dec(v___y_6403_);
lean_dec_ref(v___y_6402_);
lean_dec(v___y_6401_);
lean_dec_ref(v___y_6400_);
return v_res_6407_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6409_, lean_object* v_onAlt_6410_, lean_object* v_extraEqualities_6411_, lean_object* v_a_6412_, lean_object* v_b_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_){
_start:
{
lean_object* v___y_6420_; uint8_t v___x_6443_; 
v___x_6443_ = lean_nat_dec_lt(v_a_6412_, v_upperBound_6409_);
if (v___x_6443_ == 0)
{
lean_object* v___x_6444_; 
lean_dec(v_a_6412_);
lean_dec(v_extraEqualities_6411_);
lean_dec_ref(v_onAlt_6410_);
v___x_6444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6444_, 0, v_b_6413_);
return v___x_6444_;
}
else
{
lean_object* v_snd_6445_; lean_object* v_snd_6446_; lean_object* v_snd_6447_; lean_object* v_fst_6448_; lean_object* v___x_6450_; uint8_t v_isShared_6451_; uint8_t v_isSharedCheck_6555_; 
v_snd_6445_ = lean_ctor_get(v_b_6413_, 1);
lean_inc(v_snd_6445_);
v_snd_6446_ = lean_ctor_get(v_snd_6445_, 1);
lean_inc(v_snd_6446_);
v_snd_6447_ = lean_ctor_get(v_snd_6446_, 1);
lean_inc(v_snd_6447_);
v_fst_6448_ = lean_ctor_get(v_b_6413_, 0);
v_isSharedCheck_6555_ = !lean_is_exclusive(v_b_6413_);
if (v_isSharedCheck_6555_ == 0)
{
lean_object* v_unused_6556_; 
v_unused_6556_ = lean_ctor_get(v_b_6413_, 1);
lean_dec(v_unused_6556_);
v___x_6450_ = v_b_6413_;
v_isShared_6451_ = v_isSharedCheck_6555_;
goto v_resetjp_6449_;
}
else
{
lean_inc(v_fst_6448_);
lean_dec(v_b_6413_);
v___x_6450_ = lean_box(0);
v_isShared_6451_ = v_isSharedCheck_6555_;
goto v_resetjp_6449_;
}
v_resetjp_6449_:
{
lean_object* v_fst_6452_; lean_object* v___x_6454_; uint8_t v_isShared_6455_; uint8_t v_isSharedCheck_6553_; 
v_fst_6452_ = lean_ctor_get(v_snd_6445_, 0);
v_isSharedCheck_6553_ = !lean_is_exclusive(v_snd_6445_);
if (v_isSharedCheck_6553_ == 0)
{
lean_object* v_unused_6554_; 
v_unused_6554_ = lean_ctor_get(v_snd_6445_, 1);
lean_dec(v_unused_6554_);
v___x_6454_ = v_snd_6445_;
v_isShared_6455_ = v_isSharedCheck_6553_;
goto v_resetjp_6453_;
}
else
{
lean_inc(v_fst_6452_);
lean_dec(v_snd_6445_);
v___x_6454_ = lean_box(0);
v_isShared_6455_ = v_isSharedCheck_6553_;
goto v_resetjp_6453_;
}
v_resetjp_6453_:
{
lean_object* v_fst_6456_; lean_object* v___x_6458_; uint8_t v_isShared_6459_; uint8_t v_isSharedCheck_6551_; 
v_fst_6456_ = lean_ctor_get(v_snd_6446_, 0);
v_isSharedCheck_6551_ = !lean_is_exclusive(v_snd_6446_);
if (v_isSharedCheck_6551_ == 0)
{
lean_object* v_unused_6552_; 
v_unused_6552_ = lean_ctor_get(v_snd_6446_, 1);
lean_dec(v_unused_6552_);
v___x_6458_ = v_snd_6446_;
v_isShared_6459_ = v_isSharedCheck_6551_;
goto v_resetjp_6457_;
}
else
{
lean_inc(v_fst_6456_);
lean_dec(v_snd_6446_);
v___x_6458_ = lean_box(0);
v_isShared_6459_ = v_isSharedCheck_6551_;
goto v_resetjp_6457_;
}
v_resetjp_6457_:
{
lean_object* v_array_6460_; lean_object* v_start_6461_; lean_object* v_stop_6462_; uint8_t v___x_6463_; 
v_array_6460_ = lean_ctor_get(v_snd_6447_, 0);
v_start_6461_ = lean_ctor_get(v_snd_6447_, 1);
v_stop_6462_ = lean_ctor_get(v_snd_6447_, 2);
v___x_6463_ = lean_nat_dec_lt(v_start_6461_, v_stop_6462_);
if (v___x_6463_ == 0)
{
lean_object* v___x_6465_; 
if (v_isShared_6459_ == 0)
{
v___x_6465_ = v___x_6458_;
goto v_reusejp_6464_;
}
else
{
lean_object* v_reuseFailAlloc_6474_; 
v_reuseFailAlloc_6474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6474_, 0, v_fst_6456_);
lean_ctor_set(v_reuseFailAlloc_6474_, 1, v_snd_6447_);
v___x_6465_ = v_reuseFailAlloc_6474_;
goto v_reusejp_6464_;
}
v_reusejp_6464_:
{
lean_object* v___x_6467_; 
if (v_isShared_6455_ == 0)
{
lean_ctor_set(v___x_6454_, 1, v___x_6465_);
v___x_6467_ = v___x_6454_;
goto v_reusejp_6466_;
}
else
{
lean_object* v_reuseFailAlloc_6473_; 
v_reuseFailAlloc_6473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_fst_6452_);
lean_ctor_set(v_reuseFailAlloc_6473_, 1, v___x_6465_);
v___x_6467_ = v_reuseFailAlloc_6473_;
goto v_reusejp_6466_;
}
v_reusejp_6466_:
{
lean_object* v___x_6469_; 
if (v_isShared_6451_ == 0)
{
lean_ctor_set(v___x_6450_, 1, v___x_6467_);
v___x_6469_ = v___x_6450_;
goto v_reusejp_6468_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_fst_6448_);
lean_ctor_set(v_reuseFailAlloc_6472_, 1, v___x_6467_);
v___x_6469_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6468_;
}
v_reusejp_6468_:
{
lean_object* v___x_6470_; lean_object* v___f_6471_; 
v___x_6470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6470_, 0, v___x_6469_);
v___f_6471_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6471_, 0, v___x_6470_);
v___y_6420_ = v___f_6471_;
goto v___jp_6419_;
}
}
}
}
else
{
lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6547_; 
lean_inc(v_stop_6462_);
lean_inc(v_start_6461_);
lean_inc_ref(v_array_6460_);
v_isSharedCheck_6547_ = !lean_is_exclusive(v_snd_6447_);
if (v_isSharedCheck_6547_ == 0)
{
lean_object* v_unused_6548_; lean_object* v_unused_6549_; lean_object* v_unused_6550_; 
v_unused_6548_ = lean_ctor_get(v_snd_6447_, 2);
lean_dec(v_unused_6548_);
v_unused_6549_ = lean_ctor_get(v_snd_6447_, 1);
lean_dec(v_unused_6549_);
v_unused_6550_ = lean_ctor_get(v_snd_6447_, 0);
lean_dec(v_unused_6550_);
v___x_6476_ = v_snd_6447_;
v_isShared_6477_ = v_isSharedCheck_6547_;
goto v_resetjp_6475_;
}
else
{
lean_dec(v_snd_6447_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6547_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v_array_6478_; lean_object* v_start_6479_; lean_object* v_stop_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6485_; 
v_array_6478_ = lean_ctor_get(v_fst_6456_, 0);
v_start_6479_ = lean_ctor_get(v_fst_6456_, 1);
v_stop_6480_ = lean_ctor_get(v_fst_6456_, 2);
v___x_6481_ = lean_array_fget(v_array_6460_, v_start_6461_);
v___x_6482_ = lean_unsigned_to_nat(1u);
v___x_6483_ = lean_nat_add(v_start_6461_, v___x_6482_);
lean_dec(v_start_6461_);
if (v_isShared_6477_ == 0)
{
lean_ctor_set(v___x_6476_, 1, v___x_6483_);
v___x_6485_ = v___x_6476_;
goto v_reusejp_6484_;
}
else
{
lean_object* v_reuseFailAlloc_6546_; 
v_reuseFailAlloc_6546_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6546_, 0, v_array_6460_);
lean_ctor_set(v_reuseFailAlloc_6546_, 1, v___x_6483_);
lean_ctor_set(v_reuseFailAlloc_6546_, 2, v_stop_6462_);
v___x_6485_ = v_reuseFailAlloc_6546_;
goto v_reusejp_6484_;
}
v_reusejp_6484_:
{
uint8_t v___x_6486_; 
v___x_6486_ = lean_nat_dec_lt(v_start_6479_, v_stop_6480_);
if (v___x_6486_ == 0)
{
lean_object* v___x_6488_; 
lean_dec(v___x_6481_);
if (v_isShared_6459_ == 0)
{
lean_ctor_set(v___x_6458_, 1, v___x_6485_);
v___x_6488_ = v___x_6458_;
goto v_reusejp_6487_;
}
else
{
lean_object* v_reuseFailAlloc_6497_; 
v_reuseFailAlloc_6497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6497_, 0, v_fst_6456_);
lean_ctor_set(v_reuseFailAlloc_6497_, 1, v___x_6485_);
v___x_6488_ = v_reuseFailAlloc_6497_;
goto v_reusejp_6487_;
}
v_reusejp_6487_:
{
lean_object* v___x_6490_; 
if (v_isShared_6455_ == 0)
{
lean_ctor_set(v___x_6454_, 1, v___x_6488_);
v___x_6490_ = v___x_6454_;
goto v_reusejp_6489_;
}
else
{
lean_object* v_reuseFailAlloc_6496_; 
v_reuseFailAlloc_6496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6496_, 0, v_fst_6452_);
lean_ctor_set(v_reuseFailAlloc_6496_, 1, v___x_6488_);
v___x_6490_ = v_reuseFailAlloc_6496_;
goto v_reusejp_6489_;
}
v_reusejp_6489_:
{
lean_object* v___x_6492_; 
if (v_isShared_6451_ == 0)
{
lean_ctor_set(v___x_6450_, 1, v___x_6490_);
v___x_6492_ = v___x_6450_;
goto v_reusejp_6491_;
}
else
{
lean_object* v_reuseFailAlloc_6495_; 
v_reuseFailAlloc_6495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_fst_6448_);
lean_ctor_set(v_reuseFailAlloc_6495_, 1, v___x_6490_);
v___x_6492_ = v_reuseFailAlloc_6495_;
goto v_reusejp_6491_;
}
v_reusejp_6491_:
{
lean_object* v___x_6493_; lean_object* v___f_6494_; 
v___x_6493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6493_, 0, v___x_6492_);
v___f_6494_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6494_, 0, v___x_6493_);
v___y_6420_ = v___f_6494_;
goto v___jp_6419_;
}
}
}
}
else
{
lean_object* v___x_6499_; uint8_t v_isShared_6500_; uint8_t v_isSharedCheck_6542_; 
lean_inc(v_stop_6480_);
lean_inc(v_start_6479_);
lean_inc_ref(v_array_6478_);
v_isSharedCheck_6542_ = !lean_is_exclusive(v_fst_6456_);
if (v_isSharedCheck_6542_ == 0)
{
lean_object* v_unused_6543_; lean_object* v_unused_6544_; lean_object* v_unused_6545_; 
v_unused_6543_ = lean_ctor_get(v_fst_6456_, 2);
lean_dec(v_unused_6543_);
v_unused_6544_ = lean_ctor_get(v_fst_6456_, 1);
lean_dec(v_unused_6544_);
v_unused_6545_ = lean_ctor_get(v_fst_6456_, 0);
lean_dec(v_unused_6545_);
v___x_6499_ = v_fst_6456_;
v_isShared_6500_ = v_isSharedCheck_6542_;
goto v_resetjp_6498_;
}
else
{
lean_dec(v_fst_6456_);
v___x_6499_ = lean_box(0);
v_isShared_6500_ = v_isSharedCheck_6542_;
goto v_resetjp_6498_;
}
v_resetjp_6498_:
{
lean_object* v_array_6501_; lean_object* v_start_6502_; lean_object* v_stop_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6507_; 
v_array_6501_ = lean_ctor_get(v_fst_6452_, 0);
v_start_6502_ = lean_ctor_get(v_fst_6452_, 1);
v_stop_6503_ = lean_ctor_get(v_fst_6452_, 2);
v___x_6504_ = lean_array_fget(v_array_6478_, v_start_6479_);
v___x_6505_ = lean_nat_add(v_start_6479_, v___x_6482_);
lean_dec(v_start_6479_);
if (v_isShared_6500_ == 0)
{
lean_ctor_set(v___x_6499_, 1, v___x_6505_);
v___x_6507_ = v___x_6499_;
goto v_reusejp_6506_;
}
else
{
lean_object* v_reuseFailAlloc_6541_; 
v_reuseFailAlloc_6541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6541_, 0, v_array_6478_);
lean_ctor_set(v_reuseFailAlloc_6541_, 1, v___x_6505_);
lean_ctor_set(v_reuseFailAlloc_6541_, 2, v_stop_6480_);
v___x_6507_ = v_reuseFailAlloc_6541_;
goto v_reusejp_6506_;
}
v_reusejp_6506_:
{
uint8_t v___x_6508_; 
v___x_6508_ = lean_nat_dec_lt(v_start_6502_, v_stop_6503_);
if (v___x_6508_ == 0)
{
lean_object* v___x_6510_; 
lean_dec(v___x_6504_);
lean_dec(v___x_6481_);
if (v_isShared_6459_ == 0)
{
lean_ctor_set(v___x_6458_, 1, v___x_6485_);
lean_ctor_set(v___x_6458_, 0, v___x_6507_);
v___x_6510_ = v___x_6458_;
goto v_reusejp_6509_;
}
else
{
lean_object* v_reuseFailAlloc_6519_; 
v_reuseFailAlloc_6519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6519_, 0, v___x_6507_);
lean_ctor_set(v_reuseFailAlloc_6519_, 1, v___x_6485_);
v___x_6510_ = v_reuseFailAlloc_6519_;
goto v_reusejp_6509_;
}
v_reusejp_6509_:
{
lean_object* v___x_6512_; 
if (v_isShared_6455_ == 0)
{
lean_ctor_set(v___x_6454_, 1, v___x_6510_);
v___x_6512_ = v___x_6454_;
goto v_reusejp_6511_;
}
else
{
lean_object* v_reuseFailAlloc_6518_; 
v_reuseFailAlloc_6518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6518_, 0, v_fst_6452_);
lean_ctor_set(v_reuseFailAlloc_6518_, 1, v___x_6510_);
v___x_6512_ = v_reuseFailAlloc_6518_;
goto v_reusejp_6511_;
}
v_reusejp_6511_:
{
lean_object* v___x_6514_; 
if (v_isShared_6451_ == 0)
{
lean_ctor_set(v___x_6450_, 1, v___x_6512_);
v___x_6514_ = v___x_6450_;
goto v_reusejp_6513_;
}
else
{
lean_object* v_reuseFailAlloc_6517_; 
v_reuseFailAlloc_6517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6517_, 0, v_fst_6448_);
lean_ctor_set(v_reuseFailAlloc_6517_, 1, v___x_6512_);
v___x_6514_ = v_reuseFailAlloc_6517_;
goto v_reusejp_6513_;
}
v_reusejp_6513_:
{
lean_object* v___x_6515_; lean_object* v___f_6516_; 
v___x_6515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6515_, 0, v___x_6514_);
v___f_6516_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6516_, 0, v___x_6515_);
v___y_6420_ = v___f_6516_;
goto v___jp_6419_;
}
}
}
}
else
{
lean_object* v___x_6521_; uint8_t v_isShared_6522_; uint8_t v_isSharedCheck_6537_; 
lean_inc(v_stop_6503_);
lean_inc(v_start_6502_);
lean_inc_ref(v_array_6501_);
lean_del_object(v___x_6458_);
lean_del_object(v___x_6454_);
lean_del_object(v___x_6450_);
v_isSharedCheck_6537_ = !lean_is_exclusive(v_fst_6452_);
if (v_isSharedCheck_6537_ == 0)
{
lean_object* v_unused_6538_; lean_object* v_unused_6539_; lean_object* v_unused_6540_; 
v_unused_6538_ = lean_ctor_get(v_fst_6452_, 2);
lean_dec(v_unused_6538_);
v_unused_6539_ = lean_ctor_get(v_fst_6452_, 1);
lean_dec(v_unused_6539_);
v_unused_6540_ = lean_ctor_get(v_fst_6452_, 0);
lean_dec(v_unused_6540_);
v___x_6521_ = v_fst_6452_;
v_isShared_6522_ = v_isSharedCheck_6537_;
goto v_resetjp_6520_;
}
else
{
lean_dec(v_fst_6452_);
v___x_6521_ = lean_box(0);
v_isShared_6522_ = v_isSharedCheck_6537_;
goto v_resetjp_6520_;
}
v_resetjp_6520_:
{
lean_object* v___f_6523_; uint8_t v___x_6524_; lean_object* v_remaining_x27_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___f_6529_; lean_object* v___x_6530_; lean_object* v___x_6532_; 
v___f_6523_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6524_ = 0;
v_remaining_x27_6525_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6526_ = lean_array_fget_borrowed(v_array_6501_, v_start_6502_);
v___x_6527_ = lean_box(v___x_6524_);
v___x_6528_ = lean_box(v___x_6508_);
lean_inc(v_extraEqualities_6411_);
lean_inc(v_a_6412_);
lean_inc_ref(v_onAlt_6410_);
lean_inc(v___x_6526_);
v___f_6529_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6529_, 0, v___x_6526_);
lean_closure_set(v___f_6529_, 1, v_remaining_x27_6525_);
lean_closure_set(v___f_6529_, 2, v_onAlt_6410_);
lean_closure_set(v___f_6529_, 3, v_a_6412_);
lean_closure_set(v___f_6529_, 4, v___x_6527_);
lean_closure_set(v___f_6529_, 5, v___x_6528_);
lean_closure_set(v___f_6529_, 6, v___f_6523_);
lean_closure_set(v___f_6529_, 7, v_extraEqualities_6411_);
v___x_6530_ = lean_nat_add(v_start_6502_, v___x_6482_);
lean_dec(v_start_6502_);
if (v_isShared_6522_ == 0)
{
lean_ctor_set(v___x_6521_, 1, v___x_6530_);
v___x_6532_ = v___x_6521_;
goto v_reusejp_6531_;
}
else
{
lean_object* v_reuseFailAlloc_6536_; 
v_reuseFailAlloc_6536_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6536_, 0, v_array_6501_);
lean_ctor_set(v_reuseFailAlloc_6536_, 1, v___x_6530_);
lean_ctor_set(v_reuseFailAlloc_6536_, 2, v_stop_6503_);
v___x_6532_ = v_reuseFailAlloc_6536_;
goto v_reusejp_6531_;
}
v_reusejp_6531_:
{
lean_object* v___x_6533_; lean_object* v___x_6534_; lean_object* v___f_6535_; 
v___x_6533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6533_, 0, v___x_6504_);
v___x_6534_ = lean_box(v___x_6524_);
v___f_6535_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6535_, 0, v___x_6481_);
lean_closure_set(v___f_6535_, 1, v___x_6533_);
lean_closure_set(v___f_6535_, 2, v___f_6529_);
lean_closure_set(v___f_6535_, 3, v___x_6534_);
lean_closure_set(v___f_6535_, 4, v_fst_6448_);
lean_closure_set(v___f_6535_, 5, v___x_6507_);
lean_closure_set(v___f_6535_, 6, v___x_6485_);
lean_closure_set(v___f_6535_, 7, v___x_6532_);
v___y_6420_ = v___f_6535_;
goto v___jp_6419_;
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
v___jp_6419_:
{
lean_object* v___x_6421_; 
lean_inc(v___y_6417_);
lean_inc_ref(v___y_6416_);
lean_inc(v___y_6415_);
lean_inc_ref(v___y_6414_);
v___x_6421_ = lean_apply_5(v___y_6420_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, lean_box(0));
if (lean_obj_tag(v___x_6421_) == 0)
{
lean_object* v_a_6422_; lean_object* v___x_6424_; uint8_t v_isShared_6425_; uint8_t v_isSharedCheck_6434_; 
v_a_6422_ = lean_ctor_get(v___x_6421_, 0);
v_isSharedCheck_6434_ = !lean_is_exclusive(v___x_6421_);
if (v_isSharedCheck_6434_ == 0)
{
v___x_6424_ = v___x_6421_;
v_isShared_6425_ = v_isSharedCheck_6434_;
goto v_resetjp_6423_;
}
else
{
lean_inc(v_a_6422_);
lean_dec(v___x_6421_);
v___x_6424_ = lean_box(0);
v_isShared_6425_ = v_isSharedCheck_6434_;
goto v_resetjp_6423_;
}
v_resetjp_6423_:
{
if (lean_obj_tag(v_a_6422_) == 0)
{
lean_object* v_a_6426_; lean_object* v___x_6428_; 
lean_dec(v_a_6412_);
lean_dec(v_extraEqualities_6411_);
lean_dec_ref(v_onAlt_6410_);
v_a_6426_ = lean_ctor_get(v_a_6422_, 0);
lean_inc(v_a_6426_);
lean_dec_ref_known(v_a_6422_, 1);
if (v_isShared_6425_ == 0)
{
lean_ctor_set(v___x_6424_, 0, v_a_6426_);
v___x_6428_ = v___x_6424_;
goto v_reusejp_6427_;
}
else
{
lean_object* v_reuseFailAlloc_6429_; 
v_reuseFailAlloc_6429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6429_, 0, v_a_6426_);
v___x_6428_ = v_reuseFailAlloc_6429_;
goto v_reusejp_6427_;
}
v_reusejp_6427_:
{
return v___x_6428_;
}
}
else
{
lean_object* v_a_6430_; lean_object* v___x_6431_; lean_object* v___x_6432_; 
lean_del_object(v___x_6424_);
v_a_6430_ = lean_ctor_get(v_a_6422_, 0);
lean_inc(v_a_6430_);
lean_dec_ref_known(v_a_6422_, 1);
v___x_6431_ = lean_unsigned_to_nat(1u);
v___x_6432_ = lean_nat_add(v_a_6412_, v___x_6431_);
lean_dec(v_a_6412_);
v_a_6412_ = v___x_6432_;
v_b_6413_ = v_a_6430_;
goto _start;
}
}
}
else
{
lean_object* v_a_6435_; lean_object* v___x_6437_; uint8_t v_isShared_6438_; uint8_t v_isSharedCheck_6442_; 
lean_dec(v_a_6412_);
lean_dec(v_extraEqualities_6411_);
lean_dec_ref(v_onAlt_6410_);
v_a_6435_ = lean_ctor_get(v___x_6421_, 0);
v_isSharedCheck_6442_ = !lean_is_exclusive(v___x_6421_);
if (v_isSharedCheck_6442_ == 0)
{
v___x_6437_ = v___x_6421_;
v_isShared_6438_ = v_isSharedCheck_6442_;
goto v_resetjp_6436_;
}
else
{
lean_inc(v_a_6435_);
lean_dec(v___x_6421_);
v___x_6437_ = lean_box(0);
v_isShared_6438_ = v_isSharedCheck_6442_;
goto v_resetjp_6436_;
}
v_resetjp_6436_:
{
lean_object* v___x_6440_; 
if (v_isShared_6438_ == 0)
{
v___x_6440_ = v___x_6437_;
goto v_reusejp_6439_;
}
else
{
lean_object* v_reuseFailAlloc_6441_; 
v_reuseFailAlloc_6441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6441_, 0, v_a_6435_);
v___x_6440_ = v_reuseFailAlloc_6441_;
goto v_reusejp_6439_;
}
v_reusejp_6439_:
{
return v___x_6440_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_6409_ = stack[0].m_obj;
lean_object* v_onAlt_6410_ = stack[1].m_obj;
lean_object* v_extraEqualities_6411_ = stack[2].m_obj;
lean_object* v_a_6412_ = stack[3].m_obj;
lean_object* v_b_6413_ = stack[4].m_obj;
lean_object* v___y_6414_ = stack[5].m_obj;
lean_object* v___y_6415_ = stack[6].m_obj;
lean_object* v___y_6416_ = stack[7].m_obj;
lean_object* v___y_6417_ = stack[8].m_obj;
lean_object* v_res_6557_;
v_res_6557_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6409_, v_onAlt_6410_, v_extraEqualities_6411_, v_a_6412_, v_b_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_);
stack->m_obj
 = v_res_6557_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6558_, lean_object* v_onAlt_6559_, lean_object* v_extraEqualities_6560_, lean_object* v_a_6561_, lean_object* v_b_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_, lean_object* v___y_6565_, lean_object* v___y_6566_, lean_object* v___y_6567_){
_start:
{
lean_object* v_res_6568_; 
v_res_6568_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6558_, v_onAlt_6559_, v_extraEqualities_6560_, v_a_6561_, v_b_6562_, v___y_6563_, v___y_6564_, v___y_6565_, v___y_6566_);
lean_dec(v___y_6566_);
lean_dec_ref(v___y_6565_);
lean_dec(v___y_6564_);
lean_dec_ref(v___y_6563_);
lean_dec(v_upperBound_6558_);
return v_res_6568_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6569_, size_t v_sz_6570_, size_t v_i_6571_, lean_object* v_bs_6572_, lean_object* v___y_6573_, lean_object* v___y_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_){
_start:
{
uint8_t v___x_6578_; 
v___x_6578_ = lean_usize_dec_lt(v_i_6571_, v_sz_6570_);
if (v___x_6578_ == 0)
{
lean_object* v___x_6579_; 
lean_dec_ref(v_onParams_6569_);
v___x_6579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6579_, 0, v_bs_6572_);
return v___x_6579_;
}
else
{
lean_object* v_v_6580_; lean_object* v___x_6581_; lean_object* v_bs_x27_6582_; lean_object* v___x_6583_; 
v_v_6580_ = lean_array_uget(v_bs_6572_, v_i_6571_);
v___x_6581_ = lean_unsigned_to_nat(0u);
v_bs_x27_6582_ = lean_array_uset(v_bs_6572_, v_i_6571_, v___x_6581_);
lean_inc_ref(v_onParams_6569_);
lean_inc(v___y_6576_);
lean_inc_ref(v___y_6575_);
lean_inc(v___y_6574_);
lean_inc_ref(v___y_6573_);
v___x_6583_ = lean_apply_6(v_onParams_6569_, v_v_6580_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_, lean_box(0));
if (lean_obj_tag(v___x_6583_) == 0)
{
lean_object* v_a_6584_; size_t v___x_6585_; size_t v___x_6586_; lean_object* v___x_6587_; 
v_a_6584_ = lean_ctor_get(v___x_6583_, 0);
lean_inc(v_a_6584_);
lean_dec_ref_known(v___x_6583_, 1);
v___x_6585_ = ((size_t)1ULL);
v___x_6586_ = lean_usize_add(v_i_6571_, v___x_6585_);
v___x_6587_ = lean_array_uset(v_bs_x27_6582_, v_i_6571_, v_a_6584_);
v_i_6571_ = v___x_6586_;
v_bs_6572_ = v___x_6587_;
goto _start;
}
else
{
lean_object* v_a_6589_; lean_object* v___x_6591_; uint8_t v_isShared_6592_; uint8_t v_isSharedCheck_6596_; 
lean_dec_ref(v_bs_x27_6582_);
lean_dec_ref(v_onParams_6569_);
v_a_6589_ = lean_ctor_get(v___x_6583_, 0);
v_isSharedCheck_6596_ = !lean_is_exclusive(v___x_6583_);
if (v_isSharedCheck_6596_ == 0)
{
v___x_6591_ = v___x_6583_;
v_isShared_6592_ = v_isSharedCheck_6596_;
goto v_resetjp_6590_;
}
else
{
lean_inc(v_a_6589_);
lean_dec(v___x_6583_);
v___x_6591_ = lean_box(0);
v_isShared_6592_ = v_isSharedCheck_6596_;
goto v_resetjp_6590_;
}
v_resetjp_6590_:
{
lean_object* v___x_6594_; 
if (v_isShared_6592_ == 0)
{
v___x_6594_ = v___x_6591_;
goto v_reusejp_6593_;
}
else
{
lean_object* v_reuseFailAlloc_6595_; 
v_reuseFailAlloc_6595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6595_, 0, v_a_6589_);
v___x_6594_ = v_reuseFailAlloc_6595_;
goto v_reusejp_6593_;
}
v_reusejp_6593_:
{
return v___x_6594_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_onParams_6569_ = stack[0].m_obj;
size_t v_sz_6570_ = stack[1].m_num;
size_t v_i_6571_ = stack[2].m_num;
lean_object* v_bs_6572_ = stack[3].m_obj;
lean_object* v___y_6573_ = stack[4].m_obj;
lean_object* v___y_6574_ = stack[5].m_obj;
lean_object* v___y_6575_ = stack[6].m_obj;
lean_object* v___y_6576_ = stack[7].m_obj;
lean_object* v_res_6597_;
v_res_6597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6569_, v_sz_6570_, v_i_6571_, v_bs_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_);
stack->m_obj
 = v_res_6597_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6598_, lean_object* v_sz_6599_, lean_object* v_i_6600_, lean_object* v_bs_6601_, lean_object* v___y_6602_, lean_object* v___y_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_, lean_object* v___y_6606_){
_start:
{
size_t v_sz_boxed_6607_; size_t v_i_boxed_6608_; lean_object* v_res_6609_; 
v_sz_boxed_6607_ = lean_unbox_usize(v_sz_6599_);
lean_dec(v_sz_6599_);
v_i_boxed_6608_ = lean_unbox_usize(v_i_6600_);
lean_dec(v_i_6600_);
v_res_6609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6598_, v_sz_boxed_6607_, v_i_boxed_6608_, v_bs_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_);
lean_dec(v___y_6605_);
lean_dec_ref(v___y_6604_);
lean_dec(v___y_6603_);
lean_dec_ref(v___y_6602_);
return v_res_6609_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6610_, lean_object* v___y_6611_){
_start:
{
lean_object* v___x_6613_; lean_object* v_env_6614_; lean_object* v___x_6615_; lean_object* v___x_6616_; 
v___x_6613_ = lean_st_ref_get(v___y_6611_);
v_env_6614_ = lean_ctor_get(v___x_6613_, 0);
lean_inc_ref(v_env_6614_);
lean_dec(v___x_6613_);
v___x_6615_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6614_, v_declName_6610_);
v___x_6616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6616_, 0, v___x_6615_);
return v___x_6616_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_6610_ = stack[0].m_obj;
lean_object* v___y_6611_ = stack[1].m_obj;
lean_object* v_res_6617_;
v_res_6617_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6610_, v___y_6611_);
stack->m_obj
 = v_res_6617_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6618_, lean_object* v___y_6619_, lean_object* v___y_6620_){
_start:
{
lean_object* v_res_6621_; 
v_res_6621_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6618_, v___y_6619_);
lean_dec(v___y_6619_);
return v_res_6621_;
}
}
lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6624_, uint8_t v_useSplitter_6625_, uint8_t v_addEqualities_6626_, lean_object* v_onParams_6627_, lean_object* v_onMotive_6628_, lean_object* v_onAlt_6629_, lean_object* v_onRemaining_6630_, lean_object* v___y_6631_, lean_object* v___y_6632_, lean_object* v___y_6633_, lean_object* v___y_6634_){
_start:
{
lean_object* v___x_6636_; lean_object* v_env_6637_; lean_object* v_toMatcherInfo_6638_; lean_object* v_matcherName_6639_; lean_object* v_matcherLevels_6640_; lean_object* v_params_6641_; lean_object* v_motive_6642_; lean_object* v_discrs_6643_; lean_object* v_alts_6644_; lean_object* v_remaining_6645_; lean_object* v___y_6647_; lean_object* v___y_6648_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___y_6654_; lean_object* v___y_6655_; lean_object* v___y_6656_; lean_object* v___y_6657_; lean_object* v___y_6658_; lean_object* v___y_6659_; uint8_t v_isCasesOn_6744_; lean_object* v___y_6746_; size_t v___y_6747_; lean_object* v___y_6748_; lean_object* v___y_6749_; lean_object* v___y_6750_; lean_object* v___y_6751_; lean_object* v___y_6752_; lean_object* v_matcherLevels_6753_; lean_object* v___y_6754_; lean_object* v___y_6755_; lean_object* v___y_6756_; lean_object* v___y_6757_; lean_object* v_numDiscrEqs_6951_; lean_object* v___y_6952_; lean_object* v___y_6953_; lean_object* v___y_6954_; lean_object* v___y_6955_; 
v___x_6636_ = lean_st_ref_get(v___y_6634_);
v_env_6637_ = lean_ctor_get(v___x_6636_, 0);
lean_inc_ref(v_env_6637_);
lean_dec(v___x_6636_);
v_toMatcherInfo_6638_ = lean_ctor_get(v_matcherApp_6624_, 0);
lean_inc_ref(v_toMatcherInfo_6638_);
v_matcherName_6639_ = lean_ctor_get(v_matcherApp_6624_, 1);
lean_inc_n(v_matcherName_6639_, 2);
v_matcherLevels_6640_ = lean_ctor_get(v_matcherApp_6624_, 2);
v_params_6641_ = lean_ctor_get(v_matcherApp_6624_, 3);
v_motive_6642_ = lean_ctor_get(v_matcherApp_6624_, 4);
v_discrs_6643_ = lean_ctor_get(v_matcherApp_6624_, 5);
v_alts_6644_ = lean_ctor_get(v_matcherApp_6624_, 6);
lean_inc_ref(v_alts_6644_);
v_remaining_6645_ = lean_ctor_get(v_matcherApp_6624_, 7);
lean_inc_ref(v_remaining_6645_);
v_isCasesOn_6744_ = l_Lean_isCasesOnRecursor(v_env_6637_, v_matcherName_6639_);
if (v_isCasesOn_6744_ == 0)
{
lean_object* v___x_7005_; lean_object* v_a_7006_; 
lean_inc(v_matcherName_6639_);
v___x_7005_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6639_, v___y_6634_);
v_a_7006_ = lean_ctor_get(v___x_7005_, 0);
lean_inc(v_a_7006_);
lean_dec_ref(v___x_7005_);
if (lean_obj_tag(v_a_7006_) == 0)
{
lean_object* v___x_7007_; lean_object* v___x_7008_; lean_object* v___x_7009_; lean_object* v___x_7010_; lean_object* v___x_7011_; lean_object* v___x_7012_; lean_object* v_a_7013_; lean_object* v___x_7015_; uint8_t v_isShared_7016_; uint8_t v_isSharedCheck_7020_; 
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
lean_dec_ref(v_onMotive_6628_);
lean_dec_ref(v_onParams_6627_);
lean_dec_ref(v_matcherApp_6624_);
v___x_7007_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_7008_ = l_Lean_MessageData_ofName(v_matcherName_6639_);
v___x_7009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7009_, 0, v___x_7007_);
lean_ctor_set(v___x_7009_, 1, v___x_7008_);
v___x_7010_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_7011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_7011_, 0, v___x_7009_);
lean_ctor_set(v___x_7011_, 1, v___x_7010_);
v___x_7012_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_7011_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_);
v_a_7013_ = lean_ctor_get(v___x_7012_, 0);
v_isSharedCheck_7020_ = !lean_is_exclusive(v___x_7012_);
if (v_isSharedCheck_7020_ == 0)
{
v___x_7015_ = v___x_7012_;
v_isShared_7016_ = v_isSharedCheck_7020_;
goto v_resetjp_7014_;
}
else
{
lean_inc(v_a_7013_);
lean_dec(v___x_7012_);
v___x_7015_ = lean_box(0);
v_isShared_7016_ = v_isSharedCheck_7020_;
goto v_resetjp_7014_;
}
v_resetjp_7014_:
{
lean_object* v___x_7018_; 
if (v_isShared_7016_ == 0)
{
v___x_7018_ = v___x_7015_;
goto v_reusejp_7017_;
}
else
{
lean_object* v_reuseFailAlloc_7019_; 
v_reuseFailAlloc_7019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7019_, 0, v_a_7013_);
v___x_7018_ = v_reuseFailAlloc_7019_;
goto v_reusejp_7017_;
}
v_reusejp_7017_:
{
return v___x_7018_;
}
}
}
else
{
lean_object* v_val_7021_; lean_object* v___x_7022_; 
v_val_7021_ = lean_ctor_get(v_a_7006_, 0);
lean_inc(v_val_7021_);
lean_dec_ref_known(v_a_7006_, 1);
v___x_7022_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_7021_);
lean_dec(v_val_7021_);
v_numDiscrEqs_6951_ = v___x_7022_;
v___y_6952_ = v___y_6631_;
v___y_6953_ = v___y_6632_;
v___y_6954_ = v___y_6633_;
v___y_6955_ = v___y_6634_;
goto v___jp_6950_;
}
}
else
{
lean_object* v___x_7023_; 
v___x_7023_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6951_ = v___x_7023_;
v___y_6952_ = v___y_6631_;
v___y_6953_ = v___y_6632_;
v___y_6954_ = v___y_6633_;
v___y_6955_ = v___y_6634_;
goto v___jp_6950_;
}
v___jp_6646_:
{
lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v_aux_6662_; lean_object* v_aux_6663_; lean_object* v_aux_6664_; lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___f_6668_; uint8_t v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; 
lean_inc_ref(v___y_6653_);
v___x_6660_ = lean_array_to_list(v___y_6653_);
lean_inc(v_matcherName_6639_);
v___x_6661_ = l_Lean_mkConst(v_matcherName_6639_, v___x_6660_);
v_aux_6662_ = l_Lean_mkAppN(v___x_6661_, v___y_6647_);
lean_inc_ref(v___y_6655_);
v_aux_6663_ = l_Lean_Expr_app___override(v_aux_6662_, v___y_6655_);
v_aux_6664_ = l_Lean_mkAppN(v_aux_6663_, v___y_6657_);
v___x_6665_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6664_, 2);
v___x_6666_ = l_Lean_indentExpr(v_aux_6664_);
v___x_6667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6667_, 0, v___x_6665_);
lean_ctor_set(v___x_6667_, 1, v___x_6666_);
v___f_6668_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6668_, 0, v___x_6667_);
v___x_6669_ = 0;
v___x_6670_ = lean_box(v___x_6669_);
v___x_6671_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6671_, 0, v_aux_6664_);
lean_closure_set(v___x_6671_, 1, v___x_6670_);
v___x_6672_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6671_, v___f_6668_, v___y_6658_, v___y_6649_, v___y_6650_, v___y_6652_);
if (lean_obj_tag(v___x_6672_) == 0)
{
lean_object* v___x_6673_; lean_object* v___x_6674_; 
lean_dec_ref_known(v___x_6672_, 1);
v___x_6673_ = lean_array_get_size(v_alts_6644_);
v___x_6674_ = l_Lean_Meta_inferArgumentTypesN(v___x_6673_, v_aux_6664_, v___y_6658_, v___y_6649_, v___y_6650_, v___y_6652_);
if (lean_obj_tag(v___x_6674_) == 0)
{
lean_object* v_a_6675_; lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; 
v_a_6675_ = lean_ctor_get(v___x_6674_, 0);
lean_inc(v_a_6675_);
lean_dec_ref_known(v___x_6674_, 1);
v___x_6676_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6624_);
v___x_6677_ = lean_array_get_size(v___x_6676_);
v___x_6678_ = lean_array_get_size(v_a_6675_);
lean_inc_n(v___y_6654_, 3);
v___x_6679_ = l_Array_toSubarray___redArg(v_alts_6644_, v___y_6654_, v___x_6673_);
v___x_6680_ = l_Array_toSubarray___redArg(v___x_6676_, v___y_6654_, v___x_6677_);
v___x_6681_ = l_Array_toSubarray___redArg(v_a_6675_, v___y_6654_, v___x_6678_);
v___x_6682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6682_, 0, v___x_6680_);
lean_ctor_set(v___x_6682_, 1, v___x_6681_);
v___x_6683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6683_, 0, v___x_6679_);
lean_ctor_set(v___x_6683_, 1, v___x_6682_);
lean_inc_ref(v___y_6659_);
v___x_6684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6684_, 0, v___y_6659_);
lean_ctor_set(v___x_6684_, 1, v___x_6683_);
v___x_6685_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6673_, v_onAlt_6629_, v___y_6651_, v___y_6654_, v___x_6684_, v___y_6658_, v___y_6649_, v___y_6650_, v___y_6652_);
if (lean_obj_tag(v___x_6685_) == 0)
{
lean_object* v_a_6686_; lean_object* v_fst_6687_; lean_object* v___x_6688_; 
v_a_6686_ = lean_ctor_get(v___x_6685_, 0);
lean_inc(v_a_6686_);
lean_dec_ref_known(v___x_6685_, 1);
v_fst_6687_ = lean_ctor_get(v_a_6686_, 0);
lean_inc(v_fst_6687_);
lean_dec(v_a_6686_);
lean_inc(v___y_6652_);
lean_inc_ref(v___y_6650_);
lean_inc(v___y_6649_);
lean_inc_ref(v___y_6658_);
v___x_6688_ = lean_apply_6(v_onRemaining_6630_, v_remaining_6645_, v___y_6658_, v___y_6649_, v___y_6650_, v___y_6652_, lean_box(0));
if (lean_obj_tag(v___x_6688_) == 0)
{
lean_object* v_a_6689_; lean_object* v___x_6691_; uint8_t v_isShared_6692_; uint8_t v_isSharedCheck_6711_; 
v_a_6689_ = lean_ctor_get(v___x_6688_, 0);
v_isSharedCheck_6711_ = !lean_is_exclusive(v___x_6688_);
if (v_isSharedCheck_6711_ == 0)
{
v___x_6691_ = v___x_6688_;
v_isShared_6692_ = v_isSharedCheck_6711_;
goto v_resetjp_6690_;
}
else
{
lean_inc(v_a_6689_);
lean_dec(v___x_6688_);
v___x_6691_ = lean_box(0);
v_isShared_6692_ = v_isSharedCheck_6711_;
goto v_resetjp_6690_;
}
v_resetjp_6690_:
{
lean_object* v_numParams_6693_; lean_object* v_numDiscrs_6694_; lean_object* v_altInfos_6695_; lean_object* v_uElimPos_x3f_6696_; lean_object* v_overlaps_6697_; lean_object* v___x_6699_; uint8_t v_isShared_6700_; uint8_t v_isSharedCheck_6709_; 
v_numParams_6693_ = lean_ctor_get(v_toMatcherInfo_6638_, 0);
v_numDiscrs_6694_ = lean_ctor_get(v_toMatcherInfo_6638_, 1);
v_altInfos_6695_ = lean_ctor_get(v_toMatcherInfo_6638_, 2);
v_uElimPos_x3f_6696_ = lean_ctor_get(v_toMatcherInfo_6638_, 3);
v_overlaps_6697_ = lean_ctor_get(v_toMatcherInfo_6638_, 5);
v_isSharedCheck_6709_ = !lean_is_exclusive(v_toMatcherInfo_6638_);
if (v_isSharedCheck_6709_ == 0)
{
lean_object* v_unused_6710_; 
v_unused_6710_ = lean_ctor_get(v_toMatcherInfo_6638_, 4);
lean_dec(v_unused_6710_);
v___x_6699_ = v_toMatcherInfo_6638_;
v_isShared_6700_ = v_isSharedCheck_6709_;
goto v_resetjp_6698_;
}
else
{
lean_inc(v_overlaps_6697_);
lean_inc(v_uElimPos_x3f_6696_);
lean_inc(v_altInfos_6695_);
lean_inc(v_numDiscrs_6694_);
lean_inc(v_numParams_6693_);
lean_dec(v_toMatcherInfo_6638_);
v___x_6699_ = lean_box(0);
v_isShared_6700_ = v_isSharedCheck_6709_;
goto v_resetjp_6698_;
}
v_resetjp_6698_:
{
lean_object* v_remaining_x27_6701_; lean_object* v___x_6703_; 
v_remaining_x27_6701_ = l_Array_append___redArg(v___y_6656_, v_a_6689_);
lean_dec(v_a_6689_);
if (v_isShared_6700_ == 0)
{
lean_ctor_set(v___x_6699_, 4, v___y_6648_);
v___x_6703_ = v___x_6699_;
goto v_reusejp_6702_;
}
else
{
lean_object* v_reuseFailAlloc_6708_; 
v_reuseFailAlloc_6708_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6708_, 0, v_numParams_6693_);
lean_ctor_set(v_reuseFailAlloc_6708_, 1, v_numDiscrs_6694_);
lean_ctor_set(v_reuseFailAlloc_6708_, 2, v_altInfos_6695_);
lean_ctor_set(v_reuseFailAlloc_6708_, 3, v_uElimPos_x3f_6696_);
lean_ctor_set(v_reuseFailAlloc_6708_, 4, v___y_6648_);
lean_ctor_set(v_reuseFailAlloc_6708_, 5, v_overlaps_6697_);
v___x_6703_ = v_reuseFailAlloc_6708_;
goto v_reusejp_6702_;
}
v_reusejp_6702_:
{
lean_object* v___x_6704_; lean_object* v___x_6706_; 
v___x_6704_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6704_, 0, v___x_6703_);
lean_ctor_set(v___x_6704_, 1, v_matcherName_6639_);
lean_ctor_set(v___x_6704_, 2, v___y_6653_);
lean_ctor_set(v___x_6704_, 3, v___y_6647_);
lean_ctor_set(v___x_6704_, 4, v___y_6655_);
lean_ctor_set(v___x_6704_, 5, v___y_6657_);
lean_ctor_set(v___x_6704_, 6, v_fst_6687_);
lean_ctor_set(v___x_6704_, 7, v_remaining_x27_6701_);
if (v_isShared_6692_ == 0)
{
lean_ctor_set(v___x_6691_, 0, v___x_6704_);
v___x_6706_ = v___x_6691_;
goto v_reusejp_6705_;
}
else
{
lean_object* v_reuseFailAlloc_6707_; 
v_reuseFailAlloc_6707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6707_, 0, v___x_6704_);
v___x_6706_ = v_reuseFailAlloc_6707_;
goto v_reusejp_6705_;
}
v_reusejp_6705_:
{
return v___x_6706_;
}
}
}
}
}
else
{
lean_object* v_a_6712_; lean_object* v___x_6714_; uint8_t v_isShared_6715_; uint8_t v_isSharedCheck_6719_; 
lean_dec(v_fst_6687_);
lean_dec_ref(v___y_6657_);
lean_dec(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
v_a_6712_ = lean_ctor_get(v___x_6688_, 0);
v_isSharedCheck_6719_ = !lean_is_exclusive(v___x_6688_);
if (v_isSharedCheck_6719_ == 0)
{
v___x_6714_ = v___x_6688_;
v_isShared_6715_ = v_isSharedCheck_6719_;
goto v_resetjp_6713_;
}
else
{
lean_inc(v_a_6712_);
lean_dec(v___x_6688_);
v___x_6714_ = lean_box(0);
v_isShared_6715_ = v_isSharedCheck_6719_;
goto v_resetjp_6713_;
}
v_resetjp_6713_:
{
lean_object* v___x_6717_; 
if (v_isShared_6715_ == 0)
{
v___x_6717_ = v___x_6714_;
goto v_reusejp_6716_;
}
else
{
lean_object* v_reuseFailAlloc_6718_; 
v_reuseFailAlloc_6718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6718_, 0, v_a_6712_);
v___x_6717_ = v_reuseFailAlloc_6718_;
goto v_reusejp_6716_;
}
v_reusejp_6716_:
{
return v___x_6717_;
}
}
}
}
else
{
lean_object* v_a_6720_; lean_object* v___x_6722_; uint8_t v_isShared_6723_; uint8_t v_isSharedCheck_6727_; 
lean_dec_ref(v___y_6657_);
lean_dec(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v_remaining_6645_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
v_a_6720_ = lean_ctor_get(v___x_6685_, 0);
v_isSharedCheck_6727_ = !lean_is_exclusive(v___x_6685_);
if (v_isSharedCheck_6727_ == 0)
{
v___x_6722_ = v___x_6685_;
v_isShared_6723_ = v_isSharedCheck_6727_;
goto v_resetjp_6721_;
}
else
{
lean_inc(v_a_6720_);
lean_dec(v___x_6685_);
v___x_6722_ = lean_box(0);
v_isShared_6723_ = v_isSharedCheck_6727_;
goto v_resetjp_6721_;
}
v_resetjp_6721_:
{
lean_object* v___x_6725_; 
if (v_isShared_6723_ == 0)
{
v___x_6725_ = v___x_6722_;
goto v_reusejp_6724_;
}
else
{
lean_object* v_reuseFailAlloc_6726_; 
v_reuseFailAlloc_6726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6726_, 0, v_a_6720_);
v___x_6725_ = v_reuseFailAlloc_6726_;
goto v_reusejp_6724_;
}
v_reusejp_6724_:
{
return v___x_6725_;
}
}
}
}
else
{
lean_object* v_a_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6735_; 
lean_dec_ref(v___y_6657_);
lean_dec(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec(v___y_6654_);
lean_dec_ref(v___y_6653_);
lean_dec(v___y_6651_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
lean_dec_ref(v_matcherApp_6624_);
v_a_6728_ = lean_ctor_get(v___x_6674_, 0);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6674_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6730_ = v___x_6674_;
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6674_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v___x_6733_; 
if (v_isShared_6731_ == 0)
{
v___x_6733_ = v___x_6730_;
goto v_reusejp_6732_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_a_6728_);
v___x_6733_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6732_;
}
v_reusejp_6732_:
{
return v___x_6733_;
}
}
}
}
else
{
lean_object* v_a_6736_; lean_object* v___x_6738_; uint8_t v_isShared_6739_; uint8_t v_isSharedCheck_6743_; 
lean_dec_ref(v_aux_6664_);
lean_dec_ref(v___y_6657_);
lean_dec(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec(v___y_6654_);
lean_dec_ref(v___y_6653_);
lean_dec(v___y_6651_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
lean_dec_ref(v_matcherApp_6624_);
v_a_6736_ = lean_ctor_get(v___x_6672_, 0);
v_isSharedCheck_6743_ = !lean_is_exclusive(v___x_6672_);
if (v_isSharedCheck_6743_ == 0)
{
v___x_6738_ = v___x_6672_;
v_isShared_6739_ = v_isSharedCheck_6743_;
goto v_resetjp_6737_;
}
else
{
lean_inc(v_a_6736_);
lean_dec(v___x_6672_);
v___x_6738_ = lean_box(0);
v_isShared_6739_ = v_isSharedCheck_6743_;
goto v_resetjp_6737_;
}
v_resetjp_6737_:
{
lean_object* v___x_6741_; 
if (v_isShared_6739_ == 0)
{
v___x_6741_ = v___x_6738_;
goto v_reusejp_6740_;
}
else
{
lean_object* v_reuseFailAlloc_6742_; 
v_reuseFailAlloc_6742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6742_, 0, v_a_6736_);
v___x_6741_ = v_reuseFailAlloc_6742_;
goto v_reusejp_6740_;
}
v_reusejp_6740_:
{
return v___x_6741_;
}
}
}
}
v___jp_6745_:
{
lean_object* v___x_6758_; lean_object* v_remaining_x27_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; lean_object* v___x_6762_; lean_object* v___x_6763_; lean_object* v___x_6764_; lean_object* v___x_6765_; size_t v_sz_6766_; lean_object* v___x_6767_; 
v___x_6758_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6759_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6760_ = l_Array_reverse___redArg(v___y_6751_);
v___x_6761_ = lean_array_get_size(v___x_6760_);
v___x_6762_ = l_Array_toSubarray___redArg(v___x_6760_, v___x_6758_, v___x_6761_);
lean_inc_ref(v___y_6750_);
v___x_6763_ = l_Array_reverse___redArg(v___y_6750_);
v___x_6764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6764_, 0, v___x_6758_);
lean_ctor_set(v___x_6764_, 1, v___x_6762_);
v___x_6765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6765_, 0, v_remaining_x27_6759_);
lean_ctor_set(v___x_6765_, 1, v___x_6764_);
v_sz_6766_ = lean_array_size(v___x_6763_);
v___x_6767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6763_, v_sz_6766_, v___y_6747_, v___x_6765_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
lean_dec_ref(v___x_6763_);
if (lean_obj_tag(v___x_6767_) == 0)
{
lean_object* v_a_6768_; lean_object* v_snd_6769_; 
v_a_6768_ = lean_ctor_get(v___x_6767_, 0);
lean_inc(v_a_6768_);
lean_dec_ref_known(v___x_6767_, 1);
v_snd_6769_ = lean_ctor_get(v_a_6768_, 1);
lean_inc(v_snd_6769_);
if (v_useSplitter_6625_ == 0)
{
lean_object* v_fst_6770_; lean_object* v_fst_6771_; 
lean_dec(v___y_6752_);
v_fst_6770_ = lean_ctor_get(v_a_6768_, 0);
lean_inc(v_fst_6770_);
lean_dec(v_a_6768_);
v_fst_6771_ = lean_ctor_get(v_snd_6769_, 0);
lean_inc(v_fst_6771_);
lean_dec(v_snd_6769_);
v___y_6647_ = v___y_6746_;
v___y_6648_ = v___y_6748_;
v___y_6649_ = v___y_6755_;
v___y_6650_ = v___y_6756_;
v___y_6651_ = v_fst_6771_;
v___y_6652_ = v___y_6757_;
v___y_6653_ = v_matcherLevels_6753_;
v___y_6654_ = v___x_6758_;
v___y_6655_ = v___y_6749_;
v___y_6656_ = v_fst_6770_;
v___y_6657_ = v___y_6750_;
v___y_6658_ = v___y_6754_;
v___y_6659_ = v_remaining_x27_6759_;
goto v___jp_6646_;
}
else
{
if (v_isCasesOn_6744_ == 0)
{
lean_object* v___x_6773_; uint8_t v_isShared_6774_; uint8_t v_isSharedCheck_6931_; 
v_isSharedCheck_6931_ = !lean_is_exclusive(v_matcherApp_6624_);
if (v_isSharedCheck_6931_ == 0)
{
lean_object* v_unused_6932_; lean_object* v_unused_6933_; lean_object* v_unused_6934_; lean_object* v_unused_6935_; lean_object* v_unused_6936_; lean_object* v_unused_6937_; lean_object* v_unused_6938_; lean_object* v_unused_6939_; 
v_unused_6932_ = lean_ctor_get(v_matcherApp_6624_, 7);
lean_dec(v_unused_6932_);
v_unused_6933_ = lean_ctor_get(v_matcherApp_6624_, 6);
lean_dec(v_unused_6933_);
v_unused_6934_ = lean_ctor_get(v_matcherApp_6624_, 5);
lean_dec(v_unused_6934_);
v_unused_6935_ = lean_ctor_get(v_matcherApp_6624_, 4);
lean_dec(v_unused_6935_);
v_unused_6936_ = lean_ctor_get(v_matcherApp_6624_, 3);
lean_dec(v_unused_6936_);
v_unused_6937_ = lean_ctor_get(v_matcherApp_6624_, 2);
lean_dec(v_unused_6937_);
v_unused_6938_ = lean_ctor_get(v_matcherApp_6624_, 1);
lean_dec(v_unused_6938_);
v_unused_6939_ = lean_ctor_get(v_matcherApp_6624_, 0);
lean_dec(v_unused_6939_);
v___x_6773_ = v_matcherApp_6624_;
v_isShared_6774_ = v_isSharedCheck_6931_;
goto v_resetjp_6772_;
}
else
{
lean_dec(v_matcherApp_6624_);
v___x_6773_ = lean_box(0);
v_isShared_6774_ = v_isSharedCheck_6931_;
goto v_resetjp_6772_;
}
v_resetjp_6772_:
{
lean_object* v_fst_6775_; lean_object* v___x_6777_; uint8_t v_isShared_6778_; uint8_t v_isSharedCheck_6929_; 
v_fst_6775_ = lean_ctor_get(v_a_6768_, 0);
v_isSharedCheck_6929_ = !lean_is_exclusive(v_a_6768_);
if (v_isSharedCheck_6929_ == 0)
{
lean_object* v_unused_6930_; 
v_unused_6930_ = lean_ctor_get(v_a_6768_, 1);
lean_dec(v_unused_6930_);
v___x_6777_ = v_a_6768_;
v_isShared_6778_ = v_isSharedCheck_6929_;
goto v_resetjp_6776_;
}
else
{
lean_inc(v_fst_6775_);
lean_dec(v_a_6768_);
v___x_6777_ = lean_box(0);
v_isShared_6778_ = v_isSharedCheck_6929_;
goto v_resetjp_6776_;
}
v_resetjp_6776_:
{
lean_object* v_fst_6779_; lean_object* v___x_6781_; uint8_t v_isShared_6782_; uint8_t v_isSharedCheck_6927_; 
v_fst_6779_ = lean_ctor_get(v_snd_6769_, 0);
v_isSharedCheck_6927_ = !lean_is_exclusive(v_snd_6769_);
if (v_isSharedCheck_6927_ == 0)
{
lean_object* v_unused_6928_; 
v_unused_6928_ = lean_ctor_get(v_snd_6769_, 1);
lean_dec(v_unused_6928_);
v___x_6781_ = v_snd_6769_;
v_isShared_6782_ = v_isSharedCheck_6927_;
goto v_resetjp_6780_;
}
else
{
lean_inc(v_fst_6779_);
lean_dec(v_snd_6769_);
v___x_6781_ = lean_box(0);
v_isShared_6782_ = v_isSharedCheck_6927_;
goto v_resetjp_6780_;
}
v_resetjp_6780_:
{
lean_object* v___x_6783_; lean_object* v___x_6784_; lean_object* v_aux1_6785_; lean_object* v_aux1_6786_; lean_object* v_aux1_6787_; lean_object* v___x_6788_; lean_object* v___x_6789_; lean_object* v___x_6790_; lean_object* v___x_6791_; lean_object* v___x_6792_; lean_object* v___f_6793_; uint8_t v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; 
lean_inc_ref(v_matcherLevels_6753_);
v___x_6783_ = lean_array_to_list(v_matcherLevels_6753_);
lean_inc(v___x_6783_);
lean_inc(v_matcherName_6639_);
v___x_6784_ = l_Lean_mkConst(v_matcherName_6639_, v___x_6783_);
v_aux1_6785_ = l_Lean_mkAppN(v___x_6784_, v___y_6746_);
lean_inc_ref(v___y_6749_);
v_aux1_6786_ = l_Lean_Expr_app___override(v_aux1_6785_, v___y_6749_);
v_aux1_6787_ = l_Lean_mkAppN(v_aux1_6786_, v___y_6750_);
v___x_6788_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6787_, 2);
v___x_6789_ = l_Lean_indentExpr(v_aux1_6787_);
v___x_6790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6790_, 0, v___x_6788_);
lean_ctor_set(v___x_6790_, 1, v___x_6789_);
v___x_6791_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6792_, 0, v___x_6790_);
lean_ctor_set(v___x_6792_, 1, v___x_6791_);
v___f_6793_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6793_, 0, v___x_6792_);
v___x_6794_ = 0;
v___x_6795_ = lean_box(v___x_6794_);
v___x_6796_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6796_, 0, v_aux1_6787_);
lean_closure_set(v___x_6796_, 1, v___x_6795_);
v___x_6797_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6796_, v___f_6793_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
if (lean_obj_tag(v___x_6797_) == 0)
{
lean_object* v___x_6798_; lean_object* v___x_6799_; 
lean_dec_ref_known(v___x_6797_, 1);
v___x_6798_ = lean_array_get_size(v_alts_6644_);
v___x_6799_ = l_Lean_Meta_inferArgumentTypesN(v___x_6798_, v_aux1_6787_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
if (lean_obj_tag(v___x_6799_) == 0)
{
lean_object* v_a_6800_; lean_object* v___x_6801_; 
v_a_6800_ = lean_ctor_get(v___x_6799_, 0);
lean_inc(v_a_6800_);
lean_dec_ref_known(v___x_6799_, 1);
lean_inc(v___y_6757_);
lean_inc_ref(v___y_6756_);
lean_inc(v___y_6755_);
lean_inc_ref(v___y_6754_);
v___x_6801_ = lean_get_match_equations_for(v_matcherName_6639_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
if (lean_obj_tag(v___x_6801_) == 0)
{
lean_object* v_a_6802_; lean_object* v_splitterName_6803_; lean_object* v_splitterMatchInfo_6804_; lean_object* v___x_6805_; lean_object* v_aux2_6806_; lean_object* v_aux2_6807_; lean_object* v_aux2_6808_; lean_object* v___x_6809_; lean_object* v___x_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; lean_object* v___f_6813_; lean_object* v___x_6814_; lean_object* v___x_6815_; lean_object* v___x_6816_; 
v_a_6802_ = lean_ctor_get(v___x_6801_, 0);
lean_inc(v_a_6802_);
lean_dec_ref_known(v___x_6801_, 1);
v_splitterName_6803_ = lean_ctor_get(v_a_6802_, 1);
lean_inc_n(v_splitterName_6803_, 2);
v_splitterMatchInfo_6804_ = lean_ctor_get(v_a_6802_, 2);
lean_inc_ref(v_splitterMatchInfo_6804_);
lean_dec(v_a_6802_);
v___x_6805_ = l_Lean_mkConst(v_splitterName_6803_, v___x_6783_);
v_aux2_6806_ = l_Lean_mkAppN(v___x_6805_, v___y_6746_);
lean_inc_ref(v___y_6749_);
v_aux2_6807_ = l_Lean_Expr_app___override(v_aux2_6806_, v___y_6749_);
v_aux2_6808_ = l_Lean_mkAppN(v_aux2_6807_, v___y_6750_);
v___x_6809_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6808_, 2);
v___x_6810_ = l_Lean_indentExpr(v_aux2_6808_);
v___x_6811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6811_, 0, v___x_6809_);
lean_ctor_set(v___x_6811_, 1, v___x_6810_);
v___x_6812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6812_, 0, v___x_6811_);
lean_ctor_set(v___x_6812_, 1, v___x_6791_);
v___f_6813_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6813_, 0, v___x_6812_);
v___x_6814_ = lean_box(v___x_6794_);
v___x_6815_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6815_, 0, v_aux2_6808_);
lean_closure_set(v___x_6815_, 1, v___x_6814_);
v___x_6816_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6815_, v___f_6813_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
if (lean_obj_tag(v___x_6816_) == 0)
{
lean_object* v___x_6817_; 
lean_dec_ref_known(v___x_6816_, 1);
v___x_6817_ = l_Lean_Meta_inferArgumentTypesN(v___x_6798_, v_aux2_6808_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
if (lean_obj_tag(v___x_6817_) == 0)
{
lean_object* v_a_6818_; lean_object* v_numParams_6819_; lean_object* v_numDiscrs_6820_; lean_object* v_altInfos_6821_; lean_object* v_uElimPos_x3f_6822_; lean_object* v_overlaps_6823_; lean_object* v_altInfos_6824_; lean_object* v___x_6826_; uint8_t v_isShared_6827_; uint8_t v_isSharedCheck_6881_; 
v_a_6818_ = lean_ctor_get(v___x_6817_, 0);
lean_inc(v_a_6818_);
lean_dec_ref_known(v___x_6817_, 1);
v_numParams_6819_ = lean_ctor_get(v_toMatcherInfo_6638_, 0);
lean_inc(v_numParams_6819_);
v_numDiscrs_6820_ = lean_ctor_get(v_toMatcherInfo_6638_, 1);
lean_inc(v_numDiscrs_6820_);
v_altInfos_6821_ = lean_ctor_get(v_toMatcherInfo_6638_, 2);
lean_inc_ref(v_altInfos_6821_);
v_uElimPos_x3f_6822_ = lean_ctor_get(v_toMatcherInfo_6638_, 3);
lean_inc(v_uElimPos_x3f_6822_);
v_overlaps_6823_ = lean_ctor_get(v_toMatcherInfo_6638_, 5);
lean_inc_ref(v_overlaps_6823_);
lean_dec_ref(v_toMatcherInfo_6638_);
v_altInfos_6824_ = lean_ctor_get(v_splitterMatchInfo_6804_, 2);
v_isSharedCheck_6881_ = !lean_is_exclusive(v_splitterMatchInfo_6804_);
if (v_isSharedCheck_6881_ == 0)
{
lean_object* v_unused_6882_; lean_object* v_unused_6883_; lean_object* v_unused_6884_; lean_object* v_unused_6885_; lean_object* v_unused_6886_; 
v_unused_6882_ = lean_ctor_get(v_splitterMatchInfo_6804_, 5);
lean_dec(v_unused_6882_);
v_unused_6883_ = lean_ctor_get(v_splitterMatchInfo_6804_, 4);
lean_dec(v_unused_6883_);
v_unused_6884_ = lean_ctor_get(v_splitterMatchInfo_6804_, 3);
lean_dec(v_unused_6884_);
v_unused_6885_ = lean_ctor_get(v_splitterMatchInfo_6804_, 1);
lean_dec(v_unused_6885_);
v_unused_6886_ = lean_ctor_get(v_splitterMatchInfo_6804_, 0);
lean_dec(v_unused_6886_);
v___x_6826_ = v_splitterMatchInfo_6804_;
v_isShared_6827_ = v_isSharedCheck_6881_;
goto v_resetjp_6825_;
}
else
{
lean_inc(v_altInfos_6824_);
lean_dec(v_splitterMatchInfo_6804_);
v___x_6826_ = lean_box(0);
v_isShared_6827_ = v_isSharedCheck_6881_;
goto v_resetjp_6825_;
}
v_resetjp_6825_:
{
lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; lean_object* v___x_6831_; lean_object* v___x_6832_; lean_object* v___x_6833_; lean_object* v___x_6834_; lean_object* v___x_6835_; lean_object* v___x_6836_; lean_object* v___x_6838_; 
v___x_6828_ = lean_array_get_size(v_altInfos_6821_);
v___x_6829_ = lean_array_get_size(v_altInfos_6824_);
v___x_6830_ = lean_array_get_size(v_a_6800_);
v___x_6831_ = lean_array_get_size(v_a_6818_);
v___x_6832_ = l_Array_toSubarray___redArg(v_alts_6644_, v___x_6758_, v___x_6798_);
lean_inc_ref(v_altInfos_6821_);
v___x_6833_ = l_Array_toSubarray___redArg(v_altInfos_6821_, v___x_6758_, v___x_6828_);
v___x_6834_ = l_Array_toSubarray___redArg(v_altInfos_6824_, v___x_6758_, v___x_6829_);
v___x_6835_ = l_Array_toSubarray___redArg(v_a_6800_, v___x_6758_, v___x_6830_);
v___x_6836_ = l_Array_toSubarray___redArg(v_a_6818_, v___x_6758_, v___x_6831_);
if (v_isShared_6782_ == 0)
{
lean_ctor_set(v___x_6781_, 1, v___x_6836_);
lean_ctor_set(v___x_6781_, 0, v___x_6835_);
v___x_6838_ = v___x_6781_;
goto v_reusejp_6837_;
}
else
{
lean_object* v_reuseFailAlloc_6880_; 
v_reuseFailAlloc_6880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6880_, 0, v___x_6835_);
lean_ctor_set(v_reuseFailAlloc_6880_, 1, v___x_6836_);
v___x_6838_ = v_reuseFailAlloc_6880_;
goto v_reusejp_6837_;
}
v_reusejp_6837_:
{
lean_object* v___x_6840_; 
if (v_isShared_6778_ == 0)
{
lean_ctor_set(v___x_6777_, 1, v___x_6838_);
lean_ctor_set(v___x_6777_, 0, v___x_6834_);
v___x_6840_ = v___x_6777_;
goto v_reusejp_6839_;
}
else
{
lean_object* v_reuseFailAlloc_6879_; 
v_reuseFailAlloc_6879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6879_, 0, v___x_6834_);
lean_ctor_set(v_reuseFailAlloc_6879_, 1, v___x_6838_);
v___x_6840_ = v_reuseFailAlloc_6879_;
goto v_reusejp_6839_;
}
v_reusejp_6839_:
{
lean_object* v___x_6841_; lean_object* v___x_6842_; lean_object* v___x_6843_; lean_object* v___x_6844_; 
v___x_6841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6841_, 0, v___x_6833_);
lean_ctor_set(v___x_6841_, 1, v___x_6840_);
v___x_6842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6842_, 0, v___x_6832_);
lean_ctor_set(v___x_6842_, 1, v___x_6841_);
v___x_6843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6843_, 0, v_remaining_x27_6759_);
lean_ctor_set(v___x_6843_, 1, v___x_6842_);
v___x_6844_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6798_, v_onAlt_6629_, v_useSplitter_6625_, v_fst_6779_, v___y_6752_, v___x_6758_, v___x_6843_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_);
if (lean_obj_tag(v___x_6844_) == 0)
{
lean_object* v_a_6845_; lean_object* v_fst_6846_; lean_object* v___x_6847_; 
v_a_6845_ = lean_ctor_get(v___x_6844_, 0);
lean_inc(v_a_6845_);
lean_dec_ref_known(v___x_6844_, 1);
v_fst_6846_ = lean_ctor_get(v_a_6845_, 0);
lean_inc(v_fst_6846_);
lean_dec(v_a_6845_);
lean_inc(v___y_6757_);
lean_inc_ref(v___y_6756_);
lean_inc(v___y_6755_);
lean_inc_ref(v___y_6754_);
v___x_6847_ = lean_apply_6(v_onRemaining_6630_, v_remaining_6645_, v___y_6754_, v___y_6755_, v___y_6756_, v___y_6757_, lean_box(0));
if (lean_obj_tag(v___x_6847_) == 0)
{
lean_object* v_a_6848_; lean_object* v___x_6850_; uint8_t v_isShared_6851_; uint8_t v_isSharedCheck_6862_; 
v_a_6848_ = lean_ctor_get(v___x_6847_, 0);
v_isSharedCheck_6862_ = !lean_is_exclusive(v___x_6847_);
if (v_isSharedCheck_6862_ == 0)
{
v___x_6850_ = v___x_6847_;
v_isShared_6851_ = v_isSharedCheck_6862_;
goto v_resetjp_6849_;
}
else
{
lean_inc(v_a_6848_);
lean_dec(v___x_6847_);
v___x_6850_ = lean_box(0);
v_isShared_6851_ = v_isSharedCheck_6862_;
goto v_resetjp_6849_;
}
v_resetjp_6849_:
{
lean_object* v_remaining_x27_6852_; lean_object* v___x_6854_; 
v_remaining_x27_6852_ = l_Array_append___redArg(v_fst_6775_, v_a_6848_);
lean_dec(v_a_6848_);
if (v_isShared_6827_ == 0)
{
lean_ctor_set(v___x_6826_, 5, v_overlaps_6823_);
lean_ctor_set(v___x_6826_, 4, v___y_6748_);
lean_ctor_set(v___x_6826_, 3, v_uElimPos_x3f_6822_);
lean_ctor_set(v___x_6826_, 2, v_altInfos_6821_);
lean_ctor_set(v___x_6826_, 1, v_numDiscrs_6820_);
lean_ctor_set(v___x_6826_, 0, v_numParams_6819_);
v___x_6854_ = v___x_6826_;
goto v_reusejp_6853_;
}
else
{
lean_object* v_reuseFailAlloc_6861_; 
v_reuseFailAlloc_6861_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6861_, 0, v_numParams_6819_);
lean_ctor_set(v_reuseFailAlloc_6861_, 1, v_numDiscrs_6820_);
lean_ctor_set(v_reuseFailAlloc_6861_, 2, v_altInfos_6821_);
lean_ctor_set(v_reuseFailAlloc_6861_, 3, v_uElimPos_x3f_6822_);
lean_ctor_set(v_reuseFailAlloc_6861_, 4, v___y_6748_);
lean_ctor_set(v_reuseFailAlloc_6861_, 5, v_overlaps_6823_);
v___x_6854_ = v_reuseFailAlloc_6861_;
goto v_reusejp_6853_;
}
v_reusejp_6853_:
{
lean_object* v___x_6856_; 
if (v_isShared_6774_ == 0)
{
lean_ctor_set(v___x_6773_, 7, v_remaining_x27_6852_);
lean_ctor_set(v___x_6773_, 6, v_fst_6846_);
lean_ctor_set(v___x_6773_, 5, v___y_6750_);
lean_ctor_set(v___x_6773_, 4, v___y_6749_);
lean_ctor_set(v___x_6773_, 3, v___y_6746_);
lean_ctor_set(v___x_6773_, 2, v_matcherLevels_6753_);
lean_ctor_set(v___x_6773_, 1, v_splitterName_6803_);
lean_ctor_set(v___x_6773_, 0, v___x_6854_);
v___x_6856_ = v___x_6773_;
goto v_reusejp_6855_;
}
else
{
lean_object* v_reuseFailAlloc_6860_; 
v_reuseFailAlloc_6860_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6860_, 0, v___x_6854_);
lean_ctor_set(v_reuseFailAlloc_6860_, 1, v_splitterName_6803_);
lean_ctor_set(v_reuseFailAlloc_6860_, 2, v_matcherLevels_6753_);
lean_ctor_set(v_reuseFailAlloc_6860_, 3, v___y_6746_);
lean_ctor_set(v_reuseFailAlloc_6860_, 4, v___y_6749_);
lean_ctor_set(v_reuseFailAlloc_6860_, 5, v___y_6750_);
lean_ctor_set(v_reuseFailAlloc_6860_, 6, v_fst_6846_);
lean_ctor_set(v_reuseFailAlloc_6860_, 7, v_remaining_x27_6852_);
v___x_6856_ = v_reuseFailAlloc_6860_;
goto v_reusejp_6855_;
}
v_reusejp_6855_:
{
lean_object* v___x_6858_; 
if (v_isShared_6851_ == 0)
{
lean_ctor_set(v___x_6850_, 0, v___x_6856_);
v___x_6858_ = v___x_6850_;
goto v_reusejp_6857_;
}
else
{
lean_object* v_reuseFailAlloc_6859_; 
v_reuseFailAlloc_6859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6859_, 0, v___x_6856_);
v___x_6858_ = v_reuseFailAlloc_6859_;
goto v_reusejp_6857_;
}
v_reusejp_6857_:
{
return v___x_6858_;
}
}
}
}
}
else
{
lean_object* v_a_6863_; lean_object* v___x_6865_; uint8_t v_isShared_6866_; uint8_t v_isSharedCheck_6870_; 
lean_dec(v_fst_6846_);
lean_del_object(v___x_6826_);
lean_dec_ref(v_overlaps_6823_);
lean_dec(v_uElimPos_x3f_6822_);
lean_dec_ref(v_altInfos_6821_);
lean_dec(v_numDiscrs_6820_);
lean_dec(v_numParams_6819_);
lean_dec(v_splitterName_6803_);
lean_dec(v_fst_6775_);
lean_del_object(v___x_6773_);
lean_dec_ref(v_matcherLevels_6753_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
v_a_6863_ = lean_ctor_get(v___x_6847_, 0);
v_isSharedCheck_6870_ = !lean_is_exclusive(v___x_6847_);
if (v_isSharedCheck_6870_ == 0)
{
v___x_6865_ = v___x_6847_;
v_isShared_6866_ = v_isSharedCheck_6870_;
goto v_resetjp_6864_;
}
else
{
lean_inc(v_a_6863_);
lean_dec(v___x_6847_);
v___x_6865_ = lean_box(0);
v_isShared_6866_ = v_isSharedCheck_6870_;
goto v_resetjp_6864_;
}
v_resetjp_6864_:
{
lean_object* v___x_6868_; 
if (v_isShared_6866_ == 0)
{
v___x_6868_ = v___x_6865_;
goto v_reusejp_6867_;
}
else
{
lean_object* v_reuseFailAlloc_6869_; 
v_reuseFailAlloc_6869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6869_, 0, v_a_6863_);
v___x_6868_ = v_reuseFailAlloc_6869_;
goto v_reusejp_6867_;
}
v_reusejp_6867_:
{
return v___x_6868_;
}
}
}
}
else
{
lean_object* v_a_6871_; lean_object* v___x_6873_; uint8_t v_isShared_6874_; uint8_t v_isSharedCheck_6878_; 
lean_del_object(v___x_6826_);
lean_dec_ref(v_overlaps_6823_);
lean_dec(v_uElimPos_x3f_6822_);
lean_dec_ref(v_altInfos_6821_);
lean_dec(v_numDiscrs_6820_);
lean_dec(v_numParams_6819_);
lean_dec(v_splitterName_6803_);
lean_dec(v_fst_6775_);
lean_del_object(v___x_6773_);
lean_dec_ref(v_matcherLevels_6753_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_onRemaining_6630_);
v_a_6871_ = lean_ctor_get(v___x_6844_, 0);
v_isSharedCheck_6878_ = !lean_is_exclusive(v___x_6844_);
if (v_isSharedCheck_6878_ == 0)
{
v___x_6873_ = v___x_6844_;
v_isShared_6874_ = v_isSharedCheck_6878_;
goto v_resetjp_6872_;
}
else
{
lean_inc(v_a_6871_);
lean_dec(v___x_6844_);
v___x_6873_ = lean_box(0);
v_isShared_6874_ = v_isSharedCheck_6878_;
goto v_resetjp_6872_;
}
v_resetjp_6872_:
{
lean_object* v___x_6876_; 
if (v_isShared_6874_ == 0)
{
v___x_6876_ = v___x_6873_;
goto v_reusejp_6875_;
}
else
{
lean_object* v_reuseFailAlloc_6877_; 
v_reuseFailAlloc_6877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6877_, 0, v_a_6871_);
v___x_6876_ = v_reuseFailAlloc_6877_;
goto v_reusejp_6875_;
}
v_reusejp_6875_:
{
return v___x_6876_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6887_; lean_object* v___x_6889_; uint8_t v_isShared_6890_; uint8_t v_isSharedCheck_6894_; 
lean_dec_ref(v_splitterMatchInfo_6804_);
lean_dec(v_splitterName_6803_);
lean_dec(v_a_6800_);
lean_del_object(v___x_6781_);
lean_dec(v_fst_6779_);
lean_del_object(v___x_6777_);
lean_dec(v_fst_6775_);
lean_del_object(v___x_6773_);
lean_dec_ref(v_matcherLevels_6753_);
lean_dec(v___y_6752_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
v_a_6887_ = lean_ctor_get(v___x_6817_, 0);
v_isSharedCheck_6894_ = !lean_is_exclusive(v___x_6817_);
if (v_isSharedCheck_6894_ == 0)
{
v___x_6889_ = v___x_6817_;
v_isShared_6890_ = v_isSharedCheck_6894_;
goto v_resetjp_6888_;
}
else
{
lean_inc(v_a_6887_);
lean_dec(v___x_6817_);
v___x_6889_ = lean_box(0);
v_isShared_6890_ = v_isSharedCheck_6894_;
goto v_resetjp_6888_;
}
v_resetjp_6888_:
{
lean_object* v___x_6892_; 
if (v_isShared_6890_ == 0)
{
v___x_6892_ = v___x_6889_;
goto v_reusejp_6891_;
}
else
{
lean_object* v_reuseFailAlloc_6893_; 
v_reuseFailAlloc_6893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_a_6887_);
v___x_6892_ = v_reuseFailAlloc_6893_;
goto v_reusejp_6891_;
}
v_reusejp_6891_:
{
return v___x_6892_;
}
}
}
}
else
{
lean_object* v_a_6895_; lean_object* v___x_6897_; uint8_t v_isShared_6898_; uint8_t v_isSharedCheck_6902_; 
lean_dec_ref(v_aux2_6808_);
lean_dec_ref(v_splitterMatchInfo_6804_);
lean_dec(v_splitterName_6803_);
lean_dec(v_a_6800_);
lean_del_object(v___x_6781_);
lean_dec(v_fst_6779_);
lean_del_object(v___x_6777_);
lean_dec(v_fst_6775_);
lean_del_object(v___x_6773_);
lean_dec_ref(v_matcherLevels_6753_);
lean_dec(v___y_6752_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
v_a_6895_ = lean_ctor_get(v___x_6816_, 0);
v_isSharedCheck_6902_ = !lean_is_exclusive(v___x_6816_);
if (v_isSharedCheck_6902_ == 0)
{
v___x_6897_ = v___x_6816_;
v_isShared_6898_ = v_isSharedCheck_6902_;
goto v_resetjp_6896_;
}
else
{
lean_inc(v_a_6895_);
lean_dec(v___x_6816_);
v___x_6897_ = lean_box(0);
v_isShared_6898_ = v_isSharedCheck_6902_;
goto v_resetjp_6896_;
}
v_resetjp_6896_:
{
lean_object* v___x_6900_; 
if (v_isShared_6898_ == 0)
{
v___x_6900_ = v___x_6897_;
goto v_reusejp_6899_;
}
else
{
lean_object* v_reuseFailAlloc_6901_; 
v_reuseFailAlloc_6901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6901_, 0, v_a_6895_);
v___x_6900_ = v_reuseFailAlloc_6901_;
goto v_reusejp_6899_;
}
v_reusejp_6899_:
{
return v___x_6900_;
}
}
}
}
else
{
lean_object* v_a_6903_; lean_object* v___x_6905_; uint8_t v_isShared_6906_; uint8_t v_isSharedCheck_6910_; 
lean_dec(v_a_6800_);
lean_dec(v___x_6783_);
lean_del_object(v___x_6781_);
lean_dec(v_fst_6779_);
lean_del_object(v___x_6777_);
lean_dec(v_fst_6775_);
lean_del_object(v___x_6773_);
lean_dec_ref(v_matcherLevels_6753_);
lean_dec(v___y_6752_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
v_a_6903_ = lean_ctor_get(v___x_6801_, 0);
v_isSharedCheck_6910_ = !lean_is_exclusive(v___x_6801_);
if (v_isSharedCheck_6910_ == 0)
{
v___x_6905_ = v___x_6801_;
v_isShared_6906_ = v_isSharedCheck_6910_;
goto v_resetjp_6904_;
}
else
{
lean_inc(v_a_6903_);
lean_dec(v___x_6801_);
v___x_6905_ = lean_box(0);
v_isShared_6906_ = v_isSharedCheck_6910_;
goto v_resetjp_6904_;
}
v_resetjp_6904_:
{
lean_object* v___x_6908_; 
if (v_isShared_6906_ == 0)
{
v___x_6908_ = v___x_6905_;
goto v_reusejp_6907_;
}
else
{
lean_object* v_reuseFailAlloc_6909_; 
v_reuseFailAlloc_6909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6909_, 0, v_a_6903_);
v___x_6908_ = v_reuseFailAlloc_6909_;
goto v_reusejp_6907_;
}
v_reusejp_6907_:
{
return v___x_6908_;
}
}
}
}
else
{
lean_object* v_a_6911_; lean_object* v___x_6913_; uint8_t v_isShared_6914_; uint8_t v_isSharedCheck_6918_; 
lean_dec(v___x_6783_);
lean_del_object(v___x_6781_);
lean_dec(v_fst_6779_);
lean_del_object(v___x_6777_);
lean_dec(v_fst_6775_);
lean_del_object(v___x_6773_);
lean_dec_ref(v_matcherLevels_6753_);
lean_dec(v___y_6752_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
v_a_6911_ = lean_ctor_get(v___x_6799_, 0);
v_isSharedCheck_6918_ = !lean_is_exclusive(v___x_6799_);
if (v_isSharedCheck_6918_ == 0)
{
v___x_6913_ = v___x_6799_;
v_isShared_6914_ = v_isSharedCheck_6918_;
goto v_resetjp_6912_;
}
else
{
lean_inc(v_a_6911_);
lean_dec(v___x_6799_);
v___x_6913_ = lean_box(0);
v_isShared_6914_ = v_isSharedCheck_6918_;
goto v_resetjp_6912_;
}
v_resetjp_6912_:
{
lean_object* v___x_6916_; 
if (v_isShared_6914_ == 0)
{
v___x_6916_ = v___x_6913_;
goto v_reusejp_6915_;
}
else
{
lean_object* v_reuseFailAlloc_6917_; 
v_reuseFailAlloc_6917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6917_, 0, v_a_6911_);
v___x_6916_ = v_reuseFailAlloc_6917_;
goto v_reusejp_6915_;
}
v_reusejp_6915_:
{
return v___x_6916_;
}
}
}
}
else
{
lean_object* v_a_6919_; lean_object* v___x_6921_; uint8_t v_isShared_6922_; uint8_t v_isSharedCheck_6926_; 
lean_dec_ref(v_aux1_6787_);
lean_dec(v___x_6783_);
lean_del_object(v___x_6781_);
lean_dec(v_fst_6779_);
lean_del_object(v___x_6777_);
lean_dec(v_fst_6775_);
lean_del_object(v___x_6773_);
lean_dec_ref(v_matcherLevels_6753_);
lean_dec(v___y_6752_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
v_a_6919_ = lean_ctor_get(v___x_6797_, 0);
v_isSharedCheck_6926_ = !lean_is_exclusive(v___x_6797_);
if (v_isSharedCheck_6926_ == 0)
{
v___x_6921_ = v___x_6797_;
v_isShared_6922_ = v_isSharedCheck_6926_;
goto v_resetjp_6920_;
}
else
{
lean_inc(v_a_6919_);
lean_dec(v___x_6797_);
v___x_6921_ = lean_box(0);
v_isShared_6922_ = v_isSharedCheck_6926_;
goto v_resetjp_6920_;
}
v_resetjp_6920_:
{
lean_object* v___x_6924_; 
if (v_isShared_6922_ == 0)
{
v___x_6924_ = v___x_6921_;
goto v_reusejp_6923_;
}
else
{
lean_object* v_reuseFailAlloc_6925_; 
v_reuseFailAlloc_6925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6925_, 0, v_a_6919_);
v___x_6924_ = v_reuseFailAlloc_6925_;
goto v_reusejp_6923_;
}
v_reusejp_6923_:
{
return v___x_6924_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6940_; lean_object* v_fst_6941_; 
lean_dec(v___y_6752_);
v_fst_6940_ = lean_ctor_get(v_a_6768_, 0);
lean_inc(v_fst_6940_);
lean_dec(v_a_6768_);
v_fst_6941_ = lean_ctor_get(v_snd_6769_, 0);
lean_inc(v_fst_6941_);
lean_dec(v_snd_6769_);
v___y_6647_ = v___y_6746_;
v___y_6648_ = v___y_6748_;
v___y_6649_ = v___y_6755_;
v___y_6650_ = v___y_6756_;
v___y_6651_ = v_fst_6941_;
v___y_6652_ = v___y_6757_;
v___y_6653_ = v_matcherLevels_6753_;
v___y_6654_ = v___x_6758_;
v___y_6655_ = v___y_6749_;
v___y_6656_ = v_fst_6940_;
v___y_6657_ = v___y_6750_;
v___y_6658_ = v___y_6754_;
v___y_6659_ = v_remaining_x27_6759_;
goto v___jp_6646_;
}
}
}
else
{
lean_object* v_a_6942_; lean_object* v___x_6944_; uint8_t v_isShared_6945_; uint8_t v_isSharedCheck_6949_; 
lean_dec_ref(v_matcherLevels_6753_);
lean_dec(v___y_6752_);
lean_dec_ref(v___y_6750_);
lean_dec_ref(v___y_6749_);
lean_dec_ref(v___y_6748_);
lean_dec_ref(v___y_6746_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
lean_dec_ref(v_matcherApp_6624_);
v_a_6942_ = lean_ctor_get(v___x_6767_, 0);
v_isSharedCheck_6949_ = !lean_is_exclusive(v___x_6767_);
if (v_isSharedCheck_6949_ == 0)
{
v___x_6944_ = v___x_6767_;
v_isShared_6945_ = v_isSharedCheck_6949_;
goto v_resetjp_6943_;
}
else
{
lean_inc(v_a_6942_);
lean_dec(v___x_6767_);
v___x_6944_ = lean_box(0);
v_isShared_6945_ = v_isSharedCheck_6949_;
goto v_resetjp_6943_;
}
v_resetjp_6943_:
{
lean_object* v___x_6947_; 
if (v_isShared_6945_ == 0)
{
v___x_6947_ = v___x_6944_;
goto v_reusejp_6946_;
}
else
{
lean_object* v_reuseFailAlloc_6948_; 
v_reuseFailAlloc_6948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_a_6942_);
v___x_6947_ = v_reuseFailAlloc_6948_;
goto v_reusejp_6946_;
}
v_reusejp_6946_:
{
return v___x_6947_;
}
}
}
}
v___jp_6950_:
{
size_t v_sz_6956_; size_t v___x_6957_; lean_object* v___x_6958_; 
v_sz_6956_ = lean_array_size(v_params_6641_);
v___x_6957_ = ((size_t)0ULL);
lean_inc_ref(v_params_6641_);
lean_inc_ref(v_onParams_6627_);
v___x_6958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6627_, v_sz_6956_, v___x_6957_, v_params_6641_, v___y_6952_, v___y_6953_, v___y_6954_, v___y_6955_);
if (lean_obj_tag(v___x_6958_) == 0)
{
lean_object* v_a_6959_; size_t v_sz_6960_; lean_object* v___x_6961_; 
v_a_6959_ = lean_ctor_get(v___x_6958_, 0);
lean_inc(v_a_6959_);
lean_dec_ref_known(v___x_6958_, 1);
v_sz_6960_ = lean_array_size(v_discrs_6643_);
lean_inc_ref(v_discrs_6643_);
v___x_6961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6627_, v_sz_6960_, v___x_6957_, v_discrs_6643_, v___y_6952_, v___y_6953_, v___y_6954_, v___y_6955_);
if (lean_obj_tag(v___x_6961_) == 0)
{
lean_object* v_a_6962_; lean_object* v___x_6963_; lean_object* v___x_6964_; lean_object* v___f_6965_; uint8_t v___x_6966_; lean_object* v___x_6967_; 
v_a_6962_ = lean_ctor_get(v___x_6961_, 0);
lean_inc_n(v_a_6962_, 2);
lean_dec_ref_known(v___x_6961_, 1);
v___x_6963_ = lean_box(v_addEqualities_6626_);
v___x_6964_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6643_);
lean_inc_ref(v_toMatcherInfo_6638_);
v___f_6965_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6965_, 0, v_onMotive_6628_);
lean_closure_set(v___f_6965_, 1, v_toMatcherInfo_6638_);
lean_closure_set(v___f_6965_, 2, v_a_6962_);
lean_closure_set(v___f_6965_, 3, v___x_6963_);
lean_closure_set(v___f_6965_, 4, v___x_6964_);
lean_closure_set(v___f_6965_, 5, v_discrs_6643_);
v___x_6966_ = 0;
lean_inc_ref(v_motive_6642_);
v___x_6967_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6642_, v___f_6965_, v___x_6966_, v___y_6952_, v___y_6953_, v___y_6954_, v___y_6955_);
if (lean_obj_tag(v___x_6967_) == 0)
{
lean_object* v_a_6968_; lean_object* v_snd_6969_; lean_object* v_snd_6970_; lean_object* v_uElimPos_x3f_6971_; 
v_a_6968_ = lean_ctor_get(v___x_6967_, 0);
lean_inc(v_a_6968_);
lean_dec_ref_known(v___x_6967_, 1);
v_snd_6969_ = lean_ctor_get(v_a_6968_, 1);
v_snd_6970_ = lean_ctor_get(v_snd_6969_, 1);
lean_inc(v_snd_6970_);
v_uElimPos_x3f_6971_ = lean_ctor_get(v_toMatcherInfo_6638_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6971_) == 0)
{
lean_object* v_fst_6972_; lean_object* v_fst_6973_; lean_object* v_snd_6974_; 
v_fst_6972_ = lean_ctor_get(v_a_6968_, 0);
lean_inc(v_fst_6972_);
lean_dec(v_a_6968_);
v_fst_6973_ = lean_ctor_get(v_snd_6970_, 0);
lean_inc(v_fst_6973_);
v_snd_6974_ = lean_ctor_get(v_snd_6970_, 1);
lean_inc(v_snd_6974_);
lean_dec(v_snd_6970_);
lean_inc_ref(v_matcherLevels_6640_);
v___y_6746_ = v_a_6959_;
v___y_6747_ = v___x_6957_;
v___y_6748_ = v_snd_6974_;
v___y_6749_ = v_fst_6972_;
v___y_6750_ = v_a_6962_;
v___y_6751_ = v_fst_6973_;
v___y_6752_ = v_numDiscrEqs_6951_;
v_matcherLevels_6753_ = v_matcherLevels_6640_;
v___y_6754_ = v___y_6952_;
v___y_6755_ = v___y_6953_;
v___y_6756_ = v___y_6954_;
v___y_6757_ = v___y_6955_;
goto v___jp_6745_;
}
else
{
lean_object* v_fst_6975_; lean_object* v_fst_6976_; lean_object* v_fst_6977_; lean_object* v_snd_6978_; lean_object* v_val_6979_; lean_object* v___x_6980_; 
lean_inc(v_snd_6969_);
v_fst_6975_ = lean_ctor_get(v_a_6968_, 0);
lean_inc(v_fst_6975_);
lean_dec(v_a_6968_);
v_fst_6976_ = lean_ctor_get(v_snd_6969_, 0);
lean_inc(v_fst_6976_);
lean_dec(v_snd_6969_);
v_fst_6977_ = lean_ctor_get(v_snd_6970_, 0);
lean_inc(v_fst_6977_);
v_snd_6978_ = lean_ctor_get(v_snd_6970_, 1);
lean_inc(v_snd_6978_);
lean_dec(v_snd_6970_);
v_val_6979_ = lean_ctor_get(v_uElimPos_x3f_6971_, 0);
lean_inc_ref(v_matcherLevels_6640_);
v___x_6980_ = lean_array_set(v_matcherLevels_6640_, v_val_6979_, v_fst_6976_);
v___y_6746_ = v_a_6959_;
v___y_6747_ = v___x_6957_;
v___y_6748_ = v_snd_6978_;
v___y_6749_ = v_fst_6975_;
v___y_6750_ = v_a_6962_;
v___y_6751_ = v_fst_6977_;
v___y_6752_ = v_numDiscrEqs_6951_;
v_matcherLevels_6753_ = v___x_6980_;
v___y_6754_ = v___y_6952_;
v___y_6755_ = v___y_6953_;
v___y_6756_ = v___y_6954_;
v___y_6757_ = v___y_6955_;
goto v___jp_6745_;
}
}
else
{
lean_object* v_a_6981_; lean_object* v___x_6983_; uint8_t v_isShared_6984_; uint8_t v_isSharedCheck_6988_; 
lean_dec(v_a_6962_);
lean_dec(v_a_6959_);
lean_dec(v_numDiscrEqs_6951_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
lean_dec_ref(v_matcherApp_6624_);
v_a_6981_ = lean_ctor_get(v___x_6967_, 0);
v_isSharedCheck_6988_ = !lean_is_exclusive(v___x_6967_);
if (v_isSharedCheck_6988_ == 0)
{
v___x_6983_ = v___x_6967_;
v_isShared_6984_ = v_isSharedCheck_6988_;
goto v_resetjp_6982_;
}
else
{
lean_inc(v_a_6981_);
lean_dec(v___x_6967_);
v___x_6983_ = lean_box(0);
v_isShared_6984_ = v_isSharedCheck_6988_;
goto v_resetjp_6982_;
}
v_resetjp_6982_:
{
lean_object* v___x_6986_; 
if (v_isShared_6984_ == 0)
{
v___x_6986_ = v___x_6983_;
goto v_reusejp_6985_;
}
else
{
lean_object* v_reuseFailAlloc_6987_; 
v_reuseFailAlloc_6987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6987_, 0, v_a_6981_);
v___x_6986_ = v_reuseFailAlloc_6987_;
goto v_reusejp_6985_;
}
v_reusejp_6985_:
{
return v___x_6986_;
}
}
}
}
else
{
lean_object* v_a_6989_; lean_object* v___x_6991_; uint8_t v_isShared_6992_; uint8_t v_isSharedCheck_6996_; 
lean_dec(v_a_6959_);
lean_dec(v_numDiscrEqs_6951_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
lean_dec_ref(v_onMotive_6628_);
lean_dec_ref(v_matcherApp_6624_);
v_a_6989_ = lean_ctor_get(v___x_6961_, 0);
v_isSharedCheck_6996_ = !lean_is_exclusive(v___x_6961_);
if (v_isSharedCheck_6996_ == 0)
{
v___x_6991_ = v___x_6961_;
v_isShared_6992_ = v_isSharedCheck_6996_;
goto v_resetjp_6990_;
}
else
{
lean_inc(v_a_6989_);
lean_dec(v___x_6961_);
v___x_6991_ = lean_box(0);
v_isShared_6992_ = v_isSharedCheck_6996_;
goto v_resetjp_6990_;
}
v_resetjp_6990_:
{
lean_object* v___x_6994_; 
if (v_isShared_6992_ == 0)
{
v___x_6994_ = v___x_6991_;
goto v_reusejp_6993_;
}
else
{
lean_object* v_reuseFailAlloc_6995_; 
v_reuseFailAlloc_6995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6995_, 0, v_a_6989_);
v___x_6994_ = v_reuseFailAlloc_6995_;
goto v_reusejp_6993_;
}
v_reusejp_6993_:
{
return v___x_6994_;
}
}
}
}
else
{
lean_object* v_a_6997_; lean_object* v___x_6999_; uint8_t v_isShared_7000_; uint8_t v_isSharedCheck_7004_; 
lean_dec(v_numDiscrEqs_6951_);
lean_dec_ref(v_remaining_6645_);
lean_dec_ref(v_alts_6644_);
lean_dec(v_matcherName_6639_);
lean_dec_ref(v_toMatcherInfo_6638_);
lean_dec_ref(v_onRemaining_6630_);
lean_dec_ref(v_onAlt_6629_);
lean_dec_ref(v_onMotive_6628_);
lean_dec_ref(v_onParams_6627_);
lean_dec_ref(v_matcherApp_6624_);
v_a_6997_ = lean_ctor_get(v___x_6958_, 0);
v_isSharedCheck_7004_ = !lean_is_exclusive(v___x_6958_);
if (v_isSharedCheck_7004_ == 0)
{
v___x_6999_ = v___x_6958_;
v_isShared_7000_ = v_isSharedCheck_7004_;
goto v_resetjp_6998_;
}
else
{
lean_inc(v_a_6997_);
lean_dec(v___x_6958_);
v___x_6999_ = lean_box(0);
v_isShared_7000_ = v_isSharedCheck_7004_;
goto v_resetjp_6998_;
}
v_resetjp_6998_:
{
lean_object* v___x_7002_; 
if (v_isShared_7000_ == 0)
{
v___x_7002_ = v___x_6999_;
goto v_reusejp_7001_;
}
else
{
lean_object* v_reuseFailAlloc_7003_; 
v_reuseFailAlloc_7003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7003_, 0, v_a_6997_);
v___x_7002_ = v_reuseFailAlloc_7003_;
goto v_reusejp_7001_;
}
v_reusejp_7001_:
{
return v___x_7002_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_6624_ = stack[0].m_obj;
uint8_t v_useSplitter_6625_ = stack[1].m_num;
uint8_t v_addEqualities_6626_ = stack[2].m_num;
lean_object* v_onParams_6627_ = stack[3].m_obj;
lean_object* v_onMotive_6628_ = stack[4].m_obj;
lean_object* v_onAlt_6629_ = stack[5].m_obj;
lean_object* v_onRemaining_6630_ = stack[6].m_obj;
lean_object* v___y_6631_ = stack[7].m_obj;
lean_object* v___y_6632_ = stack[8].m_obj;
lean_object* v___y_6633_ = stack[9].m_obj;
lean_object* v___y_6634_ = stack[10].m_obj;
lean_object* v_res_7024_;
v_res_7024_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6624_, v_useSplitter_6625_, v_addEqualities_6626_, v_onParams_6627_, v_onMotive_6628_, v_onAlt_6629_, v_onRemaining_6630_, v___y_6631_, v___y_6632_, v___y_6633_, v___y_6634_);
stack->m_obj
 = v_res_7024_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_7025_, lean_object* v_useSplitter_7026_, lean_object* v_addEqualities_7027_, lean_object* v_onParams_7028_, lean_object* v_onMotive_7029_, lean_object* v_onAlt_7030_, lean_object* v_onRemaining_7031_, lean_object* v___y_7032_, lean_object* v___y_7033_, lean_object* v___y_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_){
_start:
{
uint8_t v_useSplitter_boxed_7037_; uint8_t v_addEqualities_boxed_7038_; lean_object* v_res_7039_; 
v_useSplitter_boxed_7037_ = lean_unbox(v_useSplitter_7026_);
v_addEqualities_boxed_7038_ = lean_unbox(v_addEqualities_7027_);
v_res_7039_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_7025_, v_useSplitter_boxed_7037_, v_addEqualities_boxed_7038_, v_onParams_7028_, v_onMotive_7029_, v_onAlt_7030_, v_onRemaining_7031_, v___y_7032_, v___y_7033_, v___y_7034_, v___y_7035_);
lean_dec(v___y_7035_);
lean_dec_ref(v___y_7034_);
lean_dec(v___y_7033_);
lean_dec_ref(v___y_7032_);
return v_res_7039_;
}
}
lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_7045_, lean_object* v_a_7046_, lean_object* v_a_7047_, lean_object* v_a_7048_, lean_object* v_a_7049_){
_start:
{
lean_object* v_toMatcherInfo_7051_; lean_object* v_matcherName_7052_; lean_object* v_matcherLevels_7053_; lean_object* v_params_7054_; lean_object* v_alts_7055_; lean_object* v_remaining_7056_; lean_object* v___f_7057_; lean_object* v___f_7058_; lean_object* v_nExtra_7059_; uint8_t v___x_7060_; lean_object* v___f_7061_; uint8_t v___x_7062_; lean_object* v___x_7063_; lean_object* v___x_7064_; lean_object* v___f_7065_; lean_object* v___x_7066_; 
v_toMatcherInfo_7051_ = lean_ctor_get(v_matcherApp_7045_, 0);
v_matcherName_7052_ = lean_ctor_get(v_matcherApp_7045_, 1);
v_matcherLevels_7053_ = lean_ctor_get(v_matcherApp_7045_, 2);
v_params_7054_ = lean_ctor_get(v_matcherApp_7045_, 3);
v_alts_7055_ = lean_ctor_get(v_matcherApp_7045_, 6);
v_remaining_7056_ = lean_ctor_get(v_matcherApp_7045_, 7);
v___f_7057_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_7058_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_7059_ = lean_array_get_size(v_remaining_7056_);
v___x_7060_ = 1;
v___f_7061_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_7062_ = 0;
v___x_7063_ = lean_box(v___x_7062_);
v___x_7064_ = lean_box(v___x_7060_);
lean_inc_ref(v_matcherLevels_7053_);
lean_inc_ref(v_params_7054_);
lean_inc(v_matcherName_7052_);
lean_inc_ref(v_toMatcherInfo_7051_);
lean_inc_ref(v_alts_7055_);
v___f_7065_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_7065_, 0, v_nExtra_7059_);
lean_closure_set(v___f_7065_, 1, v___x_7063_);
lean_closure_set(v___f_7065_, 2, v___x_7064_);
lean_closure_set(v___f_7065_, 3, v_alts_7055_);
lean_closure_set(v___f_7065_, 4, v_toMatcherInfo_7051_);
lean_closure_set(v___f_7065_, 5, v_matcherName_7052_);
lean_closure_set(v___f_7065_, 6, v_params_7054_);
lean_closure_set(v___f_7065_, 7, v_matcherLevels_7053_);
v___x_7066_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_7045_, v___x_7060_, v___x_7062_, v___f_7057_, v___f_7065_, v___f_7061_, v___f_7058_, v_a_7046_, v_a_7047_, v_a_7048_, v_a_7049_);
return v___x_7066_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_inferMatchType_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_7045_ = stack[0].m_obj;
lean_object* v_a_7046_ = stack[1].m_obj;
lean_object* v_a_7047_ = stack[2].m_obj;
lean_object* v_a_7048_ = stack[3].m_obj;
lean_object* v_a_7049_ = stack[4].m_obj;
lean_object* v_res_7067_;
v_res_7067_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_7045_, v_a_7046_, v_a_7047_, v_a_7048_, v_a_7049_);
stack->m_obj
 = v_res_7067_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_7068_, lean_object* v_a_7069_, lean_object* v_a_7070_, lean_object* v_a_7071_, lean_object* v_a_7072_, lean_object* v_a_7073_){
_start:
{
lean_object* v_res_7074_; 
v_res_7074_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_7068_, v_a_7069_, v_a_7070_, v_a_7071_, v_a_7072_);
lean_dec(v_a_7072_);
lean_dec_ref(v_a_7071_);
lean_dec(v_a_7070_);
lean_dec_ref(v_a_7069_);
return v_res_7074_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_7075_, lean_object* v_termAlt_7076_, lean_object* v_inst_7077_, lean_object* v_R_7078_, lean_object* v_a_7079_, lean_object* v_b_7080_, lean_object* v_c_7081_, lean_object* v___y_7082_, lean_object* v___y_7083_, lean_object* v___y_7084_, lean_object* v___y_7085_){
_start:
{
lean_object* v___x_7087_; 
v___x_7087_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_7075_, v_termAlt_7076_, v_a_7079_, v_b_7080_, v___y_7082_, v___y_7083_, v___y_7084_, v___y_7085_);
return v___x_7087_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_7075_ = stack[0].m_obj;
lean_object* v_termAlt_7076_ = stack[1].m_obj;
lean_object* v_a_7079_ = stack[4].m_obj;
lean_object* v_b_7080_ = stack[5].m_obj;
lean_object* v___y_7082_ = stack[7].m_obj;
lean_object* v___y_7083_ = stack[8].m_obj;
lean_object* v___y_7084_ = stack[9].m_obj;
lean_object* v___y_7085_ = stack[10].m_obj;
lean_object* v_res_7088_;
v_res_7088_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_7075_, v_termAlt_7076_, lean_box(0), lean_box(0), v_a_7079_, v_b_7080_, lean_box(0), v___y_7082_, v___y_7083_, v___y_7084_, v___y_7085_);
stack->m_obj
 = v_res_7088_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_7089_, lean_object* v_termAlt_7090_, lean_object* v_inst_7091_, lean_object* v_R_7092_, lean_object* v_a_7093_, lean_object* v_b_7094_, lean_object* v_c_7095_, lean_object* v___y_7096_, lean_object* v___y_7097_, lean_object* v___y_7098_, lean_object* v___y_7099_, lean_object* v___y_7100_){
_start:
{
lean_object* v_res_7101_; 
v_res_7101_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_7089_, v_termAlt_7090_, v_inst_7091_, v_R_7092_, v_a_7093_, v_b_7094_, v_c_7095_, v___y_7096_, v___y_7097_, v___y_7098_, v___y_7099_);
lean_dec(v___y_7099_);
lean_dec_ref(v___y_7098_);
lean_dec(v___y_7097_);
lean_dec_ref(v___y_7096_);
return v_res_7101_;
}
}
lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_7102_, lean_object* v_fvars_7103_, lean_object* v_names_7104_, lean_object* v_k_7105_, lean_object* v___y_7106_, lean_object* v___y_7107_, lean_object* v___y_7108_, lean_object* v___y_7109_){
_start:
{
lean_object* v___x_7111_; 
v___x_7111_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_7103_, v_names_7104_, v_k_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_);
return v___x_7111_;
}
}
LEAN_EXPORT void l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_7103_ = stack[1].m_obj;
lean_object* v_names_7104_ = stack[2].m_obj;
lean_object* v_k_7105_ = stack[3].m_obj;
lean_object* v___y_7106_ = stack[4].m_obj;
lean_object* v___y_7107_ = stack[5].m_obj;
lean_object* v___y_7108_ = stack[6].m_obj;
lean_object* v___y_7109_ = stack[7].m_obj;
lean_object* v_res_7112_;
v_res_7112_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_box(0), v_fvars_7103_, v_names_7104_, v_k_7105_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_);
stack->m_obj
 = v_res_7112_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_7113_, lean_object* v_fvars_7114_, lean_object* v_names_7115_, lean_object* v_k_7116_, lean_object* v___y_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_, lean_object* v___y_7120_, lean_object* v___y_7121_){
_start:
{
lean_object* v_res_7122_; 
v_res_7122_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_7113_, v_fvars_7114_, v_names_7115_, v_k_7116_, v___y_7117_, v___y_7118_, v___y_7119_, v___y_7120_);
lean_dec(v___y_7120_);
lean_dec_ref(v___y_7119_);
lean_dec(v___y_7118_);
lean_dec_ref(v___y_7117_);
lean_dec_ref(v_names_7115_);
lean_dec_ref(v_fvars_7114_);
return v_res_7122_;
}
}
lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7123_, lean_object* v_origAltType_7124_, lean_object* v_altInfo_7125_, lean_object* v_k_7126_, lean_object* v___y_7127_, lean_object* v___y_7128_, lean_object* v___y_7129_, lean_object* v___y_7130_){
_start:
{
lean_object* v___x_7132_; 
v___x_7132_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7124_, v_altInfo_7125_, v_k_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_);
return v___x_7132_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_origAltType_7124_ = stack[1].m_obj;
lean_object* v_altInfo_7125_ = stack[2].m_obj;
lean_object* v_k_7126_ = stack[3].m_obj;
lean_object* v___y_7127_ = stack[4].m_obj;
lean_object* v___y_7128_ = stack[5].m_obj;
lean_object* v___y_7129_ = stack[6].m_obj;
lean_object* v___y_7130_ = stack[7].m_obj;
lean_object* v_res_7133_;
v_res_7133_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_box(0), v_origAltType_7124_, v_altInfo_7125_, v_k_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_);
stack->m_obj
 = v_res_7133_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7134_, lean_object* v_origAltType_7135_, lean_object* v_altInfo_7136_, lean_object* v_k_7137_, lean_object* v___y_7138_, lean_object* v___y_7139_, lean_object* v___y_7140_, lean_object* v___y_7141_, lean_object* v___y_7142_){
_start:
{
lean_object* v_res_7143_; 
v_res_7143_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7134_, v_origAltType_7135_, v_altInfo_7136_, v_k_7137_, v___y_7138_, v___y_7139_, v___y_7140_, v___y_7141_);
lean_dec(v___y_7141_);
lean_dec_ref(v___y_7140_);
lean_dec(v___y_7139_);
lean_dec_ref(v___y_7138_);
return v_res_7143_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7144_, lean_object* v___y_7145_, lean_object* v___y_7146_, lean_object* v___y_7147_, lean_object* v___y_7148_){
_start:
{
lean_object* v___x_7150_; 
v___x_7150_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7144_, v___y_7148_);
return v___x_7150_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_7144_ = stack[0].m_obj;
lean_object* v___y_7145_ = stack[1].m_obj;
lean_object* v___y_7146_ = stack[2].m_obj;
lean_object* v___y_7147_ = stack[3].m_obj;
lean_object* v___y_7148_ = stack[4].m_obj;
lean_object* v_res_7151_;
v_res_7151_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7144_, v___y_7145_, v___y_7146_, v___y_7147_, v___y_7148_);
stack->m_obj
 = v_res_7151_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7152_, lean_object* v___y_7153_, lean_object* v___y_7154_, lean_object* v___y_7155_, lean_object* v___y_7156_, lean_object* v___y_7157_){
_start:
{
lean_object* v_res_7158_; 
v_res_7158_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7152_, v___y_7153_, v___y_7154_, v___y_7155_, v___y_7156_);
lean_dec(v___y_7156_);
lean_dec_ref(v___y_7155_);
lean_dec(v___y_7154_);
lean_dec_ref(v___y_7153_);
return v_res_7158_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7159_, size_t v_i_7160_, lean_object* v_bs_7161_, lean_object* v___y_7162_, lean_object* v___y_7163_, lean_object* v___y_7164_, lean_object* v___y_7165_){
_start:
{
lean_object* v___x_7167_; 
v___x_7167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7159_, v_i_7160_, v_bs_7161_, v___y_7162_, v___y_7164_, v___y_7165_);
return v___x_7167_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
size_t v_sz_7159_ = stack[0].m_num;
size_t v_i_7160_ = stack[1].m_num;
lean_object* v_bs_7161_ = stack[2].m_obj;
lean_object* v___y_7162_ = stack[3].m_obj;
lean_object* v___y_7163_ = stack[4].m_obj;
lean_object* v___y_7164_ = stack[5].m_obj;
lean_object* v___y_7165_ = stack[6].m_obj;
lean_object* v_res_7168_;
v_res_7168_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_7159_, v_i_7160_, v_bs_7161_, v___y_7162_, v___y_7163_, v___y_7164_, v___y_7165_);
stack->m_obj
 = v_res_7168_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7169_, lean_object* v_i_7170_, lean_object* v_bs_7171_, lean_object* v___y_7172_, lean_object* v___y_7173_, lean_object* v___y_7174_, lean_object* v___y_7175_, lean_object* v___y_7176_){
_start:
{
size_t v_sz_boxed_7177_; size_t v_i_boxed_7178_; lean_object* v_res_7179_; 
v_sz_boxed_7177_ = lean_unbox_usize(v_sz_7169_);
lean_dec(v_sz_7169_);
v_i_boxed_7178_ = lean_unbox_usize(v_i_7170_);
lean_dec(v_i_7170_);
v_res_7179_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7177_, v_i_boxed_7178_, v_bs_7171_, v___y_7172_, v___y_7173_, v___y_7174_, v___y_7175_);
lean_dec(v___y_7175_);
lean_dec_ref(v___y_7174_);
lean_dec(v___y_7173_);
lean_dec_ref(v___y_7172_);
return v_res_7179_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7180_, lean_object* v_onAlt_7181_, lean_object* v_extraEqualities_7182_, lean_object* v_inst_7183_, lean_object* v_R_7184_, lean_object* v_a_7185_, lean_object* v_b_7186_, lean_object* v_c_7187_, lean_object* v___y_7188_, lean_object* v___y_7189_, lean_object* v___y_7190_, lean_object* v___y_7191_){
_start:
{
lean_object* v___x_7193_; 
v___x_7193_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7180_, v_onAlt_7181_, v_extraEqualities_7182_, v_a_7185_, v_b_7186_, v___y_7188_, v___y_7189_, v___y_7190_, v___y_7191_);
return v___x_7193_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_7180_ = stack[0].m_obj;
lean_object* v_onAlt_7181_ = stack[1].m_obj;
lean_object* v_extraEqualities_7182_ = stack[2].m_obj;
lean_object* v_a_7185_ = stack[5].m_obj;
lean_object* v_b_7186_ = stack[6].m_obj;
lean_object* v___y_7188_ = stack[8].m_obj;
lean_object* v___y_7189_ = stack[9].m_obj;
lean_object* v___y_7190_ = stack[10].m_obj;
lean_object* v___y_7191_ = stack[11].m_obj;
lean_object* v_res_7194_;
v_res_7194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7180_, v_onAlt_7181_, v_extraEqualities_7182_, lean_box(0), lean_box(0), v_a_7185_, v_b_7186_, lean_box(0), v___y_7188_, v___y_7189_, v___y_7190_, v___y_7191_);
stack->m_obj
 = v_res_7194_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7195_, lean_object* v_onAlt_7196_, lean_object* v_extraEqualities_7197_, lean_object* v_inst_7198_, lean_object* v_R_7199_, lean_object* v_a_7200_, lean_object* v_b_7201_, lean_object* v_c_7202_, lean_object* v___y_7203_, lean_object* v___y_7204_, lean_object* v___y_7205_, lean_object* v___y_7206_, lean_object* v___y_7207_){
_start:
{
lean_object* v_res_7208_; 
v_res_7208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7195_, v_onAlt_7196_, v_extraEqualities_7197_, v_inst_7198_, v_R_7199_, v_a_7200_, v_b_7201_, v_c_7202_, v___y_7203_, v___y_7204_, v___y_7205_, v___y_7206_);
lean_dec(v___y_7206_);
lean_dec_ref(v___y_7205_);
lean_dec(v___y_7204_);
lean_dec_ref(v___y_7203_);
lean_dec(v_upperBound_7195_);
return v_res_7208_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7209_, lean_object* v_onAlt_7210_, uint8_t v_useSplitter_7211_, lean_object* v_extraEqualities_7212_, lean_object* v_numDiscrEqs_7213_, lean_object* v_inst_7214_, lean_object* v_R_7215_, lean_object* v_a_7216_, lean_object* v_b_7217_, lean_object* v_c_7218_, lean_object* v___y_7219_, lean_object* v___y_7220_, lean_object* v___y_7221_, lean_object* v___y_7222_){
_start:
{
lean_object* v___x_7224_; 
v___x_7224_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7209_, v_onAlt_7210_, v_useSplitter_7211_, v_extraEqualities_7212_, v_numDiscrEqs_7213_, v_a_7216_, v_b_7217_, v___y_7219_, v___y_7220_, v___y_7221_, v___y_7222_);
return v___x_7224_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_upperBound_7209_ = stack[0].m_obj;
lean_object* v_onAlt_7210_ = stack[1].m_obj;
uint8_t v_useSplitter_7211_ = stack[2].m_num;
lean_object* v_extraEqualities_7212_ = stack[3].m_obj;
lean_object* v_numDiscrEqs_7213_ = stack[4].m_obj;
lean_object* v_a_7216_ = stack[7].m_obj;
lean_object* v_b_7217_ = stack[8].m_obj;
lean_object* v___y_7219_ = stack[10].m_obj;
lean_object* v___y_7220_ = stack[11].m_obj;
lean_object* v___y_7221_ = stack[12].m_obj;
lean_object* v___y_7222_ = stack[13].m_obj;
lean_object* v_res_7225_;
v_res_7225_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7209_, v_onAlt_7210_, v_useSplitter_7211_, v_extraEqualities_7212_, v_numDiscrEqs_7213_, lean_box(0), lean_box(0), v_a_7216_, v_b_7217_, lean_box(0), v___y_7219_, v___y_7220_, v___y_7221_, v___y_7222_);
stack->m_obj
 = v_res_7225_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7226_, lean_object* v_onAlt_7227_, lean_object* v_useSplitter_7228_, lean_object* v_extraEqualities_7229_, lean_object* v_numDiscrEqs_7230_, lean_object* v_inst_7231_, lean_object* v_R_7232_, lean_object* v_a_7233_, lean_object* v_b_7234_, lean_object* v_c_7235_, lean_object* v___y_7236_, lean_object* v___y_7237_, lean_object* v___y_7238_, lean_object* v___y_7239_, lean_object* v___y_7240_){
_start:
{
uint8_t v_useSplitter_boxed_7241_; lean_object* v_res_7242_; 
v_useSplitter_boxed_7241_ = lean_unbox(v_useSplitter_7228_);
v_res_7242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7226_, v_onAlt_7227_, v_useSplitter_boxed_7241_, v_extraEqualities_7229_, v_numDiscrEqs_7230_, v_inst_7231_, v_R_7232_, v_a_7233_, v_b_7234_, v_c_7235_, v___y_7236_, v___y_7237_, v___y_7238_, v___y_7239_);
lean_dec(v___y_7239_);
lean_dec_ref(v___y_7238_);
lean_dec(v___y_7237_);
lean_dec_ref(v___y_7236_);
lean_dec(v_upperBound_7226_);
return v_res_7242_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_AltTelescopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_AltTelescopes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
}
#ifdef __cplusplus
}
#endif
