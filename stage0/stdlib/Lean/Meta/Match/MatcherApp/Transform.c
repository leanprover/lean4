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
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqMPR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Lean.Meta.Match.MatcherApp.Transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.MatcherApp.transform"};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1_value;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "assertion violation: ys.size == splitterAltInfo.numFields\n        "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(lean_object* v_e_19_, lean_object* v_maxFVars_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; uint8_t v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_28_, 0, v_k_21_);
v___x_29_ = 1;
v___x_30_ = 0;
v___x_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_31_, 0, v_maxFVars_20_);
v___x_32_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_19_, v___x_29_, v___x_30_, v___x_29_, v___x_30_, v___x_31_, v___f_28_, v_cleanupAnnotations_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
lean_dec_ref_known(v___x_31_, 1);
if (lean_obj_tag(v___x_32_) == 0)
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
v_a_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
else
{
lean_object* v_a_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_48_; 
v_a_41_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_48_ == 0)
{
v___x_43_ = v___x_32_;
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_a_41_);
lean_dec(v___x_32_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_48_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
lean_object* v___x_46_; 
if (v_isShared_44_ == 0)
{
v___x_46_ = v___x_43_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_a_41_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___boxed(lean_object* v_e_49_, lean_object* v_maxFVars_50_, lean_object* v_k_51_, lean_object* v_cleanupAnnotations_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_58_ = lean_unbox(v_cleanupAnnotations_52_);
v_res_59_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_e_49_, v_maxFVars_50_, v_k_51_, v_cleanupAnnotations_boxed_58_, v___y_53_, v___y_54_, v___y_55_, v___y_56_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_object* v_00_u03b1_60_, lean_object* v_e_61_, lean_object* v_maxFVars_62_, lean_object* v_k_63_, uint8_t v_cleanupAnnotations_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_e_61_, v_maxFVars_62_, v_k_63_, v_cleanupAnnotations_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___boxed(lean_object* v_00_u03b1_71_, lean_object* v_e_72_, lean_object* v_maxFVars_73_, lean_object* v_k_74_, lean_object* v_cleanupAnnotations_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_81_; lean_object* v_res_82_; 
v_cleanupAnnotations_boxed_81_ = lean_unbox(v_cleanupAnnotations_75_);
v_res_82_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(v_00_u03b1_71_, v_e_72_, v_maxFVars_73_, v_k_74_, v_cleanupAnnotations_boxed_81_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object* v_xs_83_, lean_object* v_alt_84_, uint8_t v___x_85_, uint8_t v_refined_86_, lean_object* v_unrefinedArgType_87_, lean_object* v_binderType_88_, lean_object* v_x_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
uint8_t v_refined_96_; 
if (v_refined_86_ == 0)
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_isExprDefEq(v_unrefinedArgType_87_, v_binderType_88_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; uint8_t v___x_121_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref_known(v___x_119_, 1);
v___x_121_ = lean_unbox(v_a_120_);
lean_dec(v_a_120_);
if (v___x_121_ == 0)
{
v_refined_96_ = v___x_85_;
goto v___jp_95_;
}
else
{
v_refined_96_ = v_refined_86_;
goto v___jp_95_;
}
}
else
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_129_; 
lean_dec_ref(v_x_89_);
lean_dec_ref(v_alt_84_);
lean_dec_ref(v_xs_83_);
v_a_122_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_129_ == 0)
{
v___x_124_ = v___x_119_;
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v___x_119_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_129_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
if (v_isShared_125_ == 0)
{
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_a_122_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
else
{
lean_dec_ref(v_binderType_88_);
lean_dec_ref(v_unrefinedArgType_87_);
v_refined_96_ = v_refined_86_;
goto v___jp_95_;
}
v___jp_95_:
{
lean_object* v___x_97_; uint8_t v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_array_push(v_xs_83_, v_x_89_);
v___x_98_ = 0;
v___x_99_ = 1;
v___x_100_ = l_Lean_Meta_mkLambdaFVars(v___x_97_, v_alt_84_, v___x_98_, v___x_85_, v___x_98_, v___x_85_, v___x_99_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec_ref(v___x_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_110_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_110_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_110_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_108_; 
v___x_105_ = lean_box(v_refined_96_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_a_101_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_106_);
v___x_108_ = v___x_103_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_106_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
}
else
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_118_; 
v_a_111_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_118_ == 0)
{
v___x_113_ = v___x_100_;
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_100_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_118_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_a_111_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object* v_xs_130_, lean_object* v_alt_131_, lean_object* v___x_132_, lean_object* v_refined_133_, lean_object* v_unrefinedArgType_134_, lean_object* v_binderType_135_, lean_object* v_x_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
uint8_t v___x_3916__boxed_142_; uint8_t v_refined_boxed_143_; lean_object* v_res_144_; 
v___x_3916__boxed_142_ = lean_unbox(v___x_132_);
v_refined_boxed_143_ = lean_unbox(v_refined_133_);
v_res_144_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_xs_130_, v_alt_131_, v___x_3916__boxed_142_, v_refined_boxed_143_, v_unrefinedArgType_134_, v_binderType_135_, v_x_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object* v_msgData_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; lean_object* v_env_152_; uint8_t v___x_153_; lean_object* v_env_154_; lean_object* v___x_155_; lean_object* v_toCold_156_; lean_object* v_mctx_157_; lean_object* v_lctx_158_; lean_object* v_options_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_151_ = lean_st_ref_get(v___y_149_);
v_env_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_env_152_);
lean_dec(v___x_151_);
v___x_153_ = 0;
v_env_154_ = l_Lean_Environment_setRecordingDeps(v_env_152_, v___x_153_);
v___x_155_ = lean_st_ref_get(v___y_147_);
v_toCold_156_ = lean_ctor_get(v___y_148_, 0);
v_mctx_157_ = lean_ctor_get(v___x_155_, 0);
lean_inc_ref(v_mctx_157_);
lean_dec(v___x_155_);
v_lctx_158_ = lean_ctor_get(v___y_146_, 2);
v_options_159_ = lean_ctor_get(v_toCold_156_, 2);
lean_inc_ref(v_options_159_);
lean_inc_ref(v_lctx_158_);
v___x_160_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_160_, 0, v_env_154_);
lean_ctor_set(v___x_160_, 1, v_mctx_157_);
lean_ctor_set(v___x_160_, 2, v_lctx_158_);
lean_ctor_set(v___x_160_, 3, v_options_159_);
v___x_161_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_msgData_145_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object* v_msgData_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msgData_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_ref_176_; lean_object* v___x_177_; lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_186_; 
v_ref_176_ = lean_ctor_get(v___y_173_, 2);
v___x_177_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
v_a_178_ = lean_ctor_get(v___x_177_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_186_ == 0)
{
v___x_180_ = v___x_177_;
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_177_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_186_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_184_; 
lean_inc(v_ref_176_);
v___x_182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_182_, 0, v_ref_176_);
lean_ctor_set(v___x_182_, 1, v_a_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 1);
lean_ctor_set(v___x_180_, 0, v___x_182_);
v___x_184_ = v___x_180_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object* v_msg_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t v___x_206_, uint8_t v_refined_207_, lean_object* v_unrefinedArgType_208_, lean_object* v_binderType_209_, lean_object* v_numParams_210_, lean_object* v_xs_211_, lean_object* v_alt_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v_a_223_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_270_ = lean_array_get_size(v_xs_211_);
v___x_271_ = lean_nat_dec_eq(v___x_270_, v_numParams_210_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_272_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5);
v___x_273_ = l_Nat_reprFast(v_numParams_210_);
v___x_274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
v___x_275_ = l_Lean_MessageData_ofFormat(v___x_274_);
v___x_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_272_);
lean_ctor_set(v___x_276_, 1, v___x_275_);
v___x_277_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_278_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_dec_ref_known(v___x_279_, 1);
goto v___jp_243_;
}
else
{
lean_object* v_a_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_287_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_binderType_209_);
lean_dec_ref(v_unrefinedArgType_208_);
v_a_280_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_287_ == 0)
{
v___x_282_ = v___x_279_;
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_a_280_);
lean_dec(v___x_279_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_287_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___x_285_; 
if (v_isShared_283_ == 0)
{
v___x_285_ = v___x_282_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_a_280_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
else
{
lean_dec(v_numParams_210_);
goto v___jp_243_;
}
v___jp_218_:
{
lean_object* v___x_224_; 
v___x_224_ = l_Lean_Meta_whnfForall(v_a_223_, v___y_221_, v___y_222_, v___y_219_, v___y_220_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
if (lean_obj_tag(v_a_225_) == 7)
{
lean_object* v_binderName_226_; lean_object* v_binderType_227_; uint8_t v_binderInfo_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___f_231_; lean_object* v___x_232_; 
v_binderName_226_ = lean_ctor_get(v_a_225_, 0);
lean_inc(v_binderName_226_);
v_binderType_227_ = lean_ctor_get(v_a_225_, 1);
lean_inc_ref_n(v_binderType_227_, 2);
v_binderInfo_228_ = lean_ctor_get_uint8(v_a_225_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_225_, 3);
v___x_229_ = lean_box(v___x_206_);
v___x_230_ = lean_box(v_refined_207_);
v___f_231_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 6);
lean_closure_set(v___f_231_, 0, v_xs_211_);
lean_closure_set(v___f_231_, 1, v_alt_212_);
lean_closure_set(v___f_231_, 2, v___x_229_);
lean_closure_set(v___f_231_, 3, v___x_230_);
lean_closure_set(v___f_231_, 4, v_unrefinedArgType_208_);
lean_closure_set(v___f_231_, 5, v_binderType_227_);
v___x_232_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_226_, v_binderInfo_228_, v_binderType_227_, v___f_231_, v___y_221_, v___y_222_, v___y_219_, v___y_220_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_a_225_);
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
v___x_233_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_234_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_233_, v___y_221_, v___y_222_, v___y_219_, v___y_220_);
return v___x_234_;
}
}
else
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
v_a_235_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_224_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_224_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
v___jp_243_:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_instantiateForall(v_binderType_209_, v_xs_211_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_a_245_);
lean_dec_ref_known(v___x_244_, 1);
v___y_219_ = v___y_215_;
v___y_220_ = v___y_216_;
v___y_221_ = v___y_213_;
v___y_222_ = v___y_214_;
v_a_223_ = v_a_245_;
goto v___jp_218_;
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_269_; 
v_a_246_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_269_ == 0)
{
v___x_248_ = v___x_244_;
v_isShared_249_ = v_isSharedCheck_269_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_269_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
uint8_t v___x_250_; 
v___x_250_ = l_Lean_Exception_isInterrupt(v_a_246_);
if (v___x_250_ == 0)
{
uint8_t v___x_251_; 
lean_inc(v_a_246_);
v___x_251_ = l_Lean_Exception_isRuntime(v_a_246_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_del_object(v___x_248_);
lean_dec(v_a_246_);
v___x_252_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_253_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_252_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_253_) == 0)
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc(v_a_254_);
lean_dec_ref_known(v___x_253_, 1);
v___y_219_ = v___y_215_;
v___y_220_ = v___y_216_;
v___y_221_ = v___y_213_;
v___y_222_ = v___y_214_;
v_a_223_ = v_a_254_;
goto v___jp_218_;
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
v_a_255_ = lean_ctor_get(v___x_253_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_253_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_253_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_253_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v___x_264_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
if (v_isShared_249_ == 0)
{
v___x_264_ = v___x_248_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_246_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v___x_267_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
if (v_isShared_249_ == 0)
{
v___x_267_ = v___x_248_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_246_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* v___x_288_, lean_object* v_refined_289_, lean_object* v_unrefinedArgType_290_, lean_object* v_binderType_291_, lean_object* v_numParams_292_, lean_object* v_xs_293_, lean_object* v_alt_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
uint8_t v___x_4092__boxed_300_; uint8_t v_refined_boxed_301_; lean_object* v_res_302_; 
v___x_4092__boxed_300_ = lean_unbox(v___x_288_);
v_refined_boxed_301_ = lean_unbox(v_refined_289_);
v_res_302_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4092__boxed_300_, v_refined_boxed_301_, v_unrefinedArgType_290_, v_binderType_291_, v_numParams_292_, v_xs_293_, v_alt_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
return v_res_302_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* v_unrefinedArgType_306_, lean_object* v_typeNew_307_, lean_object* v_altNumParams_308_, lean_object* v_alts_309_, uint8_t v_refined_310_, lean_object* v_i_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = lean_array_get_size(v_alts_309_);
v___x_318_ = lean_nat_dec_lt(v_i_311_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v_i_311_);
lean_dec_ref(v_typeNew_307_);
lean_dec_ref(v_unrefinedArgType_306_);
if (v_refined_310_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_alts_309_);
v___x_319_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
v___x_320_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_319_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_alts_309_);
return v___x_321_;
}
}
else
{
lean_object* v___x_322_; lean_object* v_alt_323_; lean_object* v_numParams_324_; lean_object* v___x_325_; 
v___x_322_ = lean_unsigned_to_nat(0u);
v_alt_323_ = lean_array_fget_borrowed(v_alts_309_, v_i_311_);
v_numParams_324_ = lean_array_get_borrowed(v___x_322_, v_altNumParams_308_, v_i_311_);
v___x_325_ = l_Lean_Meta_whnfD(v_typeNew_307_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
if (lean_obj_tag(v_a_326_) == 7)
{
lean_object* v_binderType_327_; lean_object* v_body_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___f_331_; uint8_t v___x_332_; lean_object* v___x_333_; 
v_binderType_327_ = lean_ctor_get(v_a_326_, 1);
lean_inc_ref(v_binderType_327_);
v_body_328_ = lean_ctor_get(v_a_326_, 2);
lean_inc_ref(v_body_328_);
lean_dec_ref_known(v_a_326_, 3);
v___x_329_ = lean_box(v___x_318_);
v___x_330_ = lean_box(v_refined_310_);
lean_inc_n(v_numParams_324_, 2);
lean_inc_ref(v_unrefinedArgType_306_);
v___f_331_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(v___f_331_, 0, v___x_329_);
lean_closure_set(v___f_331_, 1, v___x_330_);
lean_closure_set(v___f_331_, 2, v_unrefinedArgType_306_);
lean_closure_set(v___f_331_, 3, v_binderType_327_);
lean_closure_set(v___f_331_, 4, v_numParams_324_);
v___x_332_ = 0;
lean_inc(v_alt_323_);
v___x_333_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_alt_323_, v_numParams_324_, v___f_331_, v___x_332_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v_fst_335_; lean_object* v_snd_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v_fst_335_ = lean_ctor_get(v_a_334_, 0);
lean_inc(v_fst_335_);
v_snd_336_ = lean_ctor_get(v_a_334_, 1);
lean_inc(v_snd_336_);
lean_dec(v_a_334_);
v___x_337_ = lean_expr_instantiate1(v_body_328_, v_fst_335_);
lean_dec_ref(v_body_328_);
v___x_338_ = lean_array_fset(v_alts_309_, v_i_311_, v_fst_335_);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_i_311_, v___x_339_);
lean_dec(v_i_311_);
v___x_341_ = lean_unbox(v_snd_336_);
lean_dec(v_snd_336_);
v_typeNew_307_ = v___x_337_;
v_alts_309_ = v___x_338_;
v_refined_310_ = v___x_341_;
v_i_311_ = v___x_340_;
goto _start;
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_body_328_);
lean_dec(v_i_311_);
lean_dec_ref(v_alts_309_);
lean_dec_ref(v_unrefinedArgType_306_);
v_a_343_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_333_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_333_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_a_326_);
lean_dec(v_i_311_);
lean_dec_ref(v_alts_309_);
lean_dec_ref(v_unrefinedArgType_306_);
v___x_351_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_352_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_351_, v_a_312_, v_a_313_, v_a_314_, v_a_315_);
return v___x_352_;
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_i_311_);
lean_dec_ref(v_alts_309_);
lean_dec_ref(v_unrefinedArgType_306_);
v_a_353_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_325_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_325_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* v_unrefinedArgType_361_, lean_object* v_typeNew_362_, lean_object* v_altNumParams_363_, lean_object* v_alts_364_, lean_object* v_refined_365_, lean_object* v_i_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
uint8_t v_refined_boxed_372_; lean_object* v_res_373_; 
v_refined_boxed_372_ = lean_unbox(v_refined_365_);
v_res_373_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_361_, v_typeNew_362_, v_altNumParams_363_, v_alts_364_, v_refined_boxed_372_, v_i_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec_ref(v_altNumParams_363_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* v_00_u03b1_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* v_00_u03b1_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(v_00_u03b1_382_, v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
lean_dec(v___y_385_);
lean_dec_ref(v___y_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* v_e_390_, lean_object* v_k_391_, uint8_t v_cleanupAnnotations_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v___f_398_; uint8_t v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v___f_398_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_398_, 0, v_k_391_);
v___x_399_ = 1;
v___x_400_ = 0;
v___x_401_ = lean_box(0);
v___x_402_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_390_, v___x_399_, v___x_400_, v___x_399_, v___x_400_, v___x_401_, v___f_398_, v_cleanupAnnotations_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_a_403_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_402_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_402_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
v_a_411_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_402_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_402_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* v_e_419_, lean_object* v_k_420_, lean_object* v_cleanupAnnotations_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_427_; lean_object* v_res_428_; 
v_cleanupAnnotations_boxed_427_ = lean_unbox(v_cleanupAnnotations_421_);
v_res_428_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_419_, v_k_420_, v_cleanupAnnotations_boxed_427_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* v_00_u03b1_429_, lean_object* v_e_430_, lean_object* v_k_431_, uint8_t v_cleanupAnnotations_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; 
v___x_438_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_430_, v_k_431_, v_cleanupAnnotations_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* v_00_u03b1_439_, lean_object* v_e_440_, lean_object* v_k_441_, lean_object* v_cleanupAnnotations_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_448_; lean_object* v_res_449_; 
v_cleanupAnnotations_boxed_448_ = lean_unbox(v_cleanupAnnotations_442_);
v_res_449_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(v_00_u03b1_439_, v_e_440_, v_k_441_, v_cleanupAnnotations_boxed_448_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* v___x_450_, lean_object* v_motiveArgs_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
lean_object* v_zero_454_; uint8_t v_isZero_455_; 
v_zero_454_ = lean_unsigned_to_nat(0u);
v_isZero_455_ = lean_nat_dec_eq(v_x_452_, v_zero_454_);
if (v_isZero_455_ == 1)
{
lean_dec(v_x_452_);
return v_x_453_;
}
else
{
lean_object* v_one_456_; lean_object* v_n_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_one_456_ = lean_unsigned_to_nat(1u);
v_n_457_ = lean_nat_sub(v_x_452_, v_one_456_);
lean_dec(v_x_452_);
v___x_458_ = lean_array_fget_borrowed(v___x_450_, v_n_457_);
v___x_459_ = l_Lean_Expr_isFVar(v___x_458_);
if (v___x_459_ == 0)
{
v_x_452_ = v_n_457_;
goto _start;
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = l_Lean_instInhabitedExpr;
v___x_462_ = lean_array_get_borrowed(v___x_461_, v_motiveArgs_451_, v_n_457_);
lean_inc(v___x_458_);
v___x_463_ = l_Lean_Expr_replaceFVar(v_x_453_, v___x_458_, v___x_462_);
lean_dec_ref(v_x_453_);
v_x_452_ = v_n_457_;
v_x_453_ = v___x_463_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* v___x_465_, lean_object* v_motiveArgs_466_, lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_465_, v_motiveArgs_466_, v_x_467_, v_x_468_);
lean_dec_ref(v_motiveArgs_466_);
lean_dec_ref(v___x_465_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* v___x_470_, lean_object* v_motiveArgs_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_zero_474_; uint8_t v_isZero_475_; 
v_zero_474_ = lean_unsigned_to_nat(0u);
v_isZero_475_ = lean_nat_dec_eq(v_x_472_, v_zero_474_);
if (v_isZero_475_ == 1)
{
return v_x_473_;
}
else
{
lean_object* v_one_476_; lean_object* v_n_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_one_476_ = lean_unsigned_to_nat(1u);
v_n_477_ = lean_nat_sub(v_x_472_, v_one_476_);
v___x_478_ = lean_array_fget_borrowed(v___x_470_, v_n_477_);
v___x_479_ = l_Lean_Expr_isFVar(v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_470_, v_motiveArgs_471_, v_n_477_, v_x_473_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = l_Lean_instInhabitedExpr;
v___x_482_ = lean_array_get_borrowed(v___x_481_, v_motiveArgs_471_, v_n_477_);
lean_inc(v___x_478_);
v___x_483_ = l_Lean_Expr_replaceFVar(v_x_473_, v___x_478_, v___x_482_);
lean_dec_ref(v_x_473_);
v___x_484_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_470_, v_motiveArgs_471_, v_n_477_, v___x_483_);
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* v___x_485_, lean_object* v_motiveArgs_486_, lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v___x_485_, v_motiveArgs_486_, v_x_487_, v_x_488_);
lean_dec(v_x_487_);
lean_dec_ref(v_motiveArgs_486_);
lean_dec_ref(v___x_485_);
return v_res_489_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2));
v___x_495_ = l_Lean_stringToMessageData(v___x_494_);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4));
v___x_498_ = l_Lean_stringToMessageData(v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_499_, lean_object* v_e_500_, lean_object* v_discrs_501_, lean_object* v_toMatcherInfo_502_, lean_object* v_remaining_503_, lean_object* v_params_504_, lean_object* v_matcherName_505_, lean_object* v_alts_506_, lean_object* v_matcherLevels_507_, lean_object* v_motiveArgs_508_, lean_object* v_motiveBody_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; uint8_t v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v_matcherLevels_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_array_get_size(v_motiveArgs_508_);
v___x_660_ = lean_array_get_size(v_discrs_501_);
v___x_661_ = lean_nat_dec_eq(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_motiveBody_509_);
lean_dec_ref(v_matcherLevels_507_);
lean_dec_ref(v_alts_506_);
lean_dec(v_matcherName_505_);
lean_dec_ref(v_params_504_);
lean_dec_ref(v_toMatcherInfo_502_);
lean_dec_ref(v_discrs_501_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v___x_662_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_663_ = l_Nat_reprFast(v___x_660_);
v___x_664_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
v___x_665_ = l_Lean_MessageData_ofFormat(v___x_664_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_662_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_668_, v___y_510_, v___y_511_, v___y_512_, v___y_513_);
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
else
{
v___y_619_ = v___y_510_;
v___y_620_ = v___y_511_;
v___y_621_ = v___y_512_;
v___y_622_ = v___y_513_;
goto v___jp_618_;
}
v___jp_515_:
{
lean_object* v___x_531_; 
lean_inc(v___y_530_);
lean_inc_ref(v___y_529_);
lean_inc(v___y_528_);
lean_inc_ref(v___y_527_);
v___x_531_ = lean_infer_type(v___y_524_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_499_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_517_, v_a_532_, v___x_533_, v___y_526_, v___y_523_, v___x_534_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec_ref(v___x_533_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_548_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_548_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_548_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_mk_empty_array_with_capacity(v___x_540_);
v___x_542_ = lean_array_push(v___x_541_, v_e_500_);
v___x_543_ = l_Array_append___redArg(v___x_542_, v___y_520_);
v___x_544_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_544_, 0, v___y_516_);
lean_ctor_set(v___x_544_, 1, v___y_522_);
lean_ctor_set(v___x_544_, 2, v___y_519_);
lean_ctor_set(v___x_544_, 3, v___y_521_);
lean_ctor_set(v___x_544_, 4, v___y_525_);
lean_ctor_set(v___x_544_, 5, v___y_518_);
lean_ctor_set(v___x_544_, 6, v_a_536_);
lean_ctor_set(v___x_544_, 7, v___x_543_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_544_);
v___x_546_ = v___x_538_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v___y_525_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v_e_500_);
v_a_549_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_535_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_535_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec_ref(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v_a_557_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_531_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_531_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
v___jp_565_:
{
uint8_t v___x_579_; uint8_t v___x_580_; uint8_t v___x_581_; lean_object* v___x_582_; 
v___x_579_ = 0;
v___x_580_ = 1;
v___x_581_ = 1;
v___x_582_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_508_, v___y_567_, v___x_579_, v___x_580_, v___x_579_, v___x_580_, v___x_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc_n(v_a_583_, 2);
lean_dec_ref_known(v___x_582_, 1);
lean_inc_ref(v_matcherLevels_574_);
v___x_584_ = lean_array_to_list(v_matcherLevels_574_);
lean_inc(v___y_572_);
v___x_585_ = l_Lean_mkConst(v___y_572_, v___x_584_);
v___x_586_ = l_Lean_mkAppN(v___x_585_, v___y_571_);
v___x_587_ = l_Lean_Expr_app___override(v___x_586_, v_a_583_);
v___x_588_ = l_Lean_mkAppN(v___x_587_, v___y_570_);
lean_inc_ref(v___x_588_);
v___x_589_ = l_Lean_Meta_isTypeCorrect(v___x_588_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; uint8_t v___x_591_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v___x_591_ = lean_unbox(v_a_590_);
lean_dec(v_a_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v___x_588_);
lean_dec(v_a_583_);
lean_dec_ref(v_matcherLevels_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v___x_592_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_593_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_592_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
else
{
v___y_516_ = v___y_566_;
v___y_517_ = v___y_568_;
v___y_518_ = v___y_570_;
v___y_519_ = v_matcherLevels_574_;
v___y_520_ = v___y_569_;
v___y_521_ = v___y_571_;
v___y_522_ = v___y_572_;
v___y_523_ = v___x_579_;
v___y_524_ = v___x_588_;
v___y_525_ = v_a_583_;
v___y_526_ = v___y_573_;
v___y_527_ = v___y_575_;
v___y_528_ = v___y_576_;
v___y_529_ = v___y_577_;
v___y_530_ = v___y_578_;
goto v___jp_515_;
}
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec_ref(v___x_588_);
lean_dec(v_a_583_);
lean_dec_ref(v_matcherLevels_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v_a_602_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_589_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_589_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_617_; 
lean_dec_ref(v_matcherLevels_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v_a_610_ = lean_ctor_get(v___x_582_, 0);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_617_ == 0)
{
v___x_612_ = v___x_582_;
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_582_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_617_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_610_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
}
v___jp_618_:
{
lean_object* v___x_623_; 
lean_inc(v___y_622_);
lean_inc_ref(v___y_621_);
lean_inc(v___y_620_);
lean_inc_ref(v___y_619_);
lean_inc_ref(v_e_500_);
v___x_623_ = lean_infer_type(v_e_500_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc_n(v_a_624_, 2);
lean_dec_ref_known(v___x_623_, 1);
v___x_625_ = lean_array_get_size(v_discrs_501_);
v___x_626_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_501_, v_motiveArgs_508_, v___x_625_, v_a_624_);
v___x_627_ = l_Lean_mkArrow(v___x_626_, v_motiveBody_509_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_uElimPos_x3f_628_; 
v_uElimPos_x3f_628_ = lean_ctor_get(v_toMatcherInfo_502_, 3);
if (lean_obj_tag(v_uElimPos_x3f_628_) == 0)
{
lean_object* v_a_629_; 
v_a_629_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_627_, 1);
v___y_566_ = v_toMatcherInfo_502_;
v___y_567_ = v_a_629_;
v___y_568_ = v_a_624_;
v___y_569_ = v_remaining_503_;
v___y_570_ = v_discrs_501_;
v___y_571_ = v_params_504_;
v___y_572_ = v_matcherName_505_;
v___y_573_ = v_alts_506_;
v_matcherLevels_574_ = v_matcherLevels_507_;
v___y_575_ = v___y_619_;
v___y_576_ = v___y_620_;
v___y_577_ = v___y_621_;
v___y_578_ = v___y_622_;
goto v___jp_565_;
}
else
{
lean_object* v_a_630_; lean_object* v_val_631_; lean_object* v___x_632_; 
v_a_630_ = lean_ctor_get(v___x_627_, 0);
lean_inc_n(v_a_630_, 2);
lean_dec_ref_known(v___x_627_, 1);
v_val_631_ = lean_ctor_get(v_uElimPos_x3f_628_, 0);
v___x_632_ = l_Lean_Meta_getLevel(v_a_630_, v___y_619_, v___y_620_, v___y_621_, v___y_622_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v_a_633_; lean_object* v___x_634_; 
v_a_633_ = lean_ctor_get(v___x_632_, 0);
lean_inc(v_a_633_);
lean_dec_ref_known(v___x_632_, 1);
v___x_634_ = lean_array_set(v_matcherLevels_507_, v_val_631_, v_a_633_);
v___y_566_ = v_toMatcherInfo_502_;
v___y_567_ = v_a_630_;
v___y_568_ = v_a_624_;
v___y_569_ = v_remaining_503_;
v___y_570_ = v_discrs_501_;
v___y_571_ = v_params_504_;
v___y_572_ = v_matcherName_505_;
v___y_573_ = v_alts_506_;
v_matcherLevels_574_ = v___x_634_;
v___y_575_ = v___y_619_;
v___y_576_ = v___y_620_;
v___y_577_ = v___y_621_;
v___y_578_ = v___y_622_;
goto v___jp_565_;
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_a_630_);
lean_dec(v_a_624_);
lean_dec_ref(v_matcherLevels_507_);
lean_dec_ref(v_alts_506_);
lean_dec(v_matcherName_505_);
lean_dec_ref(v_params_504_);
lean_dec_ref(v_toMatcherInfo_502_);
lean_dec_ref(v_discrs_501_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v_a_635_ = lean_ctor_get(v___x_632_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_632_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_632_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
lean_dec(v_a_624_);
lean_dec_ref(v_matcherLevels_507_);
lean_dec_ref(v_alts_506_);
lean_dec(v_matcherName_505_);
lean_dec_ref(v_params_504_);
lean_dec_ref(v_toMatcherInfo_502_);
lean_dec_ref(v_discrs_501_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v_a_643_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_627_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_627_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_motiveBody_509_);
lean_dec_ref(v_matcherLevels_507_);
lean_dec_ref(v_alts_506_);
lean_dec(v_matcherName_505_);
lean_dec_ref(v_params_504_);
lean_dec_ref(v_toMatcherInfo_502_);
lean_dec_ref(v_discrs_501_);
lean_dec_ref(v_e_500_);
lean_dec_ref(v_matcherApp_499_);
v_a_651_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_623_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_623_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_678_, lean_object* v_e_679_, lean_object* v_discrs_680_, lean_object* v_toMatcherInfo_681_, lean_object* v_remaining_682_, lean_object* v_params_683_, lean_object* v_matcherName_684_, lean_object* v_alts_685_, lean_object* v_matcherLevels_686_, lean_object* v_motiveArgs_687_, lean_object* v_motiveBody_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_678_, v_e_679_, v_discrs_680_, v_toMatcherInfo_681_, v_remaining_682_, v_params_683_, v_matcherName_684_, v_alts_685_, v_matcherLevels_686_, v_motiveArgs_687_, v_motiveBody_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v_motiveArgs_687_);
lean_dec_ref(v_remaining_682_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* v_matcherApp_695_, lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_toMatcherInfo_702_; lean_object* v_matcherName_703_; lean_object* v_matcherLevels_704_; lean_object* v_params_705_; lean_object* v_motive_706_; lean_object* v_discrs_707_; lean_object* v_alts_708_; lean_object* v_remaining_709_; lean_object* v___f_710_; uint8_t v___x_711_; lean_object* v___x_712_; 
v_toMatcherInfo_702_ = lean_ctor_get(v_matcherApp_695_, 0);
lean_inc_ref(v_toMatcherInfo_702_);
v_matcherName_703_ = lean_ctor_get(v_matcherApp_695_, 1);
lean_inc(v_matcherName_703_);
v_matcherLevels_704_ = lean_ctor_get(v_matcherApp_695_, 2);
lean_inc_ref(v_matcherLevels_704_);
v_params_705_ = lean_ctor_get(v_matcherApp_695_, 3);
lean_inc_ref(v_params_705_);
v_motive_706_ = lean_ctor_get(v_matcherApp_695_, 4);
lean_inc_ref(v_motive_706_);
v_discrs_707_ = lean_ctor_get(v_matcherApp_695_, 5);
lean_inc_ref(v_discrs_707_);
v_alts_708_ = lean_ctor_get(v_matcherApp_695_, 6);
lean_inc_ref(v_alts_708_);
v_remaining_709_ = lean_ctor_get(v_matcherApp_695_, 7);
lean_inc_ref(v_remaining_709_);
v___f_710_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_710_, 0, v_matcherApp_695_);
lean_closure_set(v___f_710_, 1, v_e_696_);
lean_closure_set(v___f_710_, 2, v_discrs_707_);
lean_closure_set(v___f_710_, 3, v_toMatcherInfo_702_);
lean_closure_set(v___f_710_, 4, v_remaining_709_);
lean_closure_set(v___f_710_, 5, v_params_705_);
lean_closure_set(v___f_710_, 6, v_matcherName_703_);
lean_closure_set(v___f_710_, 7, v_alts_708_);
lean_closure_set(v___f_710_, 8, v_matcherLevels_704_);
v___x_711_ = 0;
v___x_712_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_706_, v___f_710_, v___x_711_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* v_matcherApp_713_, lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_713_, v_e_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* v_matcherApp_721_, lean_object* v_e_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_721_, v_e_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_737_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_737_ == 0)
{
v___x_731_ = v___x_728_;
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_728_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_737_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v_a_729_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_754_; 
v_a_738_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_754_ == 0)
{
v___x_740_ = v___x_728_;
v_isShared_741_ = v_isSharedCheck_754_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_728_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_754_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint8_t v___x_742_; 
v___x_742_ = l_Lean_Exception_isInterrupt(v_a_738_);
if (v___x_742_ == 0)
{
uint8_t v___x_743_; 
lean_inc(v_a_738_);
v___x_743_ = l_Lean_Exception_isRuntime(v_a_738_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; lean_object* v___x_746_; 
lean_dec(v_a_738_);
v___x_744_ = lean_box(0);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 0);
lean_ctor_set(v___x_740_, 0, v___x_744_);
v___x_746_ = v___x_740_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
else
{
lean_object* v___x_749_; 
if (v_isShared_741_ == 0)
{
v___x_749_ = v___x_740_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_738_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v___x_752_; 
if (v_isShared_741_ == 0)
{
v___x_752_ = v___x_740_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_738_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* v_matcherApp_755_, lean_object* v_e_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_755_, v_e_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec_ref(v_a_757_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(lean_object* v_type_763_, lean_object* v_maxFVars_x3f_764_, lean_object* v_k_765_, uint8_t v_cleanupAnnotations_766_, uint8_t v_whnfType_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v___f_773_; lean_object* v___x_774_; 
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_773_, 0, v_k_765_);
v___x_774_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_763_, v_maxFVars_x3f_764_, v___f_773_, v_cleanupAnnotations_766_, v_whnfType_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
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
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
v_a_783_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_774_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_774_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg___boxed(lean_object* v_type_791_, lean_object* v_maxFVars_x3f_792_, lean_object* v_k_793_, lean_object* v_cleanupAnnotations_794_, lean_object* v_whnfType_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_801_; uint8_t v_whnfType_boxed_802_; lean_object* v_res_803_; 
v_cleanupAnnotations_boxed_801_ = lean_unbox(v_cleanupAnnotations_794_);
v_whnfType_boxed_802_ = lean_unbox(v_whnfType_795_);
v_res_803_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_791_, v_maxFVars_x3f_792_, v_k_793_, v_cleanupAnnotations_boxed_801_, v_whnfType_boxed_802_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(lean_object* v_00_u03b1_804_, lean_object* v_type_805_, lean_object* v_maxFVars_x3f_806_, lean_object* v_k_807_, uint8_t v_cleanupAnnotations_808_, uint8_t v_whnfType_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_805_, v_maxFVars_x3f_806_, v_k_807_, v_cleanupAnnotations_808_, v_whnfType_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* v_00_u03b1_816_, lean_object* v_type_817_, lean_object* v_maxFVars_x3f_818_, lean_object* v_k_819_, lean_object* v_cleanupAnnotations_820_, lean_object* v_whnfType_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_827_; uint8_t v_whnfType_boxed_828_; lean_object* v_res_829_; 
v_cleanupAnnotations_boxed_827_ = lean_unbox(v_cleanupAnnotations_820_);
v_whnfType_boxed_828_ = lean_unbox(v_whnfType_821_);
v_res_829_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_00_u03b1_816_, v_type_817_, v_maxFVars_x3f_818_, v_k_819_, v_cleanupAnnotations_boxed_827_, v_whnfType_boxed_828_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(lean_object* v_type_830_, lean_object* v_k_831_, uint8_t v_cleanupAnnotations_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
lean_object* v___f_838_; uint8_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___f_838_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_838_, 0, v_k_831_);
v___x_839_ = 0;
v___x_840_ = lean_box(0);
v___x_841_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_839_, v___x_840_, v_type_830_, v___f_838_, v_cleanupAnnotations_832_, v___x_839_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_841_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_841_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg___boxed(lean_object* v_type_858_, lean_object* v_k_859_, lean_object* v_cleanupAnnotations_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_866_; lean_object* v_res_867_; 
v_cleanupAnnotations_boxed_866_ = lean_unbox(v_cleanupAnnotations_860_);
v_res_867_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_858_, v_k_859_, v_cleanupAnnotations_boxed_866_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(lean_object* v_00_u03b1_868_, lean_object* v_type_869_, lean_object* v_k_870_, uint8_t v_cleanupAnnotations_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_869_, v_k_870_, v_cleanupAnnotations_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___boxed(lean_object* v_00_u03b1_878_, lean_object* v_type_879_, lean_object* v_k_880_, lean_object* v_cleanupAnnotations_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_887_; lean_object* v_res_888_; 
v_cleanupAnnotations_boxed_887_ = lean_unbox(v_cleanupAnnotations_881_);
v_res_888_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(v_00_u03b1_878_, v_type_879_, v_k_880_, v_cleanupAnnotations_boxed_887_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(size_t v_sz_889_, size_t v_i_890_, lean_object* v_bs_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_lt(v_i_890_, v_sz_889_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_bs_891_);
return v___x_898_;
}
else
{
lean_object* v_v_899_; lean_object* v___x_900_; lean_object* v_bs_x27_901_; lean_object* v___x_902_; 
v_v_899_ = lean_array_uget(v_bs_891_, v_i_890_);
v___x_900_ = lean_unsigned_to_nat(0u);
v_bs_x27_901_ = lean_array_uset(v_bs_891_, v_i_890_, v___x_900_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc_ref(v___y_892_);
v___x_902_ = lean_infer_type(v_v_899_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; size_t v___x_904_; size_t v___x_905_; lean_object* v___x_906_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
v___x_904_ = ((size_t)1ULL);
v___x_905_ = lean_usize_add(v_i_890_, v___x_904_);
v___x_906_ = lean_array_uset(v_bs_x27_901_, v_i_890_, v_a_903_);
v_i_890_ = v___x_905_;
v_bs_891_ = v___x_906_;
goto _start;
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec_ref(v_bs_x27_901_);
v_a_908_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_902_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_902_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* v_sz_916_, lean_object* v_i_917_, lean_object* v_bs_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
size_t v_sz_boxed_924_; size_t v_i_boxed_925_; lean_object* v_res_926_; 
v_sz_boxed_924_ = lean_unbox_usize(v_sz_916_);
lean_dec(v_sz_916_);
v_i_boxed_925_ = lean_unbox_usize(v_i_917_);
lean_dec(v_i_917_);
v_res_926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_boxed_924_, v_i_boxed_925_, v_bs_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
return v_res_926_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__0));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(uint8_t v___x_930_, uint8_t v___x_931_, uint8_t v___x_932_, lean_object* v_a_933_, lean_object* v_fvs_934_, lean_object* v_body_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_array_get_size(v_fvs_934_);
v___x_950_ = lean_nat_dec_eq(v___x_949_, v_a_933_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v___x_951_ = lean_obj_once(&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1, &l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1);
v___x_952_ = l_Nat_reprFast(v_a_933_);
v___x_953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
v___x_954_ = l_Lean_MessageData_ofFormat(v___x_953_);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_951_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_955_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
v___x_958_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_957_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
else
{
lean_dec(v_a_933_);
goto v___jp_941_;
}
v___jp_941_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_942_ = lean_unsigned_to_nat(2u);
v___x_943_ = l_Lean_Expr_getAppNumArgs(v_body_935_);
v___x_944_ = lean_nat_sub(v___x_943_, v___x_942_);
lean_dec(v___x_943_);
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_sub(v___x_944_, v___x_945_);
lean_dec(v___x_944_);
v___x_947_ = l_Lean_Expr_getRevArg_x21(v_body_935_, v___x_946_);
v___x_948_ = l_Lean_Meta_mkLambdaFVars(v_fvs_934_, v___x_947_, v___x_930_, v___x_931_, v___x_930_, v___x_931_, v___x_932_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed(lean_object* v___x_967_, lean_object* v___x_968_, lean_object* v___x_969_, lean_object* v_a_970_, lean_object* v_fvs_971_, lean_object* v_body_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v___x_4175__boxed_978_; uint8_t v___x_4176__boxed_979_; uint8_t v___x_4177__boxed_980_; lean_object* v_res_981_; 
v___x_4175__boxed_978_ = lean_unbox(v___x_967_);
v___x_4176__boxed_979_ = lean_unbox(v___x_968_);
v___x_4177__boxed_980_ = lean_unbox(v___x_969_);
v_res_981_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(v___x_4175__boxed_978_, v___x_4176__boxed_979_, v___x_4177__boxed_980_, v_a_970_, v_fvs_971_, v_body_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec_ref(v_body_972_);
lean_dec_ref(v_fvs_971_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* v_as_982_, lean_object* v_bs_983_, lean_object* v_i_984_, lean_object* v_cs_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; uint8_t v___x_992_; 
v___x_991_ = lean_array_get_size(v_as_982_);
v___x_992_ = lean_nat_dec_lt(v_i_984_, v___x_991_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; 
lean_dec(v_i_984_);
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v_cs_985_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; uint8_t v___x_995_; 
v___x_994_ = lean_array_get_size(v_bs_983_);
v___x_995_ = lean_nat_dec_lt(v_i_984_, v___x_994_);
if (v___x_995_ == 0)
{
lean_object* v___x_996_; 
lean_dec(v_i_984_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v_cs_985_);
return v___x_996_;
}
else
{
uint8_t v___x_997_; uint8_t v___x_998_; lean_object* v_a_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___f_1003_; lean_object* v_b_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_997_ = 0;
v___x_998_ = 1;
v_a_999_ = lean_array_fget_borrowed(v_as_982_, v_i_984_);
v___x_1000_ = lean_box(v___x_997_);
v___x_1001_ = lean_box(v___x_995_);
v___x_1002_ = lean_box(v___x_998_);
lean_inc_n(v_a_999_, 2);
v___f_1003_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1003_, 0, v___x_1000_);
lean_closure_set(v___f_1003_, 1, v___x_1001_);
lean_closure_set(v___f_1003_, 2, v___x_1002_);
lean_closure_set(v___f_1003_, 3, v_a_999_);
v_b_1004_ = lean_array_fget_borrowed(v_bs_983_, v_i_984_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v_a_999_);
lean_inc(v_b_1004_);
v___x_1006_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_b_1004_, v___x_1005_, v___f_1003_, v___x_997_, v___x_997_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec_ref_known(v___x_1006_, 1);
v___x_1008_ = lean_unsigned_to_nat(1u);
v___x_1009_ = lean_nat_add(v_i_984_, v___x_1008_);
lean_dec(v_i_984_);
v___x_1010_ = lean_array_push(v_cs_985_, v_a_1007_);
v_i_984_ = v___x_1009_;
v_cs_985_ = v___x_1010_;
goto _start;
}
else
{
lean_object* v_a_1012_; lean_object* v___x_1014_; uint8_t v_isShared_1015_; uint8_t v_isSharedCheck_1019_; 
lean_dec_ref(v_cs_985_);
lean_dec(v_i_984_);
v_a_1012_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1014_ = v___x_1006_;
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
else
{
lean_inc(v_a_1012_);
lean_dec(v___x_1006_);
v___x_1014_ = lean_box(0);
v_isShared_1015_ = v_isSharedCheck_1019_;
goto v_resetjp_1013_;
}
v_resetjp_1013_:
{
lean_object* v___x_1017_; 
if (v_isShared_1015_ == 0)
{
v___x_1017_ = v___x_1014_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v_a_1012_);
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
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* v_as_1020_, lean_object* v_bs_1021_, lean_object* v_i_1022_, lean_object* v_cs_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_as_1020_, v_bs_1021_, v_i_1022_, v_cs_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec_ref(v_bs_1021_);
lean_dec_ref(v_as_1020_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* v_matcherApp_1032_, lean_object* v_altAuxs_1033_, lean_object* v_x_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
size_t v_sz_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v_sz_1040_ = lean_array_size(v_altAuxs_1033_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_1040_, v___x_1041_, v_altAuxs_1033_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v___x_1044_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_1032_);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_1047_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v___x_1044_, v_a_1043_, v___x_1045_, v___x_1046_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
lean_dec(v_a_1043_);
lean_dec_ref(v___x_1044_);
return v___x_1047_;
}
else
{
lean_dec_ref(v_matcherApp_1032_);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* v_matcherApp_1048_, lean_object* v_altAuxs_1049_, lean_object* v_x_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1048_, v_altAuxs_1049_, v_x_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec_ref(v_x_1050_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* v_motiveArgs_1057_, lean_object* v___x_1058_, lean_object* v_i_1059_, lean_object* v_a_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_){
_start:
{
lean_object* v_zero_1066_; uint8_t v_isZero_1067_; 
v_zero_1066_ = lean_unsigned_to_nat(0u);
v_isZero_1067_ = lean_nat_dec_eq(v_i_1059_, v_zero_1066_);
if (v_isZero_1067_ == 1)
{
lean_object* v___x_1068_; 
lean_dec(v_i_1059_);
v___x_1068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1068_, 0, v_a_1060_);
return v___x_1068_;
}
else
{
lean_object* v___x_1069_; lean_object* v_one_1070_; lean_object* v_n_1071_; lean_object* v_motiveArg_1072_; lean_object* v_discr_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1069_ = l_Lean_instInhabitedExpr;
v_one_1070_ = lean_unsigned_to_nat(1u);
v_n_1071_ = lean_nat_sub(v_i_1059_, v_one_1070_);
lean_dec(v_i_1059_);
v_motiveArg_1072_ = lean_array_get_borrowed(v___x_1069_, v_motiveArgs_1057_, v_n_1071_);
v_discr_1073_ = lean_array_fget_borrowed(v___x_1058_, v_n_1071_);
v___x_1074_ = lean_box(0);
lean_inc(v_discr_1073_);
v___x_1075_ = l_Lean_Meta_kabstract(v_a_1060_, v_discr_1073_, v___x_1074_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; lean_object* v___x_1077_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___x_1077_ = lean_expr_instantiate1(v_a_1076_, v_motiveArg_1072_);
lean_dec(v_a_1076_);
v_i_1059_ = v_n_1071_;
v_a_1060_ = v___x_1077_;
goto _start;
}
else
{
lean_dec(v_n_1071_);
return v___x_1075_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* v_motiveArgs_1079_, lean_object* v___x_1080_, lean_object* v_i_1081_, lean_object* v_a_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1079_, v___x_1080_, v_i_1081_, v_a_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec_ref(v___x_1080_);
lean_dec_ref(v_motiveArgs_1079_);
return v_res_1088_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1095_, lean_object* v_discrs_1096_, lean_object* v_e_1097_, lean_object* v_toMatcherInfo_1098_, lean_object* v_matcherName_1099_, lean_object* v_params_1100_, lean_object* v_matcherLevels_1101_, lean_object* v_motiveArgs_1102_, lean_object* v___motiveBody_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v___y_1110_; uint8_t v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v_matcherLevels_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v___x_1208_ = lean_array_get_size(v_motiveArgs_1102_);
v___x_1209_ = lean_array_get_size(v_discrs_1096_);
v___x_1210_ = lean_nat_dec_eq(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec_ref(v_matcherLevels_1101_);
lean_dec(v_matcherName_1099_);
lean_dec_ref(v_e_1097_);
lean_dec_ref(v___f_1095_);
v___x_1211_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
v___x_1212_ = l_Nat_reprFast(v___x_1209_);
v___x_1213_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
v___x_1214_ = l_Lean_MessageData_ofFormat(v___x_1213_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1211_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_1217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1215_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1217_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
v_a_1219_ = lean_ctor_get(v___x_1218_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1218_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1218_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1218_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
else
{
v___y_1178_ = v___y_1104_;
v___y_1179_ = v___y_1105_;
v___y_1180_ = v___y_1106_;
v___y_1181_ = v___y_1107_;
goto v___jp_1177_;
}
v___jp_1109_:
{
lean_object* v___x_1117_; 
lean_inc(v___y_1116_);
lean_inc_ref(v___y_1115_);
lean_inc(v___y_1114_);
lean_inc_ref(v___y_1113_);
v___x_1117_ = lean_infer_type(v___y_1110_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_a_1118_, v___y_1112_, v___y_1111_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___y_1112_);
v_a_1120_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1117_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1117_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
v___jp_1128_:
{
uint8_t v___x_1138_; uint8_t v___x_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; 
v___x_1138_ = 0;
v___x_1139_ = 1;
v___x_1140_ = 1;
v___x_1141_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1102_, v___y_1132_, v___x_1138_, v___x_1139_, v___x_1138_, v___x_1139_, v___x_1140_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = lean_array_to_list(v_matcherLevels_1133_);
v___x_1144_ = l_Lean_mkConst(v___y_1130_, v___x_1143_);
v___x_1145_ = l_Lean_mkAppN(v___x_1144_, v___y_1131_);
v___x_1146_ = l_Lean_Expr_app___override(v___x_1145_, v_a_1142_);
v___x_1147_ = l_Lean_mkAppN(v___x_1146_, v___y_1129_);
lean_inc_ref(v___x_1147_);
v___x_1148_ = l_Lean_Meta_isTypeCorrect(v___x_1147_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; uint8_t v___x_1150_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref_known(v___x_1148_, 1);
v___x_1150_ = lean_unbox(v_a_1149_);
lean_dec(v_a_1149_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec_ref(v___x_1147_);
lean_dec_ref(v___f_1095_);
v___x_1151_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
v___x_1152_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1151_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
v___y_1110_ = v___x_1147_;
v___y_1111_ = v___x_1138_;
v___y_1112_ = v___f_1095_;
v___y_1113_ = v___y_1134_;
v___y_1114_ = v___y_1135_;
v___y_1115_ = v___y_1136_;
v___y_1116_ = v___y_1137_;
goto v___jp_1109_;
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
lean_dec_ref(v___x_1147_);
lean_dec_ref(v___f_1095_);
v_a_1161_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1148_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1148_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_matcherLevels_1133_);
lean_dec(v___y_1130_);
lean_dec_ref(v___f_1095_);
v_a_1169_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1141_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1141_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
v___jp_1177_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_array_get_size(v_discrs_1096_);
v___x_1183_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1102_, v_discrs_1096_, v___x_1182_, v_e_1097_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v___x_1185_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_n(v_a_1184_, 2);
lean_dec_ref_known(v___x_1183_, 1);
v___x_1185_ = l_Lean_Meta_mkEq(v_a_1184_, v_a_1184_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_uElimPos_x3f_1186_; 
v_uElimPos_x3f_1186_ = lean_ctor_get(v_toMatcherInfo_1098_, 3);
if (lean_obj_tag(v_uElimPos_x3f_1186_) == 0)
{
lean_object* v_a_1187_; 
v_a_1187_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1185_, 1);
v___y_1129_ = v_discrs_1096_;
v___y_1130_ = v_matcherName_1099_;
v___y_1131_ = v_params_1100_;
v___y_1132_ = v_a_1187_;
v_matcherLevels_1133_ = v_matcherLevels_1101_;
v___y_1134_ = v___y_1178_;
v___y_1135_ = v___y_1179_;
v___y_1136_ = v___y_1180_;
v___y_1137_ = v___y_1181_;
goto v___jp_1128_;
}
else
{
lean_object* v_a_1188_; lean_object* v_val_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_a_1188_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1185_, 1);
v_val_1189_ = lean_ctor_get(v_uElimPos_x3f_1186_, 0);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_array_set(v_matcherLevels_1101_, v_val_1189_, v___x_1190_);
v___y_1129_ = v_discrs_1096_;
v___y_1130_ = v_matcherName_1099_;
v___y_1131_ = v_params_1100_;
v___y_1132_ = v_a_1188_;
v_matcherLevels_1133_ = v___x_1191_;
v___y_1134_ = v___y_1178_;
v___y_1135_ = v___y_1179_;
v___y_1136_ = v___y_1180_;
v___y_1137_ = v___y_1181_;
goto v___jp_1128_;
}
}
else
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
lean_dec_ref(v_matcherLevels_1101_);
lean_dec(v_matcherName_1099_);
lean_dec_ref(v___f_1095_);
v_a_1192_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1185_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1185_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_dec_ref(v_matcherLevels_1101_);
lean_dec(v_matcherName_1099_);
lean_dec_ref(v___f_1095_);
v_a_1200_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1183_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1183_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1227_, lean_object* v_discrs_1228_, lean_object* v_e_1229_, lean_object* v_toMatcherInfo_1230_, lean_object* v_matcherName_1231_, lean_object* v_params_1232_, lean_object* v_matcherLevels_1233_, lean_object* v_motiveArgs_1234_, lean_object* v___motiveBody_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1227_, v_discrs_1228_, v_e_1229_, v_toMatcherInfo_1230_, v_matcherName_1231_, v_params_1232_, v_matcherLevels_1233_, v_motiveArgs_1234_, v___motiveBody_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec_ref(v___motiveBody_1235_);
lean_dec_ref(v_motiveArgs_1234_);
lean_dec_ref(v_params_1232_);
lean_dec_ref(v_toMatcherInfo_1230_);
lean_dec_ref(v_discrs_1228_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* v_matcherApp_1242_, lean_object* v_e_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_toMatcherInfo_1249_; lean_object* v_matcherName_1250_; lean_object* v_matcherLevels_1251_; lean_object* v_params_1252_; lean_object* v_motive_1253_; lean_object* v_discrs_1254_; lean_object* v___f_1255_; lean_object* v___f_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; 
v_toMatcherInfo_1249_ = lean_ctor_get(v_matcherApp_1242_, 0);
lean_inc_ref(v_toMatcherInfo_1249_);
v_matcherName_1250_ = lean_ctor_get(v_matcherApp_1242_, 1);
lean_inc(v_matcherName_1250_);
v_matcherLevels_1251_ = lean_ctor_get(v_matcherApp_1242_, 2);
lean_inc_ref(v_matcherLevels_1251_);
v_params_1252_ = lean_ctor_get(v_matcherApp_1242_, 3);
lean_inc_ref(v_params_1252_);
v_motive_1253_ = lean_ctor_get(v_matcherApp_1242_, 4);
lean_inc_ref(v_motive_1253_);
v_discrs_1254_ = lean_ctor_get(v_matcherApp_1242_, 5);
lean_inc_ref(v_discrs_1254_);
v___f_1255_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1255_, 0, v_matcherApp_1242_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1256_, 0, v___f_1255_);
lean_closure_set(v___f_1256_, 1, v_discrs_1254_);
lean_closure_set(v___f_1256_, 2, v_e_1243_);
lean_closure_set(v___f_1256_, 3, v_toMatcherInfo_1249_);
lean_closure_set(v___f_1256_, 4, v_matcherName_1250_);
lean_closure_set(v___f_1256_, 5, v_params_1252_);
lean_closure_set(v___f_1256_, 6, v_matcherLevels_1251_);
v___x_1257_ = 0;
v___x_1258_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_1253_, v___f_1256_, v___x_1257_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* v_matcherApp_1259_, lean_object* v_e_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1259_, v_e_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* v_motiveArgs_1267_, lean_object* v___x_1268_, lean_object* v_n_1269_, lean_object* v_i_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; 
v___x_1278_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1267_, v___x_1268_, v_i_1270_, v_a_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* v_motiveArgs_1279_, lean_object* v___x_1280_, lean_object* v_n_1281_, lean_object* v_i_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v_motiveArgs_1279_, v___x_1280_, v_n_1281_, v_i_1282_, v_a_1283_, v_a_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v_n_1281_);
lean_dec_ref(v___x_1280_);
lean_dec_ref(v_motiveArgs_1279_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* v_matcherApp_1291_, lean_object* v_e_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1291_, v_e_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1307_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_a_1299_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1324_; 
v_a_1308_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1310_ = v___x_1298_;
v_isShared_1311_ = v_isSharedCheck_1324_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1298_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1324_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
uint8_t v___x_1312_; 
v___x_1312_ = l_Lean_Exception_isInterrupt(v_a_1308_);
if (v___x_1312_ == 0)
{
uint8_t v___x_1313_; 
lean_inc(v_a_1308_);
v___x_1313_ = l_Lean_Exception_isRuntime(v_a_1308_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v_a_1308_);
v___x_1314_ = lean_box(0);
if (v_isShared_1311_ == 0)
{
lean_ctor_set_tag(v___x_1310_, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1314_);
v___x_1316_ = v___x_1310_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
else
{
lean_object* v___x_1319_; 
if (v_isShared_1311_ == 0)
{
v___x_1319_ = v___x_1310_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1308_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
else
{
lean_object* v___x_1322_; 
if (v_isShared_1311_ == 0)
{
v___x_1322_ = v___x_1310_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1308_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* v_matcherApp_1325_, lean_object* v_e_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1325_, v_e_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1333_, lean_object* v_x_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v_keyedConfig_1340_; uint8_t v_trackZetaDelta_1341_; lean_object* v_zetaDeltaSet_1342_; lean_object* v_localInstances_1343_; lean_object* v_defEqCtx_x3f_1344_; lean_object* v_synthPendingDepth_1345_; lean_object* v_customCanUnfoldPredicate_x3f_1346_; uint8_t v_univApprox_1347_; uint8_t v_inTypeClassResolution_1348_; uint8_t v_cacheInferType_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_keyedConfig_1340_ = lean_ctor_get(v___y_1335_, 0);
v_trackZetaDelta_1341_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*7);
v_zetaDeltaSet_1342_ = lean_ctor_get(v___y_1335_, 1);
v_localInstances_1343_ = lean_ctor_get(v___y_1335_, 3);
v_defEqCtx_x3f_1344_ = lean_ctor_get(v___y_1335_, 4);
v_synthPendingDepth_1345_ = lean_ctor_get(v___y_1335_, 5);
v_customCanUnfoldPredicate_x3f_1346_ = lean_ctor_get(v___y_1335_, 6);
v_univApprox_1347_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1348_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*7 + 2);
v_cacheInferType_1349_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1346_);
lean_inc(v_synthPendingDepth_1345_);
lean_inc(v_defEqCtx_x3f_1344_);
lean_inc_ref(v_localInstances_1343_);
lean_inc(v_zetaDeltaSet_1342_);
lean_inc_ref(v_keyedConfig_1340_);
v___x_1350_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1350_, 0, v_keyedConfig_1340_);
lean_ctor_set(v___x_1350_, 1, v_zetaDeltaSet_1342_);
lean_ctor_set(v___x_1350_, 2, v_lctx_1333_);
lean_ctor_set(v___x_1350_, 3, v_localInstances_1343_);
lean_ctor_set(v___x_1350_, 4, v_defEqCtx_x3f_1344_);
lean_ctor_set(v___x_1350_, 5, v_synthPendingDepth_1345_);
lean_ctor_set(v___x_1350_, 6, v_customCanUnfoldPredicate_x3f_1346_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7, v_trackZetaDelta_1341_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7 + 1, v_univApprox_1347_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1348_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*7 + 3, v_cacheInferType_1349_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
lean_inc(v___y_1336_);
v___x_1351_ = lean_apply_5(v_x_1334_, v___x_1350_, v___y_1336_, v___y_1337_, v___y_1338_, lean_box(0));
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1352_, v_x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1360_, lean_object* v_lctx_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1361_, v_x_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_lctx_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1369_, v_lctx_1370_, v_x_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1378_, size_t v_i_1379_, size_t v_stop_1380_, lean_object* v_b_1381_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_eq(v_i_1379_, v_stop_1380_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; lean_object* v_fst_1384_; lean_object* v_snd_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; size_t v___x_1388_; size_t v___x_1389_; 
v___x_1383_ = lean_array_uget_borrowed(v_as_1378_, v_i_1379_);
v_fst_1384_ = lean_ctor_get(v___x_1383_, 0);
v_snd_1385_ = lean_ctor_get(v___x_1383_, 1);
v___x_1386_ = l_Lean_Expr_fvarId_x21(v_fst_1384_);
lean_inc(v_snd_1385_);
v___x_1387_ = l_Lean_LocalContext_setUserName(v_b_1381_, v___x_1386_, v_snd_1385_);
v___x_1388_ = ((size_t)1ULL);
v___x_1389_ = lean_usize_add(v_i_1379_, v___x_1388_);
v_i_1379_ = v___x_1389_;
v_b_1381_ = v___x_1387_;
goto _start;
}
else
{
return v_b_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1391_, lean_object* v_i_1392_, lean_object* v_stop_1393_, lean_object* v_b_1394_){
_start:
{
size_t v_i_boxed_1395_; size_t v_stop_boxed_1396_; lean_object* v_res_1397_; 
v_i_boxed_1395_ = lean_unbox_usize(v_i_1392_);
lean_dec(v_i_1392_);
v_stop_boxed_1396_ = lean_unbox_usize(v_stop_1393_);
lean_dec(v_stop_1393_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1391_, v_i_boxed_1395_, v_stop_boxed_1396_, v_b_1394_);
lean_dec_ref(v_as_1391_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1398_, lean_object* v_names_1399_, lean_object* v_k_1400_, lean_object* v_a_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_){
_start:
{
lean_object* v_lctx_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; uint8_t v___x_1410_; 
v_lctx_1406_ = lean_ctor_get(v_a_1401_, 2);
v___x_1407_ = l_Array_zip___redArg(v_fvars_1398_, v_names_1399_);
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_array_get_size(v___x_1407_);
v___x_1410_ = lean_nat_dec_lt(v___x_1408_, v___x_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v___x_1407_);
lean_inc_ref(v_lctx_1406_);
v___x_1411_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1406_, v_k_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
return v___x_1411_;
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = lean_usize_of_nat(v___x_1409_);
lean_inc_ref(v_lctx_1406_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1407_, v___x_1412_, v___x_1413_, v_lctx_1406_);
lean_dec_ref(v___x_1407_);
v___x_1415_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1414_, v_k_1400_, v_a_1401_, v_a_1402_, v_a_1403_, v_a_1404_);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* v_fvars_1416_, lean_object* v_names_1417_, lean_object* v_k_1418_, lean_object* v_a_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1416_, v_names_1417_, v_k_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec(v_a_1420_);
lean_dec_ref(v_a_1419_);
lean_dec_ref(v_names_1417_);
lean_dec_ref(v_fvars_1416_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* v_00_u03b1_1425_, lean_object* v_fvars_1426_, lean_object* v_names_1427_, lean_object* v_k_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1426_, v_names_1427_, v_k_1428_, v_a_1429_, v_a_1430_, v_a_1431_, v_a_1432_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_fvars_1436_, lean_object* v_names_1437_, lean_object* v_k_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(v_00_u03b1_1435_, v_fvars_1436_, v_names_1437_, v_k_1438_, v_a_1439_, v_a_1440_, v_a_1441_, v_a_1442_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec(v_a_1440_);
lean_dec_ref(v_a_1439_);
lean_dec_ref(v_names_1437_);
lean_dec_ref(v_fvars_1436_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* v_k_1445_, lean_object* v_fvars_1446_, lean_object* v_names_1447_, lean_object* v_runInBase_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_apply_2(v_runInBase_1448_, lean_box(0), v_k_1445_);
v___x_1455_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1446_, v_names_1447_, v___x_1454_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* v_k_1456_, lean_object* v_fvars_1457_, lean_object* v_names_1458_, lean_object* v_runInBase_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1456_, v_fvars_1457_, v_names_1458_, v_runInBase_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec_ref(v_names_1458_);
lean_dec_ref(v_fvars_1457_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_fvars_1468_, lean_object* v_names_1469_, lean_object* v_k_1470_){
_start:
{
lean_object* v_toBind_1471_; lean_object* v_liftWith_1472_; lean_object* v_restoreM_1473_; lean_object* v___f_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_toBind_1471_ = lean_ctor_get(v_inst_1467_, 1);
lean_inc(v_toBind_1471_);
lean_dec_ref(v_inst_1467_);
v_liftWith_1472_ = lean_ctor_get(v_inst_1466_, 0);
lean_inc(v_liftWith_1472_);
v_restoreM_1473_ = lean_ctor_get(v_inst_1466_, 1);
lean_inc(v_restoreM_1473_);
lean_dec_ref(v_inst_1466_);
v___f_1474_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1474_, 0, v_k_1470_);
lean_closure_set(v___f_1474_, 1, v_fvars_1468_);
lean_closure_set(v___f_1474_, 2, v_names_1469_);
v___x_1475_ = lean_apply_2(v_liftWith_1472_, lean_box(0), v___f_1474_);
v___x_1476_ = lean_apply_1(v_restoreM_1473_, lean_box(0));
v___x_1477_ = lean_apply_4(v_toBind_1471_, lean_box(0), lean_box(0), v___x_1475_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* v_n_1478_, lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_00_u03b1_1481_, lean_object* v_fvars_1482_, lean_object* v_names_1483_, lean_object* v_k_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_1479_, v_inst_1480_, v_fvars_1482_, v_names_1483_, v_k_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* v_k_1486_, lean_object* v_runInBase_1487_, lean_object* v_ys_1488_, lean_object* v_args_1489_, lean_object* v___mask_1490_, lean_object* v___bodyType_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = lean_apply_2(v_k_1486_, v_ys_1488_, v_args_1489_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
lean_inc(v___y_1493_);
lean_inc_ref(v___y_1492_);
v___x_1498_ = lean_apply_7(v_runInBase_1487_, lean_box(0), v___x_1497_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, lean_box(0));
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* v_k_1499_, lean_object* v_runInBase_1500_, lean_object* v_ys_1501_, lean_object* v_args_1502_, lean_object* v___mask_1503_, lean_object* v___bodyType_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1499_, v_runInBase_1500_, v_ys_1501_, v_args_1502_, v___mask_1503_, v___bodyType_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec_ref(v___bodyType_1504_);
lean_dec_ref(v___mask_1503_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* v_k_1511_, lean_object* v_origAltType_1512_, lean_object* v_altInfo_1513_, lean_object* v_runInBase_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___f_1520_; lean_object* v___x_1521_; 
v___f_1520_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1520_, 0, v_k_1511_);
lean_closure_set(v___f_1520_, 1, v_runInBase_1514_);
v___x_1521_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_1512_, v_altInfo_1513_, v___f_1520_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* v_k_1522_, lean_object* v_origAltType_1523_, lean_object* v_altInfo_1524_, lean_object* v_runInBase_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1522_, v_origAltType_1523_, v_altInfo_1524_, v_runInBase_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* v_inst_1532_, lean_object* v_inst_1533_, lean_object* v_origAltType_1534_, lean_object* v_altInfo_1535_, lean_object* v_k_1536_){
_start:
{
lean_object* v_toBind_1537_; lean_object* v_liftWith_1538_; lean_object* v_restoreM_1539_; lean_object* v___f_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v_toBind_1537_ = lean_ctor_get(v_inst_1532_, 1);
lean_inc(v_toBind_1537_);
lean_dec_ref(v_inst_1532_);
v_liftWith_1538_ = lean_ctor_get(v_inst_1533_, 0);
lean_inc(v_liftWith_1538_);
v_restoreM_1539_ = lean_ctor_get(v_inst_1533_, 1);
lean_inc(v_restoreM_1539_);
lean_dec_ref(v_inst_1533_);
v___f_1540_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1540_, 0, v_k_1536_);
lean_closure_set(v___f_1540_, 1, v_origAltType_1534_);
lean_closure_set(v___f_1540_, 2, v_altInfo_1535_);
v___x_1541_ = lean_apply_2(v_liftWith_1538_, lean_box(0), v___f_1540_);
v___x_1542_ = lean_apply_1(v_restoreM_1539_, lean_box(0));
v___x_1543_ = lean_apply_4(v_toBind_1537_, lean_box(0), lean_box(0), v___x_1541_, v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* v_n_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_00_u03b1_1547_, lean_object* v_origAltType_1548_, lean_object* v_altInfo_1549_, lean_object* v_k_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_1545_, v_inst_1546_, v_origAltType_1548_, v_altInfo_1549_, v_k_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object* v_fvars_1552_){
_start:
{
lean_object* v_args_1553_; lean_object* v_discrEqs_1554_; lean_object* v___x_1555_; 
v_args_1553_ = lean_ctor_get(v_fvars_1552_, 0);
lean_inc_ref(v_args_1553_);
v_discrEqs_1554_ = lean_ctor_get(v_fvars_1552_, 3);
lean_inc_ref(v_discrEqs_1554_);
lean_dec_ref(v_fvars_1552_);
v___x_1555_ = l_Array_append___redArg(v_args_1553_, v_discrEqs_1554_);
lean_dec_ref(v_discrEqs_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object* v_fvars_1556_){
_start:
{
lean_object* v_fields_1557_; lean_object* v_overlaps_1558_; lean_object* v_discrEqs_1559_; lean_object* v_extraEqs_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_fields_1557_ = lean_ctor_get(v_fvars_1556_, 1);
lean_inc_ref(v_fields_1557_);
v_overlaps_1558_ = lean_ctor_get(v_fvars_1556_, 2);
lean_inc_ref(v_overlaps_1558_);
v_discrEqs_1559_ = lean_ctor_get(v_fvars_1556_, 3);
lean_inc_ref(v_discrEqs_1559_);
v_extraEqs_1560_ = lean_ctor_get(v_fvars_1556_, 4);
lean_inc_ref(v_extraEqs_1560_);
lean_dec_ref(v_fvars_1556_);
v___x_1561_ = l_Array_append___redArg(v_fields_1557_, v_overlaps_1558_);
lean_dec_ref(v_overlaps_1558_);
v___x_1562_ = l_Array_append___redArg(v___x_1561_, v_discrEqs_1559_);
lean_dec_ref(v_discrEqs_1559_);
v___x_1563_ = l_Array_append___redArg(v___x_1562_, v_extraEqs_1560_);
lean_dec_ref(v_extraEqs_1560_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1564_, lean_object* v_inst_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_1568_ = l_Lean_throwError___redArg(v_inst_1564_, v_inst_1565_, v___x_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1569_, lean_object* v_inst_1570_, lean_object* v_x_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1569_, v_inst_1570_, v_x_1571_);
lean_dec_ref(v_x_1571_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1573_, lean_object* v_x_1574_){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1575_ = l_Lean_Expr_fvarId_x21(v_x_1574_);
v___x_1576_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1576_, 0, v___x_1575_);
v___x_1577_ = lean_apply_2(v_inst_1573_, lean_box(0), v___x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1578_, lean_object* v_x_1579_){
_start:
{
lean_object* v_res_1580_; 
v_res_1580_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1578_, v_x_1579_);
lean_dec_ref(v_x_1579_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1581_, lean_object* v___f_1582_, lean_object* v_xs_1583_, lean_object* v_x_1584_){
_start:
{
size_t v_sz_1585_; size_t v___x_1586_; lean_object* v___x_1587_; 
v_sz_1585_ = lean_array_size(v_xs_1583_);
v___x_1586_ = ((size_t)0ULL);
v___x_1587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1581_, v___f_1582_, v_sz_1585_, v___x_1586_, v_xs_1583_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1588_, lean_object* v___f_1589_, lean_object* v_xs_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1588_, v___f_1589_, v_xs_1590_, v_x_1591_);
lean_dec_ref(v_x_1591_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_fst_1593_, lean_object* v_fst_1594_, lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v_toPure_1597_, lean_object* v_____do__lift_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1599_ = lean_array_push(v_fst_1593_, v_____do__lift_1598_);
v___x_1600_ = lean_nat_add(v_fst_1594_, v___x_1595_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
lean_ctor_set(v___x_1601_, 1, v___x_1596_);
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1599_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
v___x_1604_ = lean_apply_2(v_toPure_1597_, lean_box(0), v___x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object* v_fst_1605_, lean_object* v_fst_1606_, lean_object* v___x_1607_, lean_object* v___x_1608_, lean_object* v_toPure_1609_, lean_object* v_____do__lift_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__3(v_fst_1605_, v_fst_1606_, v___x_1607_, v___x_1608_, v_toPure_1609_, v_____do__lift_1610_);
lean_dec(v___x_1607_);
lean_dec(v_fst_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(uint8_t v_val_1612_, lean_object* v_a_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
if (v_val_1612_ == 0)
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Meta_mkEqRefl(v_a_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_mkHEqRefl(v_a_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object* v_val_1621_, lean_object* v_a_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
uint8_t v_val_12193__boxed_1628_; lean_object* v_res_1629_; 
v_val_12193__boxed_1628_ = lean_unbox(v_val_1621_);
v_res_1629_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(v_val_12193__boxed_1628_, v_a_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_toPure_1630_, lean_object* v_inst_1631_, lean_object* v_toBind_1632_, lean_object* v_a_1633_, lean_object* v_x_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v_snd_1636_; lean_object* v_snd_1637_; lean_object* v_fst_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1686_; 
v_snd_1636_ = lean_ctor_get(v___y_1635_, 1);
lean_inc(v_snd_1636_);
v_snd_1637_ = lean_ctor_get(v_snd_1636_, 1);
lean_inc(v_snd_1637_);
v_fst_1638_ = lean_ctor_get(v___y_1635_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___y_1635_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v___y_1635_, 1);
lean_dec(v_unused_1687_);
v___x_1640_ = v___y_1635_;
v_isShared_1641_ = v_isSharedCheck_1686_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_fst_1638_);
lean_dec(v___y_1635_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1686_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_fst_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1684_; 
v_fst_1642_ = lean_ctor_get(v_snd_1636_, 0);
v_isSharedCheck_1684_ = !lean_is_exclusive(v_snd_1636_);
if (v_isSharedCheck_1684_ == 0)
{
lean_object* v_unused_1685_; 
v_unused_1685_ = lean_ctor_get(v_snd_1636_, 1);
lean_dec(v_unused_1685_);
v___x_1644_ = v_snd_1636_;
v_isShared_1645_ = v_isSharedCheck_1684_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_fst_1642_);
lean_dec(v_snd_1636_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1684_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_array_1646_; lean_object* v_start_1647_; lean_object* v_stop_1648_; uint8_t v___x_1649_; 
v_array_1646_ = lean_ctor_get(v_snd_1637_, 0);
v_start_1647_ = lean_ctor_get(v_snd_1637_, 1);
v_stop_1648_ = lean_ctor_get(v_snd_1637_, 2);
v___x_1649_ = lean_nat_dec_lt(v_start_1647_, v_stop_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1651_; 
lean_dec_ref(v_a_1633_);
lean_dec(v_toBind_1632_);
lean_dec(v_inst_1631_);
if (v_isShared_1645_ == 0)
{
v___x_1651_ = v___x_1644_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_fst_1642_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_snd_1637_);
v___x_1651_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
lean_object* v___x_1653_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1651_);
v___x_1653_ = v___x_1640_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_fst_1638_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v___x_1651_);
v___x_1653_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1653_);
v___x_1655_ = lean_apply_2(v_toPure_1630_, lean_box(0), v___x_1654_);
return v___x_1655_;
}
}
}
else
{
lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1680_; 
lean_inc(v_stop_1648_);
lean_inc(v_start_1647_);
lean_inc_ref(v_array_1646_);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_snd_1637_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1681_ = lean_ctor_get(v_snd_1637_, 2);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_snd_1637_, 1);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_snd_1637_, 0);
lean_dec(v_unused_1683_);
v___x_1659_ = v_snd_1637_;
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
else
{
lean_dec(v_snd_1637_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1661_ = lean_array_fget(v_array_1646_, v_start_1647_);
v___x_1662_ = lean_unsigned_to_nat(1u);
v___x_1663_ = lean_nat_add(v_start_1647_, v___x_1662_);
lean_dec(v_start_1647_);
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 1, v___x_1663_);
v___x_1665_ = v___x_1659_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_array_1646_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_stop_1648_);
v___x_1665_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v___x_1667_; 
lean_dec_ref(v_a_1633_);
lean_dec(v_toBind_1632_);
lean_dec(v_inst_1631_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 1, v___x_1665_);
v___x_1667_ = v___x_1644_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v_fst_1642_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 1, v___x_1667_);
v___x_1669_ = v___x_1640_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_fst_1638_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
v___x_1671_ = lean_apply_2(v_toPure_1630_, lean_box(0), v___x_1670_);
return v___x_1671_;
}
}
}
else
{
lean_object* v_val_1674_; lean_object* v___f_1675_; lean_object* v___f_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_del_object(v___x_1644_);
lean_del_object(v___x_1640_);
v_val_1674_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1674_);
lean_dec_ref_known(v___x_1661_, 1);
v___f_1675_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_1675_, 0, v_fst_1638_);
lean_closure_set(v___f_1675_, 1, v_fst_1642_);
lean_closure_set(v___f_1675_, 2, v___x_1662_);
lean_closure_set(v___f_1675_, 3, v___x_1665_);
lean_closure_set(v___f_1675_, 4, v_toPure_1630_);
v___f_1676_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed), 7, 2);
lean_closure_set(v___f_1676_, 0, v_val_1674_);
lean_closure_set(v___f_1676_, 1, v_a_1633_);
v___x_1677_ = lean_apply_2(v_inst_1631_, lean_box(0), v___f_1676_);
v___x_1678_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1677_, v___f_1675_);
return v___x_1678_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object* v_heq_1688_, lean_object* v_fst_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_mkArrow(v_heq_1688_, v_fst_1689_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_heq_1696_, lean_object* v_fst_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_heq_1696_, v_fst_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_heq_1706_, lean_object* v_fst_1707_, lean_object* v_fst_1708_, lean_object* v___x_1709_, lean_object* v___x_1710_, lean_object* v_toPure_1711_, lean_object* v_____x_1712_){
_start:
{
uint8_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1713_ = l_Lean_Expr_isHEq(v_heq_1706_);
v___x_1714_ = lean_box(v___x_1713_);
v___x_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1714_);
v___x_1716_ = lean_array_push(v_fst_1707_, v___x_1715_);
v___x_1717_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_1718_ = lean_array_push(v_fst_1708_, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1709_);
lean_ctor_set(v___x_1719_, 1, v___x_1710_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_____x_1712_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
v___x_1724_ = lean_apply_2(v_toPure_1711_, lean_box(0), v___x_1723_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object* v_heq_1725_, lean_object* v_fst_1726_, lean_object* v_fst_1727_, lean_object* v___x_1728_, lean_object* v___x_1729_, lean_object* v_toPure_1730_, lean_object* v_____x_1731_){
_start:
{
lean_object* v_res_1732_; 
v_res_1732_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__7(v_heq_1725_, v_fst_1726_, v_fst_1727_, v___x_1728_, v___x_1729_, v_toPure_1730_, v_____x_1731_);
lean_dec_ref(v_heq_1725_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_fst_1733_, lean_object* v_fst_1734_, lean_object* v_fst_1735_, lean_object* v___x_1736_, lean_object* v___x_1737_, lean_object* v_toPure_1738_, lean_object* v_inst_1739_, lean_object* v_toBind_1740_, lean_object* v_heq_1741_){
_start:
{
lean_object* v___f_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_inc_ref(v_heq_1741_);
v___f_1742_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1742_, 0, v_heq_1741_);
lean_closure_set(v___f_1742_, 1, v_fst_1733_);
v___f_1743_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_1743_, 0, v_heq_1741_);
lean_closure_set(v___f_1743_, 1, v_fst_1734_);
lean_closure_set(v___f_1743_, 2, v_fst_1735_);
lean_closure_set(v___f_1743_, 3, v___x_1736_);
lean_closure_set(v___f_1743_, 4, v___x_1737_);
lean_closure_set(v___f_1743_, 5, v_toPure_1738_);
v___x_1744_ = lean_apply_2(v_inst_1739_, lean_box(0), v___f_1742_);
v___x_1745_ = lean_apply_4(v_toBind_1740_, lean_box(0), lean_box(0), v___x_1744_, v___f_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v___x_1746_, lean_object* v_a_1747_, lean_object* v_inst_1748_, lean_object* v_toBind_1749_, lean_object* v___f_1750_, lean_object* v_fst_1751_, lean_object* v_fst_1752_, lean_object* v___x_1753_, lean_object* v___x_1754_, lean_object* v___x_1755_, lean_object* v_fst_1756_, lean_object* v_toPure_1757_, uint8_t v_____do__lift_1758_){
_start:
{
if (v_____do__lift_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
lean_dec(v_toPure_1757_);
lean_dec(v_fst_1756_);
lean_dec_ref(v___x_1755_);
lean_dec_ref(v___x_1754_);
lean_dec(v___x_1753_);
lean_dec(v_fst_1752_);
lean_dec(v_fst_1751_);
v___x_1759_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1759_, 0, v___x_1746_);
lean_closure_set(v___x_1759_, 1, v_a_1747_);
v___x_1760_ = lean_apply_2(v_inst_1748_, lean_box(0), v___x_1759_);
v___x_1761_ = lean_apply_4(v_toBind_1749_, lean_box(0), lean_box(0), v___x_1760_, v___f_1750_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_dec(v___f_1750_);
lean_dec(v_toBind_1749_);
lean_dec(v_inst_1748_);
lean_dec_ref(v_a_1747_);
lean_dec_ref(v___x_1746_);
v___x_1762_ = lean_box(0);
v___x_1763_ = lean_array_push(v_fst_1751_, v___x_1762_);
v___x_1764_ = lean_array_push(v_fst_1752_, v___x_1753_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1754_);
lean_ctor_set(v___x_1765_, 1, v___x_1755_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1764_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1763_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v_fst_1756_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
v___x_1770_ = lean_apply_2(v_toPure_1757_, lean_box(0), v___x_1769_);
return v___x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v___x_1771_, lean_object* v_a_1772_, lean_object* v_inst_1773_, lean_object* v_toBind_1774_, lean_object* v___f_1775_, lean_object* v_fst_1776_, lean_object* v_fst_1777_, lean_object* v___x_1778_, lean_object* v___x_1779_, lean_object* v___x_1780_, lean_object* v_fst_1781_, lean_object* v_toPure_1782_, lean_object* v_____do__lift_1783_){
_start:
{
uint8_t v_____do__lift_12387__boxed_1784_; lean_object* v_res_1785_; 
v_____do__lift_12387__boxed_1784_ = lean_unbox(v_____do__lift_1783_);
v_res_1785_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v___x_1771_, v_a_1772_, v_inst_1773_, v_toBind_1774_, v___f_1775_, v_fst_1776_, v_fst_1777_, v___x_1778_, v___x_1779_, v___x_1780_, v_fst_1781_, v_toPure_1782_, v_____do__lift_12387__boxed_1784_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_toPure_1786_, uint8_t v_addEqualities_1787_, lean_object* v_inst_1788_, lean_object* v_toBind_1789_, lean_object* v_a_1790_, lean_object* v_x_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_snd_1793_; lean_object* v_snd_1794_; lean_object* v_snd_1795_; lean_object* v_snd_1796_; lean_object* v_fst_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1903_; 
v_snd_1793_ = lean_ctor_get(v___y_1792_, 1);
lean_inc(v_snd_1793_);
v_snd_1794_ = lean_ctor_get(v_snd_1793_, 1);
lean_inc(v_snd_1794_);
v_snd_1795_ = lean_ctor_get(v_snd_1794_, 1);
lean_inc(v_snd_1795_);
v_snd_1796_ = lean_ctor_get(v_snd_1795_, 1);
lean_inc(v_snd_1796_);
v_fst_1797_ = lean_ctor_get(v___y_1792_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___y_1792_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v___y_1792_, 1);
lean_dec(v_unused_1904_);
v___x_1799_ = v___y_1792_;
v_isShared_1800_ = v_isSharedCheck_1903_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_fst_1797_);
lean_dec(v___y_1792_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1903_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_fst_1801_; lean_object* v___x_1803_; uint8_t v_isShared_1804_; uint8_t v_isSharedCheck_1901_; 
v_fst_1801_ = lean_ctor_get(v_snd_1793_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_snd_1793_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_snd_1793_, 1);
lean_dec(v_unused_1902_);
v___x_1803_ = v_snd_1793_;
v_isShared_1804_ = v_isSharedCheck_1901_;
goto v_resetjp_1802_;
}
else
{
lean_inc(v_fst_1801_);
lean_dec(v_snd_1793_);
v___x_1803_ = lean_box(0);
v_isShared_1804_ = v_isSharedCheck_1901_;
goto v_resetjp_1802_;
}
v_resetjp_1802_:
{
lean_object* v_fst_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1899_; 
v_fst_1805_ = lean_ctor_get(v_snd_1794_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_snd_1794_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_snd_1794_, 1);
lean_dec(v_unused_1900_);
v___x_1807_ = v_snd_1794_;
v_isShared_1808_ = v_isSharedCheck_1899_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_fst_1805_);
lean_dec(v_snd_1794_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1899_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_fst_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1897_; 
v_fst_1809_ = lean_ctor_get(v_snd_1795_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v_snd_1795_);
if (v_isSharedCheck_1897_ == 0)
{
lean_object* v_unused_1898_; 
v_unused_1898_ = lean_ctor_get(v_snd_1795_, 1);
lean_dec(v_unused_1898_);
v___x_1811_ = v_snd_1795_;
v_isShared_1812_ = v_isSharedCheck_1897_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_fst_1809_);
lean_dec(v_snd_1795_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1897_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_array_1813_; lean_object* v_start_1814_; lean_object* v_stop_1815_; uint8_t v___x_1816_; 
v_array_1813_ = lean_ctor_get(v_snd_1796_, 0);
v_start_1814_ = lean_ctor_get(v_snd_1796_, 1);
v_stop_1815_ = lean_ctor_get(v_snd_1796_, 2);
v___x_1816_ = lean_nat_dec_lt(v_start_1814_, v_stop_1815_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref(v_a_1790_);
lean_dec(v_toBind_1789_);
lean_dec(v_inst_1788_);
if (v_isShared_1812_ == 0)
{
v___x_1818_ = v___x_1811_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_fst_1809_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_snd_1796_);
v___x_1818_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1820_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___x_1818_);
v___x_1820_ = v___x_1807_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1805_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1818_);
v___x_1820_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1820_);
v___x_1822_ = v___x_1803_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_fst_1801_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1822_);
v___x_1824_ = v___x_1799_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_fst_1797_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
v___x_1826_ = lean_apply_2(v_toPure_1786_, lean_box(0), v___x_1825_);
return v___x_1826_;
}
}
}
}
}
else
{
lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1893_; 
lean_inc(v_stop_1815_);
lean_inc(v_start_1814_);
lean_inc_ref(v_array_1813_);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_snd_1796_);
if (v_isSharedCheck_1893_ == 0)
{
lean_object* v_unused_1894_; lean_object* v_unused_1895_; lean_object* v_unused_1896_; 
v_unused_1894_ = lean_ctor_get(v_snd_1796_, 2);
lean_dec(v_unused_1894_);
v_unused_1895_ = lean_ctor_get(v_snd_1796_, 1);
lean_dec(v_unused_1895_);
v_unused_1896_ = lean_ctor_get(v_snd_1796_, 0);
lean_dec(v_unused_1896_);
v___x_1832_ = v_snd_1796_;
v_isShared_1833_ = v_isSharedCheck_1893_;
goto v_resetjp_1831_;
}
else
{
lean_dec(v_snd_1796_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1893_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_array_1834_; lean_object* v_start_1835_; lean_object* v_stop_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1841_; 
v_array_1834_ = lean_ctor_get(v_fst_1809_, 0);
v_start_1835_ = lean_ctor_get(v_fst_1809_, 1);
v_stop_1836_ = lean_ctor_get(v_fst_1809_, 2);
v___x_1837_ = lean_array_fget(v_array_1813_, v_start_1814_);
v___x_1838_ = lean_unsigned_to_nat(1u);
v___x_1839_ = lean_nat_add(v_start_1814_, v___x_1838_);
lean_dec(v_start_1814_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1839_);
v___x_1841_ = v___x_1832_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_array_1813_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1839_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_stop_1815_);
v___x_1841_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_nat_dec_lt(v_start_1835_, v_stop_1836_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1844_; 
lean_dec(v___x_1837_);
lean_dec_ref(v_a_1790_);
lean_dec(v_toBind_1789_);
lean_dec(v_inst_1788_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v___x_1841_);
v___x_1844_ = v___x_1811_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_fst_1809_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1841_);
v___x_1844_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___x_1844_);
v___x_1846_ = v___x_1807_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_fst_1805_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1846_);
v___x_1848_ = v___x_1803_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_fst_1801_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1848_);
v___x_1850_ = v___x_1799_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_fst_1797_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
v___x_1852_ = lean_apply_2(v_toPure_1786_, lean_box(0), v___x_1851_);
return v___x_1852_;
}
}
}
}
}
else
{
lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1888_; 
lean_inc(v_stop_1836_);
lean_inc(v_start_1835_);
lean_inc_ref(v_array_1834_);
v_isSharedCheck_1888_ = !lean_is_exclusive(v_fst_1809_);
if (v_isSharedCheck_1888_ == 0)
{
lean_object* v_unused_1889_; lean_object* v_unused_1890_; lean_object* v_unused_1891_; 
v_unused_1889_ = lean_ctor_get(v_fst_1809_, 2);
lean_dec(v_unused_1889_);
v_unused_1890_ = lean_ctor_get(v_fst_1809_, 1);
lean_dec(v_unused_1890_);
v_unused_1891_ = lean_ctor_get(v_fst_1809_, 0);
lean_dec(v_unused_1891_);
v___x_1858_ = v_fst_1809_;
v_isShared_1859_ = v_isSharedCheck_1888_;
goto v_resetjp_1857_;
}
else
{
lean_dec(v_fst_1809_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1888_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1860_ = lean_array_fget(v_array_1834_, v_start_1835_);
v___x_1861_ = lean_nat_add(v_start_1835_, v___x_1838_);
lean_dec(v_start_1835_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1861_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_array_1834_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1887_, 2, v_stop_1836_);
v___x_1863_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
if (v_addEqualities_1787_ == 0)
{
lean_dec(v___x_1860_);
lean_dec_ref(v_a_1790_);
lean_dec(v_toBind_1789_);
lean_dec(v_inst_1788_);
goto v___jp_1864_;
}
else
{
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v___f_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_del_object(v___x_1811_);
lean_del_object(v___x_1807_);
lean_del_object(v___x_1803_);
lean_del_object(v___x_1799_);
lean_inc_n(v_toBind_1789_, 2);
lean_inc_n(v_inst_1788_, 2);
lean_inc(v_toPure_1786_);
lean_inc_ref(v___x_1841_);
lean_inc_ref(v___x_1863_);
lean_inc(v_fst_1805_);
lean_inc(v_fst_1801_);
lean_inc(v_fst_1797_);
v___f_1882_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8), 9, 8);
lean_closure_set(v___f_1882_, 0, v_fst_1797_);
lean_closure_set(v___f_1882_, 1, v_fst_1801_);
lean_closure_set(v___f_1882_, 2, v_fst_1805_);
lean_closure_set(v___f_1882_, 3, v___x_1863_);
lean_closure_set(v___f_1882_, 4, v___x_1841_);
lean_closure_set(v___f_1882_, 5, v_toPure_1786_);
lean_closure_set(v___f_1882_, 6, v_inst_1788_);
lean_closure_set(v___f_1882_, 7, v_toBind_1789_);
lean_inc_ref(v_a_1790_);
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 13, 12);
lean_closure_set(v___f_1883_, 0, v___x_1860_);
lean_closure_set(v___f_1883_, 1, v_a_1790_);
lean_closure_set(v___f_1883_, 2, v_inst_1788_);
lean_closure_set(v___f_1883_, 3, v_toBind_1789_);
lean_closure_set(v___f_1883_, 4, v___f_1882_);
lean_closure_set(v___f_1883_, 5, v_fst_1801_);
lean_closure_set(v___f_1883_, 6, v_fst_1805_);
lean_closure_set(v___f_1883_, 7, v___x_1837_);
lean_closure_set(v___f_1883_, 8, v___x_1863_);
lean_closure_set(v___f_1883_, 9, v___x_1841_);
lean_closure_set(v___f_1883_, 10, v_fst_1797_);
lean_closure_set(v___f_1883_, 11, v_toPure_1786_);
v___x_1884_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1884_, 0, v_a_1790_);
v___x_1885_ = lean_apply_2(v_inst_1788_, lean_box(0), v___x_1884_);
v___x_1886_ = lean_apply_4(v_toBind_1789_, lean_box(0), lean_box(0), v___x_1885_, v___f_1883_);
return v___x_1886_;
}
else
{
lean_dec(v___x_1860_);
lean_dec_ref(v_a_1790_);
lean_dec(v_toBind_1789_);
lean_dec(v_inst_1788_);
goto v___jp_1864_;
}
}
v___jp_1864_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_array_push(v_fst_1801_, v___x_1865_);
v___x_1867_ = lean_array_push(v_fst_1805_, v___x_1837_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v___x_1841_);
lean_ctor_set(v___x_1811_, 0, v___x_1863_);
v___x_1869_ = v___x_1811_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1841_);
v___x_1869_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___x_1869_);
lean_ctor_set(v___x_1807_, 0, v___x_1867_);
v___x_1871_ = v___x_1807_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1804_ == 0)
{
lean_ctor_set(v___x_1803_, 1, v___x_1871_);
lean_ctor_set(v___x_1803_, 0, v___x_1866_);
v___x_1873_ = v___x_1803_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1866_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 1, v___x_1873_);
v___x_1875_ = v___x_1799_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_fst_1797_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
v___x_1877_ = lean_apply_2(v_toPure_1786_, lean_box(0), v___x_1876_);
return v___x_1877_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object* v_toPure_1905_, lean_object* v_addEqualities_1906_, lean_object* v_inst_1907_, lean_object* v_toBind_1908_, lean_object* v_a_1909_, lean_object* v_x_1910_, lean_object* v___y_1911_){
_start:
{
uint8_t v_addEqualities_boxed_1912_; lean_object* v_res_1913_; 
v_addEqualities_boxed_1912_ = lean_unbox(v_addEqualities_1906_);
v_res_1913_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(v_toPure_1905_, v_addEqualities_boxed_1912_, v_inst_1907_, v_toBind_1908_, v_a_1909_, v_x_1910_, v___y_1911_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v_toPure_1914_, lean_object* v_____do__lift_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_apply_2(v_toPure_1914_, lean_box(0), v_____do__lift_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1917_, lean_object* v_____do__lift_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_apply_2(v_toPure_1917_, lean_box(0), v_____do__lift_1918_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1920_, lean_object* v_fst_1921_, lean_object* v_____do__lift_1922_, lean_object* v_toPure_1923_, lean_object* v_____do__lift_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1925_, 0, v_fst_1920_);
lean_ctor_set(v___x_1925_, 1, v_fst_1921_);
v___x_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1926_, 0, v_____do__lift_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_____do__lift_1922_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_apply_2(v_toPure_1923_, lean_box(0), v___x_1927_);
return v___x_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1929_, lean_object* v_fst_1930_, lean_object* v_toPure_1931_, lean_object* v_fst_1932_, lean_object* v_inst_1933_, lean_object* v_toBind_1934_, lean_object* v_____do__lift_1935_){
_start:
{
lean_object* v___f_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___f_1936_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1936_, 0, v_fst_1929_);
lean_closure_set(v___f_1936_, 1, v_fst_1930_);
lean_closure_set(v___f_1936_, 2, v_____do__lift_1935_);
lean_closure_set(v___f_1936_, 3, v_toPure_1931_);
v___x_1937_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1937_, 0, v_fst_1932_);
v___x_1938_ = lean_apply_2(v_inst_1933_, lean_box(0), v___x_1937_);
v___x_1939_ = lean_apply_4(v_toBind_1934_, lean_box(0), lean_box(0), v___x_1938_, v___f_1936_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1940_, lean_object* v_inst_1941_, lean_object* v_toBind_1942_, lean_object* v_motiveArgs_1943_, lean_object* v_____s_1944_){
_start:
{
lean_object* v_snd_1945_; lean_object* v_snd_1946_; lean_object* v_fst_1947_; lean_object* v_fst_1948_; lean_object* v_fst_1949_; lean_object* v___f_1950_; uint8_t v___x_1951_; uint8_t v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v_snd_1945_ = lean_ctor_get(v_____s_1944_, 1);
lean_inc(v_snd_1945_);
v_snd_1946_ = lean_ctor_get(v_snd_1945_, 1);
lean_inc(v_snd_1946_);
v_fst_1947_ = lean_ctor_get(v_____s_1944_, 0);
lean_inc_n(v_fst_1947_, 2);
lean_dec_ref(v_____s_1944_);
v_fst_1948_ = lean_ctor_get(v_snd_1945_, 0);
lean_inc(v_fst_1948_);
lean_dec(v_snd_1945_);
v_fst_1949_ = lean_ctor_get(v_snd_1946_, 0);
lean_inc(v_fst_1949_);
lean_dec(v_snd_1946_);
lean_inc(v_toBind_1942_);
lean_inc(v_inst_1941_);
v___f_1950_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1950_, 0, v_fst_1948_);
lean_closure_set(v___f_1950_, 1, v_fst_1949_);
lean_closure_set(v___f_1950_, 2, v_toPure_1940_);
lean_closure_set(v___f_1950_, 3, v_fst_1947_);
lean_closure_set(v___f_1950_, 4, v_inst_1941_);
lean_closure_set(v___f_1950_, 5, v_toBind_1942_);
v___x_1951_ = 0;
v___x_1952_ = 1;
v___x_1953_ = 1;
v___x_1954_ = lean_box(v___x_1951_);
v___x_1955_ = lean_box(v___x_1952_);
v___x_1956_ = lean_box(v___x_1951_);
v___x_1957_ = lean_box(v___x_1952_);
v___x_1958_ = lean_box(v___x_1953_);
v___x_1959_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1959_, 0, v_motiveArgs_1943_);
lean_closure_set(v___x_1959_, 1, v_fst_1947_);
lean_closure_set(v___x_1959_, 2, v___x_1954_);
lean_closure_set(v___x_1959_, 3, v___x_1955_);
lean_closure_set(v___x_1959_, 4, v___x_1956_);
lean_closure_set(v___x_1959_, 5, v___x_1957_);
lean_closure_set(v___x_1959_, 6, v___x_1958_);
v___x_1960_ = lean_apply_2(v_inst_1941_, lean_box(0), v___x_1959_);
v___x_1961_ = lean_apply_4(v_toBind_1942_, lean_box(0), lean_box(0), v___x_1960_, v___f_1950_);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_1964_, lean_object* v_discrs_x27_1965_, lean_object* v_motiveArgs_1966_, lean_object* v_inst_1967_, lean_object* v___f_1968_, lean_object* v_toBind_1969_, lean_object* v___f_1970_, lean_object* v_motiveBody_x27_1971_){
_start:
{
lean_object* v_discrInfos_1972_; lean_object* v___x_1973_; lean_object* v_addHEqualities_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; size_t v_sz_1983_; size_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v_discrInfos_1972_ = lean_ctor_get(v_toMatcherInfo_1964_, 4);
lean_inc_ref(v_discrInfos_1972_);
lean_dec_ref(v_toMatcherInfo_1964_);
v___x_1973_ = lean_unsigned_to_nat(0u);
v_addHEqualities_1974_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_1975_ = lean_array_get_size(v_discrs_x27_1965_);
v___x_1976_ = l_Array_toSubarray___redArg(v_discrs_x27_1965_, v___x_1973_, v___x_1975_);
v___x_1977_ = lean_array_get_size(v_discrInfos_1972_);
v___x_1978_ = l_Array_toSubarray___redArg(v_discrInfos_1972_, v___x_1973_, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1976_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v_addHEqualities_1974_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v_addHEqualities_1974_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v_motiveBody_x27_1971_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v_sz_1983_ = lean_array_size(v_motiveArgs_1966_);
v___x_1984_ = ((size_t)0ULL);
v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1967_, v_motiveArgs_1966_, v___f_1968_, v_sz_1983_, v___x_1984_, v___x_1982_);
v___x_1986_ = lean_apply_4(v_toBind_1969_, lean_box(0), lean_box(0), v___x_1985_, v___f_1970_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_1987_, lean_object* v_motiveArgs_1988_, lean_object* v_motiveBody_1989_, lean_object* v_toBind_1990_, lean_object* v___f_1991_, lean_object* v_____r_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_apply_2(v_onMotive_1987_, v_motiveArgs_1988_, v_motiveBody_1989_);
v___x_1994_ = lean_apply_4(v_toBind_1990_, lean_box(0), lean_box(0), v___x_1993_, v___f_1991_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_1995_, lean_object* v_____r_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_apply_1(v___f_1995_, v_____r_1996_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_1998_, lean_object* v_inst_1999_, lean_object* v_toBind_2000_, lean_object* v_toMatcherInfo_2001_, lean_object* v_discrs_x27_2002_, lean_object* v_inst_2003_, lean_object* v___f_2004_, lean_object* v_onMotive_2005_, lean_object* v_discrs_2006_, lean_object* v_inst_2007_, lean_object* v_motiveArgs_2008_, lean_object* v_motiveBody_2009_){
_start:
{
lean_object* v___f_2010_; lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
lean_inc_ref_n(v_motiveArgs_2008_, 3);
lean_inc_n(v_toBind_2000_, 3);
v___f_2010_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2010_, 0, v_toPure_1998_);
lean_closure_set(v___f_2010_, 1, v_inst_1999_);
lean_closure_set(v___f_2010_, 2, v_toBind_2000_);
lean_closure_set(v___f_2010_, 3, v_motiveArgs_2008_);
lean_inc_ref(v_inst_2003_);
v___f_2011_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2011_, 0, v_toMatcherInfo_2001_);
lean_closure_set(v___f_2011_, 1, v_discrs_x27_2002_);
lean_closure_set(v___f_2011_, 2, v_motiveArgs_2008_);
lean_closure_set(v___f_2011_, 3, v_inst_2003_);
lean_closure_set(v___f_2011_, 4, v___f_2004_);
lean_closure_set(v___f_2011_, 5, v_toBind_2000_);
lean_closure_set(v___f_2011_, 6, v___f_2010_);
lean_inc_ref(v___f_2011_);
lean_inc_ref(v_motiveBody_2009_);
lean_inc(v_onMotive_2005_);
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2012_, 0, v_onMotive_2005_);
lean_closure_set(v___f_2012_, 1, v_motiveArgs_2008_);
lean_closure_set(v___f_2012_, 2, v_motiveBody_2009_);
lean_closure_set(v___f_2012_, 3, v_toBind_2000_);
lean_closure_set(v___f_2012_, 4, v___f_2011_);
v___x_2013_ = lean_array_get_size(v_motiveArgs_2008_);
v___x_2014_ = lean_array_get_size(v_discrs_2006_);
v___x_2015_ = lean_nat_dec_eq(v___x_2013_, v___x_2014_);
if (v___x_2015_ == 0)
{
lean_object* v___f_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec_ref(v___f_2011_);
lean_dec_ref(v_motiveBody_2009_);
lean_dec_ref(v_motiveArgs_2008_);
lean_dec(v_onMotive_2005_);
v___f_2016_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2016_, 0, v___f_2012_);
v___x_2017_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2018_ = l_Nat_reprFast(v___x_2014_);
v___x_2019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
v___x_2020_ = l_Lean_MessageData_ofFormat(v___x_2019_);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2017_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = l_Lean_throwError___redArg(v_inst_2003_, v_inst_2007_, v___x_2023_);
v___x_2025_ = lean_apply_4(v_toBind_2000_, lean_box(0), lean_box(0), v___x_2024_, v___f_2016_);
return v___x_2025_;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec_ref(v___f_2012_);
lean_dec_ref(v_inst_2007_);
lean_dec_ref(v_inst_2003_);
v___x_2026_ = lean_box(0);
v___x_2027_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2005_, v_motiveArgs_2008_, v_motiveBody_2009_, v_toBind_2000_, v___f_2011_, v___x_2026_);
return v___x_2027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2028_, lean_object* v_inst_2029_, lean_object* v_toBind_2030_, lean_object* v_toMatcherInfo_2031_, lean_object* v_discrs_x27_2032_, lean_object* v_inst_2033_, lean_object* v___f_2034_, lean_object* v_onMotive_2035_, lean_object* v_discrs_2036_, lean_object* v_inst_2037_, lean_object* v_motiveArgs_2038_, lean_object* v_motiveBody_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2028_, v_inst_2029_, v_toBind_2030_, v_toMatcherInfo_2031_, v_discrs_x27_2032_, v_inst_2033_, v___f_2034_, v_onMotive_2035_, v_discrs_2036_, v_inst_2037_, v_motiveArgs_2038_, v_motiveBody_2039_);
lean_dec_ref(v_discrs_2036_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2041_, lean_object* v_numParams_2042_, lean_object* v_numDiscrs_2043_, lean_object* v_altInfos_2044_, lean_object* v_uElimPos_x3f_2045_, lean_object* v_snd_2046_, lean_object* v_overlaps_2047_, lean_object* v_matcherName_2048_, lean_object* v_matcherLevels_2049_, lean_object* v_params_x27_2050_, lean_object* v_fst_2051_, lean_object* v_discrs_x27_2052_, lean_object* v_fst_2053_, lean_object* v_toPure_2054_, lean_object* v_____do__lift_2055_){
_start:
{
lean_object* v_remaining_x27_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; 
v_remaining_x27_2056_ = l_Array_append___redArg(v_fst_2041_, v_____do__lift_2055_);
v___x_2057_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2057_, 0, v_numParams_2042_);
lean_ctor_set(v___x_2057_, 1, v_numDiscrs_2043_);
lean_ctor_set(v___x_2057_, 2, v_altInfos_2044_);
lean_ctor_set(v___x_2057_, 3, v_uElimPos_x3f_2045_);
lean_ctor_set(v___x_2057_, 4, v_snd_2046_);
lean_ctor_set(v___x_2057_, 5, v_overlaps_2047_);
v___x_2058_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
lean_ctor_set(v___x_2058_, 1, v_matcherName_2048_);
lean_ctor_set(v___x_2058_, 2, v_matcherLevels_2049_);
lean_ctor_set(v___x_2058_, 3, v_params_x27_2050_);
lean_ctor_set(v___x_2058_, 4, v_fst_2051_);
lean_ctor_set(v___x_2058_, 5, v_discrs_x27_2052_);
lean_ctor_set(v___x_2058_, 6, v_fst_2053_);
lean_ctor_set(v___x_2058_, 7, v_remaining_x27_2056_);
v___x_2059_ = lean_apply_2(v_toPure_2054_, lean_box(0), v___x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2060_, lean_object* v_numParams_2061_, lean_object* v_numDiscrs_2062_, lean_object* v_altInfos_2063_, lean_object* v_uElimPos_x3f_2064_, lean_object* v_snd_2065_, lean_object* v_overlaps_2066_, lean_object* v_matcherName_2067_, lean_object* v_matcherLevels_2068_, lean_object* v_params_x27_2069_, lean_object* v_fst_2070_, lean_object* v_discrs_x27_2071_, lean_object* v_fst_2072_, lean_object* v_toPure_2073_, lean_object* v_____do__lift_2074_){
_start:
{
lean_object* v_res_2075_; 
v_res_2075_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2060_, v_numParams_2061_, v_numDiscrs_2062_, v_altInfos_2063_, v_uElimPos_x3f_2064_, v_snd_2065_, v_overlaps_2066_, v_matcherName_2067_, v_matcherLevels_2068_, v_params_x27_2069_, v_fst_2070_, v_discrs_x27_2071_, v_fst_2072_, v_toPure_2073_, v_____do__lift_2074_);
lean_dec_ref(v_____do__lift_2074_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2076_, lean_object* v_numParams_2077_, lean_object* v_numDiscrs_2078_, lean_object* v_altInfos_2079_, lean_object* v_uElimPos_x3f_2080_, lean_object* v_snd_2081_, lean_object* v_overlaps_2082_, lean_object* v_matcherName_2083_, lean_object* v_matcherLevels_2084_, lean_object* v_params_x27_2085_, lean_object* v_fst_2086_, lean_object* v_discrs_x27_2087_, lean_object* v_toPure_2088_, lean_object* v_onRemaining_2089_, lean_object* v_remaining_2090_, lean_object* v_toBind_2091_, lean_object* v_____s_2092_){
_start:
{
lean_object* v_fst_2093_; lean_object* v___f_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v_fst_2093_ = lean_ctor_get(v_____s_2092_, 0);
lean_inc(v_fst_2093_);
lean_dec_ref(v_____s_2092_);
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2094_, 0, v_fst_2076_);
lean_closure_set(v___f_2094_, 1, v_numParams_2077_);
lean_closure_set(v___f_2094_, 2, v_numDiscrs_2078_);
lean_closure_set(v___f_2094_, 3, v_altInfos_2079_);
lean_closure_set(v___f_2094_, 4, v_uElimPos_x3f_2080_);
lean_closure_set(v___f_2094_, 5, v_snd_2081_);
lean_closure_set(v___f_2094_, 6, v_overlaps_2082_);
lean_closure_set(v___f_2094_, 7, v_matcherName_2083_);
lean_closure_set(v___f_2094_, 8, v_matcherLevels_2084_);
lean_closure_set(v___f_2094_, 9, v_params_x27_2085_);
lean_closure_set(v___f_2094_, 10, v_fst_2086_);
lean_closure_set(v___f_2094_, 11, v_discrs_x27_2087_);
lean_closure_set(v___f_2094_, 12, v_fst_2093_);
lean_closure_set(v___f_2094_, 13, v_toPure_2088_);
v___x_2095_ = lean_apply_1(v_onRemaining_2089_, v_remaining_2090_);
v___x_2096_ = lean_apply_4(v_toBind_2091_, lean_box(0), lean_box(0), v___x_2095_, v___f_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2097_ = _args[0];
lean_object* v_numParams_2098_ = _args[1];
lean_object* v_numDiscrs_2099_ = _args[2];
lean_object* v_altInfos_2100_ = _args[3];
lean_object* v_uElimPos_x3f_2101_ = _args[4];
lean_object* v_snd_2102_ = _args[5];
lean_object* v_overlaps_2103_ = _args[6];
lean_object* v_matcherName_2104_ = _args[7];
lean_object* v_matcherLevels_2105_ = _args[8];
lean_object* v_params_x27_2106_ = _args[9];
lean_object* v_fst_2107_ = _args[10];
lean_object* v_discrs_x27_2108_ = _args[11];
lean_object* v_toPure_2109_ = _args[12];
lean_object* v_onRemaining_2110_ = _args[13];
lean_object* v_remaining_2111_ = _args[14];
lean_object* v_toBind_2112_ = _args[15];
lean_object* v_____s_2113_ = _args[16];
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2097_, v_numParams_2098_, v_numDiscrs_2099_, v_altInfos_2100_, v_uElimPos_x3f_2101_, v_snd_2102_, v_overlaps_2103_, v_matcherName_2104_, v_matcherLevels_2105_, v_params_x27_2106_, v_fst_2107_, v_discrs_x27_2108_, v_toPure_2109_, v_onRemaining_2110_, v_remaining_2111_, v_toBind_2112_, v_____s_2113_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2115_, lean_object* v_next_2116_, lean_object* v_G_2117_, lean_object* v_____do__lift_2118_){
_start:
{
if (lean_obj_tag(v_____do__lift_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
lean_dec(v_G_2117_);
v_a_2119_ = lean_ctor_get(v_____do__lift_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v_____do__lift_2118_, 1);
v___x_2120_ = lean_apply_2(v_toPure_2115_, lean_box(0), v_a_2119_);
return v___x_2120_;
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
lean_dec(v_toPure_2115_);
v_a_2121_ = lean_ctor_get(v_____do__lift_2118_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v_____do__lift_2118_, 1);
v___x_2122_ = lean_unsigned_to_nat(1u);
v___x_2123_ = lean_nat_add(v_next_2116_, v___x_2122_);
v___x_2124_ = lean_apply_4(v_G_2117_, v___x_2123_, v_a_2121_, lean_box(0), lean_box(0));
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2125_, lean_object* v_next_2126_, lean_object* v_G_2127_, lean_object* v_____do__lift_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2125_, v_next_2126_, v_G_2127_, v_____do__lift_2128_);
lean_dec(v_next_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2130_, lean_object* v_ys4_2131_, uint8_t v___x_2132_, uint8_t v___x_2133_, lean_object* v_inst_2134_, lean_object* v_alt_x27_2135_){
_start:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2136_ = l_Array_append___redArg(v_xs_2130_, v_ys4_2131_);
v___x_2137_ = 1;
v___x_2138_ = lean_box(v___x_2132_);
v___x_2139_ = lean_box(v___x_2133_);
v___x_2140_ = lean_box(v___x_2132_);
v___x_2141_ = lean_box(v___x_2133_);
v___x_2142_ = lean_box(v___x_2137_);
v___x_2143_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2143_, 0, v___x_2136_);
lean_closure_set(v___x_2143_, 1, v_alt_x27_2135_);
lean_closure_set(v___x_2143_, 2, v___x_2138_);
lean_closure_set(v___x_2143_, 3, v___x_2139_);
lean_closure_set(v___x_2143_, 4, v___x_2140_);
lean_closure_set(v___x_2143_, 5, v___x_2141_);
lean_closure_set(v___x_2143_, 6, v___x_2142_);
v___x_2144_ = lean_apply_2(v_inst_2134_, lean_box(0), v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2145_, lean_object* v_ys4_2146_, lean_object* v___x_2147_, lean_object* v___x_2148_, lean_object* v_inst_2149_, lean_object* v_alt_x27_2150_){
_start:
{
uint8_t v___x_12840__boxed_2151_; uint8_t v___x_12841__boxed_2152_; lean_object* v_res_2153_; 
v___x_12840__boxed_2151_ = lean_unbox(v___x_2147_);
v___x_12841__boxed_2152_ = lean_unbox(v___x_2148_);
v_res_2153_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2145_, v_ys4_2146_, v___x_12840__boxed_2151_, v___x_12841__boxed_2152_, v_inst_2149_, v_alt_x27_2150_);
lean_dec_ref(v_ys4_2146_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_xs_2154_, lean_object* v_remaining_x27_2155_, lean_object* v_ys4_2156_, lean_object* v_onAlt_2157_, lean_object* v_next_2158_, lean_object* v_altType_2159_, lean_object* v_toBind_2160_, lean_object* v___f_2161_, lean_object* v_alt_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
lean_inc_ref(v_remaining_x27_2155_);
lean_inc_ref(v_xs_2154_);
v___x_2163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2163_, 0, v_xs_2154_);
lean_ctor_set(v___x_2163_, 1, v_xs_2154_);
lean_ctor_set(v___x_2163_, 2, v_remaining_x27_2155_);
lean_ctor_set(v___x_2163_, 3, v_remaining_x27_2155_);
lean_ctor_set(v___x_2163_, 4, v_ys4_2156_);
v___x_2164_ = lean_apply_4(v_onAlt_2157_, v_next_2158_, v_altType_2159_, v___x_2163_, v_alt_2162_);
v___x_2165_ = lean_apply_4(v_toBind_2160_, lean_box(0), lean_box(0), v___x_2164_, v___f_2161_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2166_, lean_object* v_xs_2167_, lean_object* v_inst_2168_, lean_object* v_toBind_2169_, lean_object* v___f_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_, lean_object* v_names_2173_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_inc_ref(v_xs_2167_);
v___x_2174_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2174_, 0, v___x_2166_);
lean_closure_set(v___x_2174_, 1, v_xs_2167_);
v___x_2175_ = lean_apply_2(v_inst_2168_, lean_box(0), v___x_2174_);
v___x_2176_ = lean_apply_4(v_toBind_2169_, lean_box(0), lean_box(0), v___x_2175_, v___f_2170_);
v___x_2177_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2171_, v_inst_2172_, v_xs_2167_, v_names_2173_, v___x_2176_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2178_, uint8_t v___x_2179_, uint8_t v___x_2180_, lean_object* v_inst_2181_, lean_object* v_remaining_x27_2182_, lean_object* v_onAlt_2183_, lean_object* v_next_2184_, lean_object* v_toBind_2185_, lean_object* v___x_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v___f_2189_, lean_object* v_ys4_2190_, lean_object* v_altType_2191_){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___f_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; 
v___x_2192_ = lean_box(v___x_2179_);
v___x_2193_ = lean_box(v___x_2180_);
lean_inc(v_inst_2181_);
lean_inc_ref(v_ys4_2190_);
lean_inc_ref_n(v_xs_2178_, 2);
v___f_2194_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2194_, 0, v_xs_2178_);
lean_closure_set(v___f_2194_, 1, v_ys4_2190_);
lean_closure_set(v___f_2194_, 2, v___x_2192_);
lean_closure_set(v___f_2194_, 3, v___x_2193_);
lean_closure_set(v___f_2194_, 4, v_inst_2181_);
lean_inc_n(v_toBind_2185_, 2);
v___f_2195_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 9, 8);
lean_closure_set(v___f_2195_, 0, v_xs_2178_);
lean_closure_set(v___f_2195_, 1, v_remaining_x27_2182_);
lean_closure_set(v___f_2195_, 2, v_ys4_2190_);
lean_closure_set(v___f_2195_, 3, v_onAlt_2183_);
lean_closure_set(v___f_2195_, 4, v_next_2184_);
lean_closure_set(v___f_2195_, 5, v_altType_2191_);
lean_closure_set(v___f_2195_, 6, v_toBind_2185_);
lean_closure_set(v___f_2195_, 7, v___f_2194_);
lean_inc_ref(v_inst_2188_);
lean_inc_ref(v_inst_2187_);
lean_inc_ref(v___x_2186_);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2196_, 0, v___x_2186_);
lean_closure_set(v___f_2196_, 1, v_xs_2178_);
lean_closure_set(v___f_2196_, 2, v_inst_2181_);
lean_closure_set(v___f_2196_, 3, v_toBind_2185_);
lean_closure_set(v___f_2196_, 4, v___f_2195_);
lean_closure_set(v___f_2196_, 5, v_inst_2187_);
lean_closure_set(v___f_2196_, 6, v_inst_2188_);
v___x_2197_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2187_, v_inst_2188_, v___x_2186_, v___f_2189_, v___x_2179_);
v___x_2198_ = lean_apply_4(v_toBind_2185_, lean_box(0), lean_box(0), v___x_2197_, v___f_2196_);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2199_, lean_object* v___x_2200_, lean_object* v___x_2201_, lean_object* v_inst_2202_, lean_object* v_remaining_x27_2203_, lean_object* v_onAlt_2204_, lean_object* v_next_2205_, lean_object* v_toBind_2206_, lean_object* v___x_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v___f_2210_, lean_object* v_ys4_2211_, lean_object* v_altType_2212_){
_start:
{
uint8_t v___x_12893__boxed_2213_; uint8_t v___x_12894__boxed_2214_; lean_object* v_res_2215_; 
v___x_12893__boxed_2213_ = lean_unbox(v___x_2200_);
v___x_12894__boxed_2214_ = lean_unbox(v___x_2201_);
v_res_2215_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2199_, v___x_12893__boxed_2213_, v___x_12894__boxed_2214_, v_inst_2202_, v_remaining_x27_2203_, v_onAlt_2204_, v_next_2205_, v_toBind_2206_, v___x_2207_, v_inst_2208_, v_inst_2209_, v___f_2210_, v_ys4_2211_, v_altType_2212_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2216_, uint8_t v___x_2217_, lean_object* v_inst_2218_, lean_object* v_remaining_x27_2219_, lean_object* v_onAlt_2220_, lean_object* v_next_2221_, lean_object* v_toBind_2222_, lean_object* v___x_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v___f_2226_, lean_object* v_fst_2227_, lean_object* v_xs_2228_, lean_object* v_altType_2229_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___f_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2230_ = lean_box(v___x_2216_);
v___x_2231_ = lean_box(v___x_2217_);
lean_inc_ref(v_inst_2225_);
lean_inc_ref(v_inst_2224_);
v___f_2232_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 14, 12);
lean_closure_set(v___f_2232_, 0, v_xs_2228_);
lean_closure_set(v___f_2232_, 1, v___x_2230_);
lean_closure_set(v___f_2232_, 2, v___x_2231_);
lean_closure_set(v___f_2232_, 3, v_inst_2218_);
lean_closure_set(v___f_2232_, 4, v_remaining_x27_2219_);
lean_closure_set(v___f_2232_, 5, v_onAlt_2220_);
lean_closure_set(v___f_2232_, 6, v_next_2221_);
lean_closure_set(v___f_2232_, 7, v_toBind_2222_);
lean_closure_set(v___f_2232_, 8, v___x_2223_);
lean_closure_set(v___f_2232_, 9, v_inst_2224_);
lean_closure_set(v___f_2232_, 10, v_inst_2225_);
lean_closure_set(v___f_2232_, 11, v___f_2226_);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_fst_2227_);
v___x_2234_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2224_, v_inst_2225_, v_altType_2229_, v___x_2233_, v___f_2232_, v___x_2216_, v___x_2216_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2235_, lean_object* v___x_2236_, lean_object* v_inst_2237_, lean_object* v_remaining_x27_2238_, lean_object* v_onAlt_2239_, lean_object* v_next_2240_, lean_object* v_toBind_2241_, lean_object* v___x_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v___f_2245_, lean_object* v_fst_2246_, lean_object* v_xs_2247_, lean_object* v_altType_2248_){
_start:
{
uint8_t v___x_12928__boxed_2249_; uint8_t v___x_12929__boxed_2250_; lean_object* v_res_2251_; 
v___x_12928__boxed_2249_ = lean_unbox(v___x_2235_);
v___x_12929__boxed_2250_ = lean_unbox(v___x_2236_);
v_res_2251_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_12928__boxed_2249_, v___x_12929__boxed_2250_, v_inst_2237_, v_remaining_x27_2238_, v_onAlt_2239_, v_next_2240_, v_toBind_2241_, v___x_2242_, v_inst_2243_, v_inst_2244_, v___f_2245_, v_fst_2246_, v_xs_2247_, v_altType_2248_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_fst_2252_, lean_object* v___x_2253_, lean_object* v___x_2254_, lean_object* v___x_2255_, lean_object* v_toPure_2256_, lean_object* v_alt_x27_2257_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2258_ = lean_array_push(v_fst_2252_, v_alt_x27_2257_);
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2253_);
lean_ctor_set(v___x_2259_, 1, v___x_2254_);
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2255_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
v___x_2263_ = lean_apply_2(v_toPure_2256_, lean_box(0), v___x_2262_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2264_, lean_object* v_toPure_2265_, lean_object* v_toBind_2266_, lean_object* v___f_2267_, uint8_t v___x_2268_, uint8_t v___x_2269_, lean_object* v_inst_2270_, lean_object* v_remaining_x27_2271_, lean_object* v_onAlt_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v___f_2275_, lean_object* v_fst_2276_, lean_object* v_next_2277_, lean_object* v_acc_2278_, lean_object* v_h_2279_, lean_object* v_G_2280_){
_start:
{
uint8_t v___x_2281_; 
v___x_2281_ = lean_nat_dec_lt(v_next_2277_, v___x_2264_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; 
lean_dec(v_G_2280_);
lean_dec(v_next_2277_);
lean_dec(v_fst_2276_);
lean_dec(v___f_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec_ref(v_inst_2273_);
lean_dec(v_onAlt_2272_);
lean_dec_ref(v_remaining_x27_2271_);
lean_dec(v_inst_2270_);
lean_dec(v___f_2267_);
lean_dec(v_toBind_2266_);
v___x_2282_ = lean_apply_2(v_toPure_2265_, lean_box(0), v_acc_2278_);
return v___x_2282_;
}
else
{
lean_object* v_snd_2283_; lean_object* v_snd_2284_; lean_object* v_snd_2285_; lean_object* v_fst_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2396_; 
v_snd_2283_ = lean_ctor_get(v_acc_2278_, 1);
lean_inc(v_snd_2283_);
v_snd_2284_ = lean_ctor_get(v_snd_2283_, 1);
lean_inc(v_snd_2284_);
v_snd_2285_ = lean_ctor_get(v_snd_2284_, 1);
lean_inc(v_snd_2285_);
v_fst_2286_ = lean_ctor_get(v_acc_2278_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_acc_2278_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v_acc_2278_, 1);
lean_dec(v_unused_2397_);
v___x_2288_ = v_acc_2278_;
v_isShared_2289_ = v_isSharedCheck_2396_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_fst_2286_);
lean_dec(v_acc_2278_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2396_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v_fst_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2394_; 
v_fst_2290_ = lean_ctor_get(v_snd_2283_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_snd_2283_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v_snd_2283_, 1);
lean_dec(v_unused_2395_);
v___x_2292_ = v_snd_2283_;
v_isShared_2293_ = v_isSharedCheck_2394_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_fst_2290_);
lean_dec(v_snd_2283_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2394_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_fst_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2392_; 
v_fst_2294_ = lean_ctor_get(v_snd_2284_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_snd_2284_);
if (v_isSharedCheck_2392_ == 0)
{
lean_object* v_unused_2393_; 
v_unused_2393_ = lean_ctor_get(v_snd_2284_, 1);
lean_dec(v_unused_2393_);
v___x_2296_ = v_snd_2284_;
v_isShared_2297_ = v_isSharedCheck_2392_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_fst_2294_);
lean_dec(v_snd_2284_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2392_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_array_2298_; lean_object* v_start_2299_; lean_object* v_stop_2300_; lean_object* v___f_2301_; lean_object* v___y_2303_; uint8_t v___x_2306_; 
v_array_2298_ = lean_ctor_get(v_snd_2285_, 0);
v_start_2299_ = lean_ctor_get(v_snd_2285_, 1);
v_stop_2300_ = lean_ctor_get(v_snd_2285_, 2);
lean_inc(v_next_2277_);
lean_inc(v_toPure_2265_);
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2301_, 0, v_toPure_2265_);
lean_closure_set(v___f_2301_, 1, v_next_2277_);
lean_closure_set(v___f_2301_, 2, v_G_2280_);
v___x_2306_ = lean_nat_dec_lt(v_start_2299_, v_stop_2300_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2308_; 
lean_dec(v_next_2277_);
lean_dec(v_fst_2276_);
lean_dec(v___f_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec_ref(v_inst_2273_);
lean_dec(v_onAlt_2272_);
lean_dec_ref(v_remaining_x27_2271_);
lean_dec(v_inst_2270_);
if (v_isShared_2297_ == 0)
{
v___x_2308_ = v___x_2296_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_fst_2294_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v_snd_2285_);
v___x_2308_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___x_2308_);
v___x_2310_ = v___x_2292_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_fst_2290_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2310_);
v___x_2312_ = v___x_2288_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_fst_2286_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
v___x_2314_ = lean_apply_2(v_toPure_2265_, lean_box(0), v___x_2313_);
v___y_2303_ = v___x_2314_;
goto v___jp_2302_;
}
}
}
}
else
{
lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2388_; 
lean_inc(v_stop_2300_);
lean_inc(v_start_2299_);
lean_inc_ref(v_array_2298_);
v_isSharedCheck_2388_ = !lean_is_exclusive(v_snd_2285_);
if (v_isSharedCheck_2388_ == 0)
{
lean_object* v_unused_2389_; lean_object* v_unused_2390_; lean_object* v_unused_2391_; 
v_unused_2389_ = lean_ctor_get(v_snd_2285_, 2);
lean_dec(v_unused_2389_);
v_unused_2390_ = lean_ctor_get(v_snd_2285_, 1);
lean_dec(v_unused_2390_);
v_unused_2391_ = lean_ctor_get(v_snd_2285_, 0);
lean_dec(v_unused_2391_);
v___x_2319_ = v_snd_2285_;
v_isShared_2320_ = v_isSharedCheck_2388_;
goto v_resetjp_2318_;
}
else
{
lean_dec(v_snd_2285_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2388_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_array_2321_; lean_object* v_start_2322_; lean_object* v_stop_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2328_; 
v_array_2321_ = lean_ctor_get(v_fst_2294_, 0);
v_start_2322_ = lean_ctor_get(v_fst_2294_, 1);
v_stop_2323_ = lean_ctor_get(v_fst_2294_, 2);
v___x_2324_ = lean_array_fget(v_array_2298_, v_start_2299_);
v___x_2325_ = lean_unsigned_to_nat(1u);
v___x_2326_ = lean_nat_add(v_start_2299_, v___x_2325_);
lean_dec(v_start_2299_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 1, v___x_2326_);
v___x_2328_ = v___x_2319_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_array_2298_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2387_, 2, v_stop_2300_);
v___x_2328_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
uint8_t v___x_2329_; 
v___x_2329_ = lean_nat_dec_lt(v_start_2322_, v_stop_2323_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2331_; 
lean_dec(v___x_2324_);
lean_dec(v_next_2277_);
lean_dec(v_fst_2276_);
lean_dec(v___f_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec_ref(v_inst_2273_);
lean_dec(v_onAlt_2272_);
lean_dec_ref(v_remaining_x27_2271_);
lean_dec(v_inst_2270_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2328_);
v___x_2331_ = v___x_2296_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_fst_2294_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___x_2328_);
v___x_2331_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2333_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___x_2331_);
v___x_2333_ = v___x_2292_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_fst_2290_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2331_);
v___x_2333_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2333_);
v___x_2335_ = v___x_2288_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_fst_2286_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
v___x_2337_ = lean_apply_2(v_toPure_2265_, lean_box(0), v___x_2336_);
v___y_2303_ = v___x_2337_;
goto v___jp_2302_;
}
}
}
}
else
{
lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2383_; 
lean_inc(v_stop_2323_);
lean_inc(v_start_2322_);
lean_inc_ref(v_array_2321_);
v_isSharedCheck_2383_ = !lean_is_exclusive(v_fst_2294_);
if (v_isSharedCheck_2383_ == 0)
{
lean_object* v_unused_2384_; lean_object* v_unused_2385_; lean_object* v_unused_2386_; 
v_unused_2384_ = lean_ctor_get(v_fst_2294_, 2);
lean_dec(v_unused_2384_);
v_unused_2385_ = lean_ctor_get(v_fst_2294_, 1);
lean_dec(v_unused_2385_);
v_unused_2386_ = lean_ctor_get(v_fst_2294_, 0);
lean_dec(v_unused_2386_);
v___x_2342_ = v_fst_2294_;
v_isShared_2343_ = v_isSharedCheck_2383_;
goto v_resetjp_2341_;
}
else
{
lean_dec(v_fst_2294_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2383_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_array_2344_; lean_object* v_start_2345_; lean_object* v_stop_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2350_; 
v_array_2344_ = lean_ctor_get(v_fst_2290_, 0);
v_start_2345_ = lean_ctor_get(v_fst_2290_, 1);
v_stop_2346_ = lean_ctor_get(v_fst_2290_, 2);
v___x_2347_ = lean_array_fget(v_array_2321_, v_start_2322_);
v___x_2348_ = lean_nat_add(v_start_2322_, v___x_2325_);
lean_dec(v_start_2322_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 1, v___x_2348_);
v___x_2350_ = v___x_2342_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_array_2321_);
lean_ctor_set(v_reuseFailAlloc_2382_, 1, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2382_, 2, v_stop_2323_);
v___x_2350_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_nat_dec_lt(v_start_2345_, v_stop_2346_);
if (v___x_2351_ == 0)
{
lean_object* v___x_2353_; 
lean_dec(v___x_2347_);
lean_dec(v___x_2324_);
lean_dec(v_next_2277_);
lean_dec(v_fst_2276_);
lean_dec(v___f_2275_);
lean_dec_ref(v_inst_2274_);
lean_dec_ref(v_inst_2273_);
lean_dec(v_onAlt_2272_);
lean_dec_ref(v_remaining_x27_2271_);
lean_dec(v_inst_2270_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 1, v___x_2328_);
lean_ctor_set(v___x_2296_, 0, v___x_2350_);
v___x_2353_ = v___x_2296_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2328_);
v___x_2353_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v___x_2353_);
v___x_2355_ = v___x_2292_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_fst_2290_);
lean_ctor_set(v_reuseFailAlloc_2361_, 1, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2355_);
v___x_2357_ = v___x_2288_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_fst_2286_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
v___x_2359_ = lean_apply_2(v_toPure_2265_, lean_box(0), v___x_2358_);
v___y_2303_ = v___x_2359_;
goto v___jp_2302_;
}
}
}
}
else
{
lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2378_; 
lean_inc(v_stop_2346_);
lean_inc(v_start_2345_);
lean_inc_ref(v_array_2344_);
lean_del_object(v___x_2296_);
lean_del_object(v___x_2292_);
lean_del_object(v___x_2288_);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_fst_2290_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; lean_object* v_unused_2380_; lean_object* v_unused_2381_; 
v_unused_2379_ = lean_ctor_get(v_fst_2290_, 2);
lean_dec(v_unused_2379_);
v_unused_2380_ = lean_ctor_get(v_fst_2290_, 1);
lean_dec(v_unused_2380_);
v_unused_2381_ = lean_ctor_get(v_fst_2290_, 0);
lean_dec(v_unused_2381_);
v___x_2364_ = v_fst_2290_;
v_isShared_2365_ = v_isSharedCheck_2378_;
goto v_resetjp_2363_;
}
else
{
lean_dec(v_fst_2290_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2378_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2366_ = lean_array_fget_borrowed(v_array_2344_, v_start_2345_);
v___x_2367_ = lean_box(v___x_2268_);
v___x_2368_ = lean_box(v___x_2269_);
lean_inc_ref(v_inst_2274_);
lean_inc_ref(v_inst_2273_);
lean_inc(v___x_2366_);
lean_inc(v_toBind_2266_);
v___f_2369_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 14, 12);
lean_closure_set(v___f_2369_, 0, v___x_2367_);
lean_closure_set(v___f_2369_, 1, v___x_2368_);
lean_closure_set(v___f_2369_, 2, v_inst_2270_);
lean_closure_set(v___f_2369_, 3, v_remaining_x27_2271_);
lean_closure_set(v___f_2369_, 4, v_onAlt_2272_);
lean_closure_set(v___f_2369_, 5, v_next_2277_);
lean_closure_set(v___f_2369_, 6, v_toBind_2266_);
lean_closure_set(v___f_2369_, 7, v___x_2366_);
lean_closure_set(v___f_2369_, 8, v_inst_2273_);
lean_closure_set(v___f_2369_, 9, v_inst_2274_);
lean_closure_set(v___f_2369_, 10, v___f_2275_);
lean_closure_set(v___f_2369_, 11, v_fst_2276_);
v___x_2370_ = lean_nat_add(v_start_2345_, v___x_2325_);
lean_dec(v_start_2345_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v___x_2370_);
v___x_2372_ = v___x_2364_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_array_2344_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v_stop_2346_);
v___x_2372_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___f_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___f_2373_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2373_, 0, v_fst_2286_);
lean_closure_set(v___f_2373_, 1, v___x_2350_);
lean_closure_set(v___f_2373_, 2, v___x_2328_);
lean_closure_set(v___f_2373_, 3, v___x_2372_);
lean_closure_set(v___f_2373_, 4, v_toPure_2265_);
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2347_);
v___x_2375_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2273_, v_inst_2274_, v___x_2324_, v___x_2374_, v___f_2369_, v___x_2268_, v___x_2268_);
lean_inc(v_toBind_2266_);
v___x_2376_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v___x_2375_, v___f_2373_);
v___y_2303_ = v___x_2376_;
goto v___jp_2302_;
}
}
}
}
}
}
}
}
}
v___jp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_inc(v_toBind_2266_);
v___x_2304_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v___y_2303_, v___f_2267_);
v___x_2305_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v___x_2304_, v___f_2301_);
return v___x_2305_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_2398_ = _args[0];
lean_object* v_toPure_2399_ = _args[1];
lean_object* v_toBind_2400_ = _args[2];
lean_object* v___f_2401_ = _args[3];
lean_object* v___x_2402_ = _args[4];
lean_object* v___x_2403_ = _args[5];
lean_object* v_inst_2404_ = _args[6];
lean_object* v_remaining_x27_2405_ = _args[7];
lean_object* v_onAlt_2406_ = _args[8];
lean_object* v_inst_2407_ = _args[9];
lean_object* v_inst_2408_ = _args[10];
lean_object* v___f_2409_ = _args[11];
lean_object* v_fst_2410_ = _args[12];
lean_object* v_next_2411_ = _args[13];
lean_object* v_acc_2412_ = _args[14];
lean_object* v_h_2413_ = _args[15];
lean_object* v_G_2414_ = _args[16];
_start:
{
uint8_t v___x_12979__boxed_2415_; uint8_t v___x_12980__boxed_2416_; lean_object* v_res_2417_; 
v___x_12979__boxed_2415_ = lean_unbox(v___x_2402_);
v___x_12980__boxed_2416_ = lean_unbox(v___x_2403_);
v_res_2417_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2398_, v_toPure_2399_, v_toBind_2400_, v___f_2401_, v___x_12979__boxed_2415_, v___x_12980__boxed_2416_, v_inst_2404_, v_remaining_x27_2405_, v_onAlt_2406_, v_inst_2407_, v_inst_2408_, v___f_2409_, v_fst_2410_, v_next_2411_, v_acc_2412_, v_h_2413_, v_G_2414_);
lean_dec(v___x_2398_);
return v_res_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_matcherApp_2418_, lean_object* v_alts_2419_, lean_object* v___x_2420_, lean_object* v___x_2421_, lean_object* v_remaining_x27_2422_, lean_object* v___f_2423_, lean_object* v_toBind_2424_, lean_object* v___f_2425_, lean_object* v_altTypes_2426_){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2427_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2418_);
v___x_2428_ = lean_array_get_size(v___x_2427_);
v___x_2429_ = lean_array_get_size(v_altTypes_2426_);
lean_inc_n(v___x_2420_, 3);
v___x_2430_ = l_Array_toSubarray___redArg(v_alts_2419_, v___x_2420_, v___x_2421_);
v___x_2431_ = l_Array_toSubarray___redArg(v___x_2427_, v___x_2420_, v___x_2428_);
v___x_2432_ = l_Array_toSubarray___redArg(v_altTypes_2426_, v___x_2420_, v___x_2429_);
v___x_2433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2431_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2430_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_remaining_x27_2422_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2423_, v___x_2420_, v___x_2435_, lean_box(0));
v___x_2437_ = lean_apply_4(v_toBind_2424_, lean_box(0), lean_box(0), v___x_2436_, v___f_2425_);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2438_, lean_object* v_toPure_2439_, lean_object* v_toBind_2440_, lean_object* v___f_2441_, uint8_t v___x_2442_, uint8_t v___x_2443_, lean_object* v_inst_2444_, lean_object* v_remaining_x27_2445_, lean_object* v_onAlt_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v___f_2449_, lean_object* v_fst_2450_, lean_object* v_matcherApp_2451_, lean_object* v___x_2452_, lean_object* v___f_2453_, lean_object* v_aux_2454_, lean_object* v_____r_2455_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2456_ = lean_array_get_size(v_alts_2438_);
v___x_2457_ = lean_box(v___x_2442_);
v___x_2458_ = lean_box(v___x_2443_);
lean_inc_ref(v_remaining_x27_2445_);
lean_inc(v_inst_2444_);
lean_inc_n(v_toBind_2440_, 2);
v___f_2459_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 17, 13);
lean_closure_set(v___f_2459_, 0, v___x_2456_);
lean_closure_set(v___f_2459_, 1, v_toPure_2439_);
lean_closure_set(v___f_2459_, 2, v_toBind_2440_);
lean_closure_set(v___f_2459_, 3, v___f_2441_);
lean_closure_set(v___f_2459_, 4, v___x_2457_);
lean_closure_set(v___f_2459_, 5, v___x_2458_);
lean_closure_set(v___f_2459_, 6, v_inst_2444_);
lean_closure_set(v___f_2459_, 7, v_remaining_x27_2445_);
lean_closure_set(v___f_2459_, 8, v_onAlt_2446_);
lean_closure_set(v___f_2459_, 9, v_inst_2447_);
lean_closure_set(v___f_2459_, 10, v_inst_2448_);
lean_closure_set(v___f_2459_, 11, v___f_2449_);
lean_closure_set(v___f_2459_, 12, v_fst_2450_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2460_, 0, v_matcherApp_2451_);
lean_closure_set(v___f_2460_, 1, v_alts_2438_);
lean_closure_set(v___f_2460_, 2, v___x_2452_);
lean_closure_set(v___f_2460_, 3, v___x_2456_);
lean_closure_set(v___f_2460_, 4, v_remaining_x27_2445_);
lean_closure_set(v___f_2460_, 5, v___f_2459_);
lean_closure_set(v___f_2460_, 6, v_toBind_2440_);
lean_closure_set(v___f_2460_, 7, v___f_2453_);
v___x_2461_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2461_, 0, v___x_2456_);
lean_closure_set(v___x_2461_, 1, v_aux_2454_);
v___x_2462_ = lean_apply_2(v_inst_2444_, lean_box(0), v___x_2461_);
v___x_2463_ = lean_apply_4(v_toBind_2440_, lean_box(0), lean_box(0), v___x_2462_, v___f_2460_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_alts_2464_ = _args[0];
lean_object* v_toPure_2465_ = _args[1];
lean_object* v_toBind_2466_ = _args[2];
lean_object* v___f_2467_ = _args[3];
lean_object* v___x_2468_ = _args[4];
lean_object* v___x_2469_ = _args[5];
lean_object* v_inst_2470_ = _args[6];
lean_object* v_remaining_x27_2471_ = _args[7];
lean_object* v_onAlt_2472_ = _args[8];
lean_object* v_inst_2473_ = _args[9];
lean_object* v_inst_2474_ = _args[10];
lean_object* v___f_2475_ = _args[11];
lean_object* v_fst_2476_ = _args[12];
lean_object* v_matcherApp_2477_ = _args[13];
lean_object* v___x_2478_ = _args[14];
lean_object* v___f_2479_ = _args[15];
lean_object* v_aux_2480_ = _args[16];
lean_object* v_____r_2481_ = _args[17];
_start:
{
uint8_t v___x_13236__boxed_2482_; uint8_t v___x_13237__boxed_2483_; lean_object* v_res_2484_; 
v___x_13236__boxed_2482_ = lean_unbox(v___x_2468_);
v___x_13237__boxed_2483_ = lean_unbox(v___x_2469_);
v_res_2484_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2464_, v_toPure_2465_, v_toBind_2466_, v___f_2467_, v___x_13236__boxed_2482_, v___x_13237__boxed_2483_, v_inst_2470_, v_remaining_x27_2471_, v_onAlt_2472_, v_inst_2473_, v_inst_2474_, v___f_2475_, v_fst_2476_, v_matcherApp_2477_, v___x_2478_, v___f_2479_, v_aux_2480_, v_____r_2481_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v___x_2485_, lean_object* v_e_2486_){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = l_Lean_indentD(v_e_2486_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2485_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v___x_2489_, lean_object* v___f_2490_, lean_object* v_runInBase_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_apply_2(v_runInBase_2491_, lean_box(0), v___x_2489_);
v___x_2498_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2497_, v___f_2490_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object* v___x_2499_, lean_object* v___f_2500_, lean_object* v_runInBase_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2499_, v___f_2500_, v_runInBase_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v_toPure_2508_, lean_object* v_next_2509_, lean_object* v_G_2510_, lean_object* v_____do__lift_2511_){
_start:
{
if (lean_obj_tag(v_____do__lift_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2513_; 
lean_dec(v_G_2510_);
v_a_2512_ = lean_ctor_get(v_____do__lift_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v_____do__lift_2511_, 1);
v___x_2513_ = lean_apply_2(v_toPure_2508_, lean_box(0), v_a_2512_);
return v___x_2513_;
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
lean_dec(v_toPure_2508_);
v_a_2514_ = lean_ctor_get(v_____do__lift_2511_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v_____do__lift_2511_, 1);
v___x_2515_ = lean_unsigned_to_nat(1u);
v___x_2516_ = lean_nat_add(v_next_2509_, v___x_2515_);
v___x_2517_ = lean_apply_4(v_G_2510_, v___x_2516_, v_a_2514_, lean_box(0), lean_box(0));
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v_toPure_2518_, lean_object* v_next_2519_, lean_object* v_G_2520_, lean_object* v_____do__lift_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v_toPure_2518_, v_next_2519_, v_G_2520_, v_____do__lift_2521_);
lean_dec(v_next_2519_);
return v_res_2522_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_box(0);
v___x_2532_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4));
v___x_2533_ = l_Lean_mkConst(v___x_2532_, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2534_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5);
v___x_2535_ = lean_unsigned_to_nat(2u);
v___x_2536_ = lean_mk_empty_array_with_capacity(v___x_2535_);
v___x_2537_ = lean_array_push(v___x_2536_, v___x_2534_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v___x_2538_, lean_object* v_toPure_2539_, lean_object* v_inst_2540_, lean_object* v_alt_x27_2541_){
_start:
{
uint8_t v_hasUnitThunk_2542_; 
v_hasUnitThunk_2542_ = lean_ctor_get_uint8(v___x_2538_, sizeof(void*)*2);
if (v_hasUnitThunk_2542_ == 0)
{
lean_object* v___x_2543_; 
lean_dec(v_inst_2540_);
v___x_2543_ = lean_apply_2(v_toPure_2539_, lean_box(0), v_alt_x27_2541_);
return v___x_2543_;
}
else
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
lean_dec(v_toPure_2539_);
v___x_2544_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_2545_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_2546_ = lean_array_push(v___x_2545_, v_alt_x27_2541_);
v___x_2547_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2547_, 0, v___x_2544_);
lean_closure_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_apply_2(v_inst_2540_, lean_box(0), v___x_2547_);
return v___x_2548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v___x_2549_, lean_object* v_toPure_2550_, lean_object* v_inst_2551_, lean_object* v_alt_x27_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v___x_2549_, v_toPure_2550_, v_inst_2551_, v_alt_x27_2552_);
lean_dec_ref(v___x_2549_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v_ys_2554_, lean_object* v_ys2_2555_, lean_object* v_ys3_2556_, lean_object* v_ys4_2557_, uint8_t v___x_2558_, uint8_t v_useSplitter_2559_, lean_object* v_inst_2560_, lean_object* v_alt_x27_2561_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v___x_2562_ = l_Array_append___redArg(v_ys_2554_, v_ys2_2555_);
v___x_2563_ = l_Array_append___redArg(v___x_2562_, v_ys3_2556_);
v___x_2564_ = l_Array_append___redArg(v___x_2563_, v_ys4_2557_);
v___x_2565_ = 1;
v___x_2566_ = lean_box(v___x_2558_);
v___x_2567_ = lean_box(v_useSplitter_2559_);
v___x_2568_ = lean_box(v___x_2558_);
v___x_2569_ = lean_box(v_useSplitter_2559_);
v___x_2570_ = lean_box(v___x_2565_);
v___x_2571_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2571_, 0, v___x_2564_);
lean_closure_set(v___x_2571_, 1, v_alt_x27_2561_);
lean_closure_set(v___x_2571_, 2, v___x_2566_);
lean_closure_set(v___x_2571_, 3, v___x_2567_);
lean_closure_set(v___x_2571_, 4, v___x_2568_);
lean_closure_set(v___x_2571_, 5, v___x_2569_);
lean_closure_set(v___x_2571_, 6, v___x_2570_);
v___x_2572_ = lean_apply_2(v_inst_2560_, lean_box(0), v___x_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v_ys_2573_, lean_object* v_ys2_2574_, lean_object* v_ys3_2575_, lean_object* v_ys4_2576_, lean_object* v___x_2577_, lean_object* v_useSplitter_2578_, lean_object* v_inst_2579_, lean_object* v_alt_x27_2580_){
_start:
{
uint8_t v___x_13390__boxed_2581_; uint8_t v_useSplitter_boxed_2582_; lean_object* v_res_2583_; 
v___x_13390__boxed_2581_ = lean_unbox(v___x_2577_);
v_useSplitter_boxed_2582_ = lean_unbox(v_useSplitter_2578_);
v_res_2583_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2573_, v_ys2_2574_, v_ys3_2575_, v_ys4_2576_, v___x_13390__boxed_2581_, v_useSplitter_boxed_2582_, v_inst_2579_, v_alt_x27_2580_);
lean_dec_ref(v_ys4_2576_);
lean_dec_ref(v_ys3_2575_);
lean_dec_ref(v_ys2_2574_);
return v_res_2583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_args_2584_, lean_object* v_ys_2585_, lean_object* v_ys2_2586_, lean_object* v_ys3_2587_, lean_object* v_ys4_2588_, lean_object* v_onAlt_2589_, lean_object* v_next_2590_, lean_object* v_altType_2591_, lean_object* v_toBind_2592_, lean_object* v___f_2593_, lean_object* v_alt_2594_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2595_, 0, v_args_2584_);
lean_ctor_set(v___x_2595_, 1, v_ys_2585_);
lean_ctor_set(v___x_2595_, 2, v_ys2_2586_);
lean_ctor_set(v___x_2595_, 3, v_ys3_2587_);
lean_ctor_set(v___x_2595_, 4, v_ys4_2588_);
v___x_2596_ = lean_apply_4(v_onAlt_2589_, v_next_2590_, v_altType_2591_, v___x_2595_, v_alt_2594_);
v___x_2597_ = lean_apply_4(v_toBind_2592_, lean_box(0), lean_box(0), v___x_2596_, v___f_2593_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_toMonadExceptOf_2598_, lean_object* v_ys_2599_, lean_object* v_ys2_2600_, lean_object* v_ys3_2601_, uint8_t v___x_2602_, uint8_t v_useSplitter_2603_, lean_object* v_inst_2604_, lean_object* v_args_2605_, lean_object* v_onAlt_2606_, lean_object* v_next_2607_, lean_object* v_toBind_2608_, lean_object* v___x_2609_, lean_object* v___f_2610_, lean_object* v_ys4_2611_, lean_object* v_altType_2612_){
_start:
{
lean_object* v_tryCatch_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_tryCatch_2613_ = lean_ctor_get(v_toMonadExceptOf_2598_, 1);
lean_inc(v_tryCatch_2613_);
lean_dec_ref(v_toMonadExceptOf_2598_);
v___x_2614_ = lean_box(v___x_2602_);
v___x_2615_ = lean_box(v_useSplitter_2603_);
lean_inc(v_inst_2604_);
lean_inc_ref(v_ys4_2611_);
lean_inc_ref_n(v_ys3_2601_, 2);
lean_inc_ref(v_ys2_2600_);
lean_inc_ref(v_ys_2599_);
v___f_2616_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2616_, 0, v_ys_2599_);
lean_closure_set(v___f_2616_, 1, v_ys2_2600_);
lean_closure_set(v___f_2616_, 2, v_ys3_2601_);
lean_closure_set(v___f_2616_, 3, v_ys4_2611_);
lean_closure_set(v___f_2616_, 4, v___x_2614_);
lean_closure_set(v___f_2616_, 5, v___x_2615_);
lean_closure_set(v___f_2616_, 6, v_inst_2604_);
lean_inc(v_toBind_2608_);
lean_inc_ref(v_args_2605_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 11, 10);
lean_closure_set(v___f_2617_, 0, v_args_2605_);
lean_closure_set(v___f_2617_, 1, v_ys_2599_);
lean_closure_set(v___f_2617_, 2, v_ys2_2600_);
lean_closure_set(v___f_2617_, 3, v_ys3_2601_);
lean_closure_set(v___f_2617_, 4, v_ys4_2611_);
lean_closure_set(v___f_2617_, 5, v_onAlt_2606_);
lean_closure_set(v___f_2617_, 6, v_next_2607_);
lean_closure_set(v___f_2617_, 7, v_altType_2612_);
lean_closure_set(v___f_2617_, 8, v_toBind_2608_);
lean_closure_set(v___f_2617_, 9, v___f_2616_);
v___x_2618_ = l_Array_append___redArg(v_args_2605_, v_ys3_2601_);
lean_dec_ref(v_ys3_2601_);
v___x_2619_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2619_, 0, v___x_2609_);
lean_closure_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = lean_apply_2(v_inst_2604_, lean_box(0), v___x_2619_);
v___x_2621_ = lean_apply_3(v_tryCatch_2613_, lean_box(0), v___x_2620_, v___f_2610_);
v___x_2622_ = lean_apply_4(v_toBind_2608_, lean_box(0), lean_box(0), v___x_2621_, v___f_2617_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_toMonadExceptOf_2623_, lean_object* v_ys_2624_, lean_object* v_ys2_2625_, lean_object* v_ys3_2626_, lean_object* v___x_2627_, lean_object* v_useSplitter_2628_, lean_object* v_inst_2629_, lean_object* v_args_2630_, lean_object* v_onAlt_2631_, lean_object* v_next_2632_, lean_object* v_toBind_2633_, lean_object* v___x_2634_, lean_object* v___f_2635_, lean_object* v_ys4_2636_, lean_object* v_altType_2637_){
_start:
{
uint8_t v___x_13426__boxed_2638_; uint8_t v_useSplitter_boxed_2639_; lean_object* v_res_2640_; 
v___x_13426__boxed_2638_ = lean_unbox(v___x_2627_);
v_useSplitter_boxed_2639_ = lean_unbox(v_useSplitter_2628_);
v_res_2640_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_toMonadExceptOf_2623_, v_ys_2624_, v_ys2_2625_, v_ys3_2626_, v___x_13426__boxed_2638_, v_useSplitter_boxed_2639_, v_inst_2629_, v_args_2630_, v_onAlt_2631_, v_next_2632_, v_toBind_2633_, v___x_2634_, v___f_2635_, v_ys4_2636_, v_altType_2637_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_toMonadExceptOf_2641_, lean_object* v_ys_2642_, lean_object* v_ys2_2643_, uint8_t v___x_2644_, uint8_t v_useSplitter_2645_, lean_object* v_inst_2646_, lean_object* v_args_2647_, lean_object* v_onAlt_2648_, lean_object* v_next_2649_, lean_object* v_toBind_2650_, lean_object* v___x_2651_, lean_object* v___f_2652_, lean_object* v_fst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_ys3_2656_, lean_object* v_altType_2657_){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___f_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2658_ = lean_box(v___x_2644_);
v___x_2659_ = lean_box(v_useSplitter_2645_);
v___f_2660_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2660_, 0, v_toMonadExceptOf_2641_);
lean_closure_set(v___f_2660_, 1, v_ys_2642_);
lean_closure_set(v___f_2660_, 2, v_ys2_2643_);
lean_closure_set(v___f_2660_, 3, v_ys3_2656_);
lean_closure_set(v___f_2660_, 4, v___x_2658_);
lean_closure_set(v___f_2660_, 5, v___x_2659_);
lean_closure_set(v___f_2660_, 6, v_inst_2646_);
lean_closure_set(v___f_2660_, 7, v_args_2647_);
lean_closure_set(v___f_2660_, 8, v_onAlt_2648_);
lean_closure_set(v___f_2660_, 9, v_next_2649_);
lean_closure_set(v___f_2660_, 10, v_toBind_2650_);
lean_closure_set(v___f_2660_, 11, v___x_2651_);
lean_closure_set(v___f_2660_, 12, v___f_2652_);
v___x_2661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2661_, 0, v_fst_2653_);
v___x_2662_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2654_, v_inst_2655_, v_altType_2657_, v___x_2661_, v___f_2660_, v___x_2644_, v___x_2644_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2663_ = _args[0];
lean_object* v_ys_2664_ = _args[1];
lean_object* v_ys2_2665_ = _args[2];
lean_object* v___x_2666_ = _args[3];
lean_object* v_useSplitter_2667_ = _args[4];
lean_object* v_inst_2668_ = _args[5];
lean_object* v_args_2669_ = _args[6];
lean_object* v_onAlt_2670_ = _args[7];
lean_object* v_next_2671_ = _args[8];
lean_object* v_toBind_2672_ = _args[9];
lean_object* v___x_2673_ = _args[10];
lean_object* v___f_2674_ = _args[11];
lean_object* v_fst_2675_ = _args[12];
lean_object* v_inst_2676_ = _args[13];
lean_object* v_inst_2677_ = _args[14];
lean_object* v_ys3_2678_ = _args[15];
lean_object* v_altType_2679_ = _args[16];
_start:
{
uint8_t v___x_13456__boxed_2680_; uint8_t v_useSplitter_boxed_2681_; lean_object* v_res_2682_; 
v___x_13456__boxed_2680_ = lean_unbox(v___x_2666_);
v_useSplitter_boxed_2681_ = lean_unbox(v_useSplitter_2667_);
v_res_2682_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_toMonadExceptOf_2663_, v_ys_2664_, v_ys2_2665_, v___x_13456__boxed_2680_, v_useSplitter_boxed_2681_, v_inst_2668_, v_args_2669_, v_onAlt_2670_, v_next_2671_, v_toBind_2672_, v___x_2673_, v___f_2674_, v_fst_2675_, v_inst_2676_, v_inst_2677_, v_ys3_2678_, v_altType_2679_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_toMonadExceptOf_2683_, lean_object* v_ys_2684_, uint8_t v___x_2685_, uint8_t v_useSplitter_2686_, lean_object* v_inst_2687_, lean_object* v_args_2688_, lean_object* v_onAlt_2689_, lean_object* v_next_2690_, lean_object* v_toBind_2691_, lean_object* v___x_2692_, lean_object* v___f_2693_, lean_object* v_fst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_numDiscrEqs_2697_, lean_object* v_ys2_2698_, lean_object* v_altType_2699_){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2700_ = lean_box(v___x_2685_);
v___x_2701_ = lean_box(v_useSplitter_2686_);
lean_inc_ref(v_inst_2696_);
lean_inc_ref(v_inst_2695_);
v___f_2702_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2702_, 0, v_toMonadExceptOf_2683_);
lean_closure_set(v___f_2702_, 1, v_ys_2684_);
lean_closure_set(v___f_2702_, 2, v_ys2_2698_);
lean_closure_set(v___f_2702_, 3, v___x_2700_);
lean_closure_set(v___f_2702_, 4, v___x_2701_);
lean_closure_set(v___f_2702_, 5, v_inst_2687_);
lean_closure_set(v___f_2702_, 6, v_args_2688_);
lean_closure_set(v___f_2702_, 7, v_onAlt_2689_);
lean_closure_set(v___f_2702_, 8, v_next_2690_);
lean_closure_set(v___f_2702_, 9, v_toBind_2691_);
lean_closure_set(v___f_2702_, 10, v___x_2692_);
lean_closure_set(v___f_2702_, 11, v___f_2693_);
lean_closure_set(v___f_2702_, 12, v_fst_2694_);
lean_closure_set(v___f_2702_, 13, v_inst_2695_);
lean_closure_set(v___f_2702_, 14, v_inst_2696_);
v___x_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_numDiscrEqs_2697_);
v___x_2704_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2695_, v_inst_2696_, v_altType_2699_, v___x_2703_, v___f_2702_, v___x_2685_, v___x_2685_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2705_ = _args[0];
lean_object* v_ys_2706_ = _args[1];
lean_object* v___x_2707_ = _args[2];
lean_object* v_useSplitter_2708_ = _args[3];
lean_object* v_inst_2709_ = _args[4];
lean_object* v_args_2710_ = _args[5];
lean_object* v_onAlt_2711_ = _args[6];
lean_object* v_next_2712_ = _args[7];
lean_object* v_toBind_2713_ = _args[8];
lean_object* v___x_2714_ = _args[9];
lean_object* v___f_2715_ = _args[10];
lean_object* v_fst_2716_ = _args[11];
lean_object* v_inst_2717_ = _args[12];
lean_object* v_inst_2718_ = _args[13];
lean_object* v_numDiscrEqs_2719_ = _args[14];
lean_object* v_ys2_2720_ = _args[15];
lean_object* v_altType_2721_ = _args[16];
_start:
{
uint8_t v___x_13484__boxed_2722_; uint8_t v_useSplitter_boxed_2723_; lean_object* v_res_2724_; 
v___x_13484__boxed_2722_ = lean_unbox(v___x_2707_);
v_useSplitter_boxed_2723_ = lean_unbox(v_useSplitter_2708_);
v_res_2724_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_toMonadExceptOf_2705_, v_ys_2706_, v___x_13484__boxed_2722_, v_useSplitter_boxed_2723_, v_inst_2709_, v_args_2710_, v_onAlt_2711_, v_next_2712_, v_toBind_2713_, v___x_2714_, v___f_2715_, v_fst_2716_, v_inst_2717_, v_inst_2718_, v_numDiscrEqs_2719_, v_ys2_2720_, v_altType_2721_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v_numOverlaps_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v___f_2728_, uint8_t v___x_2729_, lean_object* v_toBind_2730_, lean_object* v___f_2731_, lean_object* v_altType_2732_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_numOverlaps_2725_);
v___x_2734_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2726_, v_inst_2727_, v_altType_2732_, v___x_2733_, v___f_2728_, v___x_2729_, v___x_2729_);
v___x_2735_ = lean_apply_4(v_toBind_2730_, lean_box(0), lean_box(0), v___x_2734_, v___f_2731_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v_numOverlaps_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v___f_2739_, lean_object* v___x_2740_, lean_object* v_toBind_2741_, lean_object* v___f_2742_, lean_object* v_altType_2743_){
_start:
{
uint8_t v___x_13515__boxed_2744_; lean_object* v_res_2745_; 
v___x_13515__boxed_2744_ = lean_unbox(v___x_2740_);
v_res_2745_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v_numOverlaps_2736_, v_inst_2737_, v_inst_2738_, v___f_2739_, v___x_13515__boxed_2744_, v_toBind_2741_, v___f_2742_, v_altType_2743_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2746_, lean_object* v_altType_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_apply_1(v___f_2746_, v_altType_2747_);
return v___x_2748_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2753_ = lean_box(0);
v___x_2754_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2755_ = l_Lean_mkConst(v___x_2754_, v___x_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(uint8_t v_hasUnitThunk_2756_, lean_object* v_toPure_2757_, lean_object* v_toBind_2758_, lean_object* v___f_2759_, lean_object* v___x_2760_, lean_object* v_inst_2761_, lean_object* v___f_2762_, lean_object* v_altType_2763_){
_start:
{
if (v_hasUnitThunk_2756_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
lean_dec(v___f_2762_);
lean_dec(v_inst_2761_);
v___x_2764_ = lean_apply_2(v_toPure_2757_, lean_box(0), v_altType_2763_);
v___x_2765_ = lean_apply_4(v_toBind_2758_, lean_box(0), lean_box(0), v___x_2764_, v___f_2759_);
return v___x_2765_;
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_dec(v___f_2759_);
lean_dec(v_toPure_2757_);
v___x_2766_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2767_ = lean_mk_empty_array_with_capacity(v___x_2760_);
v___x_2768_ = lean_array_push(v___x_2767_, v___x_2766_);
v___x_2769_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2769_, 0, v_altType_2763_);
lean_closure_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = lean_apply_2(v_inst_2761_, lean_box(0), v___x_2769_);
v___x_2771_ = lean_apply_4(v_toBind_2758_, lean_box(0), lean_box(0), v___x_2770_, v___f_2762_);
return v___x_2771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v_hasUnitThunk_2772_, lean_object* v_toPure_2773_, lean_object* v_toBind_2774_, lean_object* v___f_2775_, lean_object* v___x_2776_, lean_object* v_inst_2777_, lean_object* v___f_2778_, lean_object* v_altType_2779_){
_start:
{
uint8_t v_hasUnitThunk_boxed_2780_; lean_object* v_res_2781_; 
v_hasUnitThunk_boxed_2780_ = lean_unbox(v_hasUnitThunk_2772_);
v_res_2781_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v_hasUnitThunk_boxed_2780_, v_toPure_2773_, v_toBind_2774_, v___f_2775_, v___x_2776_, v_inst_2777_, v___f_2778_, v_altType_2779_);
lean_dec(v___x_2776_);
return v_res_2781_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2785_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2786_ = lean_unsigned_to_nat(8u);
v___x_2787_ = lean_unsigned_to_nat(363u);
v___x_2788_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2789_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2790_ = l_mkPanicMessageWithDecl(v___x_2789_, v___x_2788_, v___x_2787_, v___x_2786_, v___x_2785_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2791_, lean_object* v___x_2792_, lean_object* v_toMonadExceptOf_2793_, uint8_t v___x_2794_, uint8_t v_useSplitter_2795_, lean_object* v_inst_2796_, lean_object* v_onAlt_2797_, lean_object* v_next_2798_, lean_object* v_toBind_2799_, lean_object* v___x_2800_, lean_object* v___f_2801_, lean_object* v_fst_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_numDiscrEqs_2805_, lean_object* v___f_2806_, lean_object* v_toPure_2807_, lean_object* v___x_2808_, lean_object* v___x_2809_, lean_object* v_ys_2810_, lean_object* v_args_2811_){
_start:
{
lean_object* v_numFields_2812_; lean_object* v_numOverlaps_2813_; uint8_t v_hasUnitThunk_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_numFields_2812_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_numFields_2812_);
v_numOverlaps_2813_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_numOverlaps_2813_);
v_hasUnitThunk_2814_ = lean_ctor_get_uint8(v___x_2791_, sizeof(void*)*2);
lean_dec_ref(v___x_2791_);
v___x_2815_ = lean_array_get_size(v_ys_2810_);
v___x_2816_ = lean_nat_dec_eq(v___x_2815_, v_numFields_2812_);
lean_dec(v_numFields_2812_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec(v_numOverlaps_2813_);
lean_dec_ref(v_args_2811_);
lean_dec_ref(v_ys_2810_);
lean_dec_ref(v___x_2809_);
lean_dec(v___x_2808_);
lean_dec(v_toPure_2807_);
lean_dec(v___f_2806_);
lean_dec(v_numDiscrEqs_2805_);
lean_dec_ref(v_inst_2804_);
lean_dec_ref(v_inst_2803_);
lean_dec(v_fst_2802_);
lean_dec(v___f_2801_);
lean_dec_ref(v___x_2800_);
lean_dec(v_toBind_2799_);
lean_dec(v_next_2798_);
lean_dec(v_onAlt_2797_);
lean_dec(v_inst_2796_);
lean_dec_ref(v_toMonadExceptOf_2793_);
v___x_2817_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2818_ = l_panic___redArg(v___x_2792_, v___x_2817_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; lean_object* v___f_2823_; lean_object* v___f_2824_; lean_object* v___x_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2819_ = lean_box(v___x_2794_);
v___x_2820_ = lean_box(v_useSplitter_2795_);
lean_inc_ref(v_inst_2804_);
lean_inc_ref(v_inst_2803_);
lean_inc_n(v_toBind_2799_, 3);
lean_inc_n(v_inst_2796_, 2);
lean_inc_ref(v_ys_2810_);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2821_, 0, v_toMonadExceptOf_2793_);
lean_closure_set(v___f_2821_, 1, v_ys_2810_);
lean_closure_set(v___f_2821_, 2, v___x_2819_);
lean_closure_set(v___f_2821_, 3, v___x_2820_);
lean_closure_set(v___f_2821_, 4, v_inst_2796_);
lean_closure_set(v___f_2821_, 5, v_args_2811_);
lean_closure_set(v___f_2821_, 6, v_onAlt_2797_);
lean_closure_set(v___f_2821_, 7, v_next_2798_);
lean_closure_set(v___f_2821_, 8, v_toBind_2799_);
lean_closure_set(v___f_2821_, 9, v___x_2800_);
lean_closure_set(v___f_2821_, 10, v___f_2801_);
lean_closure_set(v___f_2821_, 11, v_fst_2802_);
lean_closure_set(v___f_2821_, 12, v_inst_2803_);
lean_closure_set(v___f_2821_, 13, v_inst_2804_);
lean_closure_set(v___f_2821_, 14, v_numDiscrEqs_2805_);
v___x_2822_ = lean_box(v___x_2794_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2823_, 0, v_numOverlaps_2813_);
lean_closure_set(v___f_2823_, 1, v_inst_2803_);
lean_closure_set(v___f_2823_, 2, v_inst_2804_);
lean_closure_set(v___f_2823_, 3, v___f_2821_);
lean_closure_set(v___f_2823_, 4, v___x_2822_);
lean_closure_set(v___f_2823_, 5, v_toBind_2799_);
lean_closure_set(v___f_2823_, 6, v___f_2806_);
v___f_2824_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2824_, 0, v___f_2823_);
v___x_2825_ = lean_box(v_hasUnitThunk_2814_);
lean_inc_ref(v___f_2824_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2826_, 0, v___x_2825_);
lean_closure_set(v___f_2826_, 1, v_toPure_2807_);
lean_closure_set(v___f_2826_, 2, v_toBind_2799_);
lean_closure_set(v___f_2826_, 3, v___f_2824_);
lean_closure_set(v___f_2826_, 4, v___x_2808_);
lean_closure_set(v___f_2826_, 5, v_inst_2796_);
lean_closure_set(v___f_2826_, 6, v___f_2824_);
v___x_2827_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2827_, 0, v___x_2809_);
lean_closure_set(v___x_2827_, 1, v_ys_2810_);
v___x_2828_ = lean_apply_2(v_inst_2796_, lean_box(0), v___x_2827_);
v___x_2829_ = lean_apply_4(v_toBind_2799_, lean_box(0), lean_box(0), v___x_2828_, v___f_2826_);
return v___x_2829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2830_ = _args[0];
lean_object* v___x_2831_ = _args[1];
lean_object* v_toMonadExceptOf_2832_ = _args[2];
lean_object* v___x_2833_ = _args[3];
lean_object* v_useSplitter_2834_ = _args[4];
lean_object* v_inst_2835_ = _args[5];
lean_object* v_onAlt_2836_ = _args[6];
lean_object* v_next_2837_ = _args[7];
lean_object* v_toBind_2838_ = _args[8];
lean_object* v___x_2839_ = _args[9];
lean_object* v___f_2840_ = _args[10];
lean_object* v_fst_2841_ = _args[11];
lean_object* v_inst_2842_ = _args[12];
lean_object* v_inst_2843_ = _args[13];
lean_object* v_numDiscrEqs_2844_ = _args[14];
lean_object* v___f_2845_ = _args[15];
lean_object* v_toPure_2846_ = _args[16];
lean_object* v___x_2847_ = _args[17];
lean_object* v___x_2848_ = _args[18];
lean_object* v_ys_2849_ = _args[19];
lean_object* v_args_2850_ = _args[20];
_start:
{
uint8_t v___x_13607__boxed_2851_; uint8_t v_useSplitter_boxed_2852_; lean_object* v_res_2853_; 
v___x_13607__boxed_2851_ = lean_unbox(v___x_2833_);
v_useSplitter_boxed_2852_ = lean_unbox(v_useSplitter_2834_);
v_res_2853_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2830_, v___x_2831_, v_toMonadExceptOf_2832_, v___x_13607__boxed_2851_, v_useSplitter_boxed_2852_, v_inst_2835_, v_onAlt_2836_, v_next_2837_, v_toBind_2838_, v___x_2839_, v___f_2840_, v_fst_2841_, v_inst_2842_, v_inst_2843_, v_numDiscrEqs_2844_, v___f_2845_, v_toPure_2846_, v___x_2847_, v___x_2848_, v_ys_2849_, v_args_2850_);
lean_dec(v___x_2831_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v_fst_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v___x_2857_, lean_object* v___x_2858_, lean_object* v___x_2859_, lean_object* v_toPure_2860_, lean_object* v_alt_x27_2861_){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2862_ = lean_array_push(v_fst_2854_, v_alt_x27_2861_);
v___x_2863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2855_);
lean_ctor_set(v___x_2863_, 1, v___x_2856_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2857_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2858_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2859_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2862_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
v___x_2869_ = lean_apply_2(v_toPure_2860_, lean_box(0), v___x_2868_);
return v___x_2869_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2871_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0));
v___x_2872_ = lean_unsigned_to_nat(6u);
v___x_2873_ = lean_unsigned_to_nat(361u);
v___x_2874_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2875_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2876_ = l_mkPanicMessageWithDecl(v___x_2875_, v___x_2874_, v___x_2873_, v___x_2872_, v___x_2871_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2877_, lean_object* v_toPure_2878_, lean_object* v_toBind_2879_, lean_object* v___f_2880_, lean_object* v___x_2881_, lean_object* v___x_2882_, lean_object* v_inst_2883_, lean_object* v___x_2884_, lean_object* v_toMonadExceptOf_2885_, uint8_t v___x_2886_, uint8_t v_useSplitter_2887_, lean_object* v_onAlt_2888_, lean_object* v___f_2889_, lean_object* v_fst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_numDiscrEqs_2893_, lean_object* v_next_2894_, lean_object* v_acc_2895_, lean_object* v_h_2896_, lean_object* v_G_2897_){
_start:
{
uint8_t v___x_2898_; 
v___x_2898_ = lean_nat_dec_lt(v_next_2894_, v___x_2877_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec(v_G_2897_);
lean_dec(v_next_2894_);
lean_dec(v_numDiscrEqs_2893_);
lean_dec_ref(v_inst_2892_);
lean_dec_ref(v_inst_2891_);
lean_dec(v_fst_2890_);
lean_dec(v___f_2889_);
lean_dec(v_onAlt_2888_);
lean_dec_ref(v_toMonadExceptOf_2885_);
lean_dec(v___x_2884_);
lean_dec(v_inst_2883_);
lean_dec(v___f_2880_);
lean_dec(v_toBind_2879_);
v___x_2899_ = lean_apply_2(v_toPure_2878_, lean_box(0), v_acc_2895_);
return v___x_2899_;
}
else
{
lean_object* v_snd_2900_; lean_object* v_snd_2901_; lean_object* v_snd_2902_; lean_object* v_snd_2903_; lean_object* v_snd_2904_; lean_object* v_fst_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_3115_; 
v_snd_2900_ = lean_ctor_get(v_acc_2895_, 1);
lean_inc(v_snd_2900_);
v_snd_2901_ = lean_ctor_get(v_snd_2900_, 1);
lean_inc(v_snd_2901_);
v_snd_2902_ = lean_ctor_get(v_snd_2901_, 1);
lean_inc(v_snd_2902_);
v_snd_2903_ = lean_ctor_get(v_snd_2902_, 1);
lean_inc(v_snd_2903_);
v_snd_2904_ = lean_ctor_get(v_snd_2903_, 1);
lean_inc(v_snd_2904_);
v_fst_2905_ = lean_ctor_get(v_acc_2895_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_acc_2895_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v_acc_2895_, 1);
lean_dec(v_unused_3116_);
v___x_2907_ = v_acc_2895_;
v_isShared_2908_ = v_isSharedCheck_3115_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_fst_2905_);
lean_dec(v_acc_2895_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_3115_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v_fst_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_3113_; 
v_fst_2909_ = lean_ctor_get(v_snd_2900_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_snd_2900_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v_snd_2900_, 1);
lean_dec(v_unused_3114_);
v___x_2911_ = v_snd_2900_;
v_isShared_2912_ = v_isSharedCheck_3113_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_fst_2909_);
lean_dec(v_snd_2900_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_3113_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v_fst_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_3111_; 
v_fst_2913_ = lean_ctor_get(v_snd_2901_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_snd_2901_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v_snd_2901_, 1);
lean_dec(v_unused_3112_);
v___x_2915_ = v_snd_2901_;
v_isShared_2916_ = v_isSharedCheck_3111_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_fst_2913_);
lean_dec(v_snd_2901_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_3111_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v_fst_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_3109_; 
v_fst_2917_ = lean_ctor_get(v_snd_2902_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_snd_2902_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v_snd_2902_, 1);
lean_dec(v_unused_3110_);
v___x_2919_ = v_snd_2902_;
v_isShared_2920_ = v_isSharedCheck_3109_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_fst_2917_);
lean_dec(v_snd_2902_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_3109_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_fst_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_3107_; 
v_fst_2921_ = lean_ctor_get(v_snd_2903_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_snd_2903_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v_snd_2903_, 1);
lean_dec(v_unused_3108_);
v___x_2923_ = v_snd_2903_;
v_isShared_2924_ = v_isSharedCheck_3107_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_fst_2921_);
lean_dec(v_snd_2903_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_3107_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v_array_2925_; lean_object* v_start_2926_; lean_object* v_stop_2927_; lean_object* v___f_2928_; lean_object* v___y_2930_; uint8_t v___x_2933_; 
v_array_2925_ = lean_ctor_get(v_snd_2904_, 0);
v_start_2926_ = lean_ctor_get(v_snd_2904_, 1);
v_stop_2927_ = lean_ctor_get(v_snd_2904_, 2);
lean_inc(v_next_2894_);
lean_inc(v_toPure_2878_);
v___f_2928_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_2928_, 0, v_toPure_2878_);
lean_closure_set(v___f_2928_, 1, v_next_2894_);
lean_closure_set(v___f_2928_, 2, v_G_2897_);
v___x_2933_ = lean_nat_dec_lt(v_start_2926_, v_stop_2927_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2935_; 
lean_dec(v_next_2894_);
lean_dec(v_numDiscrEqs_2893_);
lean_dec_ref(v_inst_2892_);
lean_dec_ref(v_inst_2891_);
lean_dec(v_fst_2890_);
lean_dec(v___f_2889_);
lean_dec(v_onAlt_2888_);
lean_dec_ref(v_toMonadExceptOf_2885_);
lean_dec(v___x_2884_);
lean_dec(v_inst_2883_);
if (v_isShared_2924_ == 0)
{
v___x_2935_ = v___x_2923_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_fst_2921_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v_snd_2904_);
v___x_2935_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
lean_object* v___x_2937_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_2935_);
v___x_2937_ = v___x_2919_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_fst_2917_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2939_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_2937_);
v___x_2939_ = v___x_2915_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_fst_2913_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2941_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2939_);
v___x_2941_ = v___x_2911_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_fst_2909_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2943_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2941_);
v___x_2943_ = v___x_2907_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_fst_2905_);
lean_ctor_set(v_reuseFailAlloc_2946_, 1, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = lean_apply_2(v_toPure_2878_, lean_box(0), v___x_2944_);
v___y_2930_ = v___x_2945_;
goto v___jp_2929_;
}
}
}
}
}
}
else
{
lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_3103_; 
lean_inc(v_stop_2927_);
lean_inc(v_start_2926_);
lean_inc_ref(v_array_2925_);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_snd_2904_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; lean_object* v_unused_3105_; lean_object* v_unused_3106_; 
v_unused_3104_ = lean_ctor_get(v_snd_2904_, 2);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v_snd_2904_, 1);
lean_dec(v_unused_3105_);
v_unused_3106_ = lean_ctor_get(v_snd_2904_, 0);
lean_dec(v_unused_3106_);
v___x_2952_ = v_snd_2904_;
v_isShared_2953_ = v_isSharedCheck_3103_;
goto v_resetjp_2951_;
}
else
{
lean_dec(v_snd_2904_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_3103_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v_array_2954_; lean_object* v_start_2955_; lean_object* v_stop_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v_array_2954_ = lean_ctor_get(v_fst_2921_, 0);
v_start_2955_ = lean_ctor_get(v_fst_2921_, 1);
v_stop_2956_ = lean_ctor_get(v_fst_2921_, 2);
v___x_2957_ = lean_array_fget(v_array_2925_, v_start_2926_);
v___x_2958_ = lean_unsigned_to_nat(1u);
v___x_2959_ = lean_nat_add(v_start_2926_, v___x_2958_);
lean_dec(v_start_2926_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 1, v___x_2959_);
v___x_2961_ = v___x_2952_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_array_2925_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3102_, 2, v_stop_2927_);
v___x_2961_ = v_reuseFailAlloc_3102_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
uint8_t v___x_2962_; 
v___x_2962_ = lean_nat_dec_lt(v_start_2955_, v_stop_2956_);
if (v___x_2962_ == 0)
{
lean_object* v___x_2964_; 
lean_dec(v___x_2957_);
lean_dec(v_next_2894_);
lean_dec(v_numDiscrEqs_2893_);
lean_dec_ref(v_inst_2892_);
lean_dec_ref(v_inst_2891_);
lean_dec(v_fst_2890_);
lean_dec(v___f_2889_);
lean_dec(v_onAlt_2888_);
lean_dec_ref(v_toMonadExceptOf_2885_);
lean_dec(v___x_2884_);
lean_dec(v_inst_2883_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2961_);
v___x_2964_ = v___x_2923_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_fst_2921_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2961_);
v___x_2964_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2966_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_2964_);
v___x_2966_ = v___x_2919_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_fst_2917_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2964_);
v___x_2966_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_2966_);
v___x_2968_ = v___x_2915_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_fst_2913_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2970_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2968_);
v___x_2970_ = v___x_2911_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_fst_2909_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2970_);
v___x_2972_ = v___x_2907_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_fst_2905_);
lean_ctor_set(v_reuseFailAlloc_2975_, 1, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
v___x_2974_ = lean_apply_2(v_toPure_2878_, lean_box(0), v___x_2973_);
v___y_2930_ = v___x_2974_;
goto v___jp_2929_;
}
}
}
}
}
}
else
{
lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_3098_; 
lean_inc(v_stop_2956_);
lean_inc(v_start_2955_);
lean_inc_ref(v_array_2954_);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_fst_2921_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; lean_object* v_unused_3100_; lean_object* v_unused_3101_; 
v_unused_3099_ = lean_ctor_get(v_fst_2921_, 2);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_fst_2921_, 1);
lean_dec(v_unused_3100_);
v_unused_3101_ = lean_ctor_get(v_fst_2921_, 0);
lean_dec(v_unused_3101_);
v___x_2981_ = v_fst_2921_;
v_isShared_2982_ = v_isSharedCheck_3098_;
goto v_resetjp_2980_;
}
else
{
lean_dec(v_fst_2921_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_3098_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v_array_2983_; lean_object* v_start_2984_; lean_object* v_stop_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2989_; 
v_array_2983_ = lean_ctor_get(v_fst_2917_, 0);
v_start_2984_ = lean_ctor_get(v_fst_2917_, 1);
v_stop_2985_ = lean_ctor_get(v_fst_2917_, 2);
v___x_2986_ = lean_array_fget(v_array_2954_, v_start_2955_);
v___x_2987_ = lean_nat_add(v_start_2955_, v___x_2958_);
lean_dec(v_start_2955_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 1, v___x_2987_);
v___x_2989_ = v___x_2981_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_array_2954_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_2987_);
lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_stop_2956_);
v___x_2989_ = v_reuseFailAlloc_3097_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
uint8_t v___x_2990_; 
v___x_2990_ = lean_nat_dec_lt(v_start_2984_, v_stop_2985_);
if (v___x_2990_ == 0)
{
lean_object* v___x_2992_; 
lean_dec(v___x_2986_);
lean_dec(v___x_2957_);
lean_dec(v_next_2894_);
lean_dec(v_numDiscrEqs_2893_);
lean_dec_ref(v_inst_2892_);
lean_dec_ref(v_inst_2891_);
lean_dec(v_fst_2890_);
lean_dec(v___f_2889_);
lean_dec(v_onAlt_2888_);
lean_dec_ref(v_toMonadExceptOf_2885_);
lean_dec(v___x_2884_);
lean_dec(v_inst_2883_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2961_);
lean_ctor_set(v___x_2923_, 0, v___x_2989_);
v___x_2992_ = v___x_2923_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2961_);
v___x_2992_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2994_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_2992_);
v___x_2994_ = v___x_2919_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_fst_2917_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2996_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_2994_);
v___x_2996_ = v___x_2915_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_fst_2913_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2998_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_2996_);
v___x_2998_ = v___x_2911_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_fst_2909_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_3000_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2998_);
v___x_3000_ = v___x_2907_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_fst_2905_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
v___x_3002_ = lean_apply_2(v_toPure_2878_, lean_box(0), v___x_3001_);
v___y_2930_ = v___x_3002_;
goto v___jp_2929_;
}
}
}
}
}
}
else
{
lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3093_; 
lean_inc(v_stop_2985_);
lean_inc(v_start_2984_);
lean_inc_ref(v_array_2983_);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_fst_2917_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; lean_object* v_unused_3095_; lean_object* v_unused_3096_; 
v_unused_3094_ = lean_ctor_get(v_fst_2917_, 2);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_fst_2917_, 1);
lean_dec(v_unused_3095_);
v_unused_3096_ = lean_ctor_get(v_fst_2917_, 0);
lean_dec(v_unused_3096_);
v___x_3009_ = v_fst_2917_;
v_isShared_3010_ = v_isSharedCheck_3093_;
goto v_resetjp_3008_;
}
else
{
lean_dec(v_fst_2917_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3093_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v_array_3011_; lean_object* v_start_3012_; lean_object* v_stop_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3017_; 
v_array_3011_ = lean_ctor_get(v_fst_2913_, 0);
v_start_3012_ = lean_ctor_get(v_fst_2913_, 1);
v_stop_3013_ = lean_ctor_get(v_fst_2913_, 2);
v___x_3014_ = lean_array_fget(v_array_2983_, v_start_2984_);
v___x_3015_ = lean_nat_add(v_start_2984_, v___x_2958_);
lean_dec(v_start_2984_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___x_3015_);
v___x_3017_ = v___x_3009_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_array_2983_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3015_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v_stop_2985_);
v___x_3017_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
uint8_t v___x_3018_; 
v___x_3018_ = lean_nat_dec_lt(v_start_3012_, v_stop_3013_);
if (v___x_3018_ == 0)
{
lean_object* v___x_3020_; 
lean_dec(v___x_3014_);
lean_dec(v___x_2986_);
lean_dec(v___x_2957_);
lean_dec(v_next_2894_);
lean_dec(v_numDiscrEqs_2893_);
lean_dec_ref(v_inst_2892_);
lean_dec_ref(v_inst_2891_);
lean_dec(v_fst_2890_);
lean_dec(v___f_2889_);
lean_dec(v_onAlt_2888_);
lean_dec_ref(v_toMonadExceptOf_2885_);
lean_dec(v___x_2884_);
lean_dec(v_inst_2883_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2961_);
lean_ctor_set(v___x_2923_, 0, v___x_2989_);
v___x_3020_ = v___x_2923_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_2961_);
v___x_3020_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3022_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_3020_);
lean_ctor_set(v___x_2919_, 0, v___x_3017_);
v___x_3022_ = v___x_2919_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v___x_3020_);
v___x_3022_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3024_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_3022_);
v___x_3024_ = v___x_2915_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_fst_2913_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_3024_);
v___x_3026_ = v___x_2911_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_fst_2909_);
lean_ctor_set(v_reuseFailAlloc_3032_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_3026_);
v___x_3028_ = v___x_2907_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_fst_2905_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
v___x_3030_ = lean_apply_2(v_toPure_2878_, lean_box(0), v___x_3029_);
v___y_2930_ = v___x_3030_;
goto v___jp_2929_;
}
}
}
}
}
}
else
{
lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3088_; 
lean_inc(v_stop_3013_);
lean_inc(v_start_3012_);
lean_inc_ref(v_array_3011_);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_fst_2913_);
if (v_isSharedCheck_3088_ == 0)
{
lean_object* v_unused_3089_; lean_object* v_unused_3090_; lean_object* v_unused_3091_; 
v_unused_3089_ = lean_ctor_get(v_fst_2913_, 2);
lean_dec(v_unused_3089_);
v_unused_3090_ = lean_ctor_get(v_fst_2913_, 1);
lean_dec(v_unused_3090_);
v_unused_3091_ = lean_ctor_get(v_fst_2913_, 0);
lean_dec(v_unused_3091_);
v___x_3037_ = v_fst_2913_;
v_isShared_3038_ = v_isSharedCheck_3088_;
goto v_resetjp_3036_;
}
else
{
lean_dec(v_fst_2913_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3088_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v_array_3039_; lean_object* v_start_3040_; lean_object* v_stop_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3045_; 
v_array_3039_ = lean_ctor_get(v_fst_2909_, 0);
v_start_3040_ = lean_ctor_get(v_fst_2909_, 1);
v_stop_3041_ = lean_ctor_get(v_fst_2909_, 2);
v___x_3042_ = lean_array_fget(v_array_3011_, v_start_3012_);
v___x_3043_ = lean_nat_add(v_start_3012_, v___x_2958_);
lean_dec(v_start_3012_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3043_);
v___x_3045_ = v___x_3037_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_array_3011_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3087_, 2, v_stop_3013_);
v___x_3045_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
uint8_t v___x_3046_; 
v___x_3046_ = lean_nat_dec_lt(v_start_3040_, v_stop_3041_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3048_; 
lean_dec(v___x_3042_);
lean_dec(v___x_3014_);
lean_dec(v___x_2986_);
lean_dec(v___x_2957_);
lean_dec(v_next_2894_);
lean_dec(v_numDiscrEqs_2893_);
lean_dec_ref(v_inst_2892_);
lean_dec_ref(v_inst_2891_);
lean_dec(v_fst_2890_);
lean_dec(v___f_2889_);
lean_dec(v_onAlt_2888_);
lean_dec_ref(v_toMonadExceptOf_2885_);
lean_dec(v___x_2884_);
lean_dec(v_inst_2883_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2961_);
lean_ctor_set(v___x_2923_, 0, v___x_2989_);
v___x_3048_ = v___x_2923_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_2961_);
v___x_3048_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3050_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_3048_);
lean_ctor_set(v___x_2919_, 0, v___x_3017_);
v___x_3050_ = v___x_2919_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3052_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_3050_);
lean_ctor_set(v___x_2915_, 0, v___x_3045_);
v___x_3052_ = v___x_2915_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 1, v___x_3052_);
v___x_3054_ = v___x_2911_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_fst_2909_);
lean_ctor_set(v_reuseFailAlloc_3060_, 1, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3056_; 
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_3054_);
v___x_3056_ = v___x_2907_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_fst_2905_);
lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
v___x_3058_ = lean_apply_2(v_toPure_2878_, lean_box(0), v___x_3057_);
v___y_2930_ = v___x_3058_;
goto v___jp_2929_;
}
}
}
}
}
}
else
{
lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3083_; 
lean_inc(v_stop_3041_);
lean_inc(v_start_3040_);
lean_inc_ref(v_array_3039_);
lean_del_object(v___x_2923_);
lean_del_object(v___x_2919_);
lean_del_object(v___x_2915_);
lean_del_object(v___x_2911_);
lean_del_object(v___x_2907_);
v_isSharedCheck_3083_ = !lean_is_exclusive(v_fst_2909_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; lean_object* v_unused_3085_; lean_object* v_unused_3086_; 
v_unused_3084_ = lean_ctor_get(v_fst_2909_, 2);
lean_dec(v_unused_3084_);
v_unused_3085_ = lean_ctor_get(v_fst_2909_, 1);
lean_dec(v_unused_3085_);
v_unused_3086_ = lean_ctor_get(v_fst_2909_, 0);
lean_dec(v_unused_3086_);
v___x_3065_ = v_fst_2909_;
v_isShared_3066_ = v_isSharedCheck_3083_;
goto v_resetjp_3064_;
}
else
{
lean_dec(v_fst_2909_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3083_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v_numOverlaps_3067_; uint8_t v___x_3068_; 
v_numOverlaps_3067_ = lean_ctor_get(v___x_3042_, 1);
v___x_3068_ = lean_nat_dec_eq(v_numOverlaps_3067_, v___x_2881_);
if (v___x_3068_ == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
lean_del_object(v___x_3065_);
lean_dec_ref(v___x_3045_);
lean_dec(v___x_3042_);
lean_dec(v_stop_3041_);
lean_dec(v_start_3040_);
lean_dec_ref(v_array_3039_);
lean_dec_ref(v___x_3017_);
lean_dec(v___x_3014_);
lean_dec_ref(v___x_2989_);
lean_dec(v___x_2986_);
lean_dec_ref(v___x_2961_);
lean_dec(v___x_2957_);
lean_dec(v_fst_2905_);
lean_dec(v_next_2894_);
lean_dec(v_numDiscrEqs_2893_);
lean_dec_ref(v_inst_2892_);
lean_dec_ref(v_inst_2891_);
lean_dec(v_fst_2890_);
lean_dec(v___f_2889_);
lean_dec(v_onAlt_2888_);
lean_dec_ref(v_toMonadExceptOf_2885_);
lean_dec(v___x_2884_);
lean_dec(v_inst_2883_);
lean_dec(v_toPure_2878_);
v___x_3069_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_3070_ = l_panic___redArg(v___x_2882_, v___x_3069_);
v___y_2930_ = v___x_3070_;
goto v___jp_2929_;
}
else
{
lean_object* v___f_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___f_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_inc(v_inst_2883_);
lean_inc_n(v_toPure_2878_, 2);
lean_inc(v___x_3014_);
v___f_3071_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_3071_, 0, v___x_3014_);
lean_closure_set(v___f_3071_, 1, v_toPure_2878_);
lean_closure_set(v___f_3071_, 2, v_inst_2883_);
v___x_3072_ = lean_array_fget_borrowed(v_array_3039_, v_start_3040_);
v___x_3073_ = lean_box(v___x_2886_);
v___x_3074_ = lean_box(v_useSplitter_2887_);
lean_inc_ref(v_inst_2892_);
lean_inc_ref(v_inst_2891_);
lean_inc(v___x_3072_);
lean_inc(v_toBind_2879_);
v___f_3075_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 21, 19);
lean_closure_set(v___f_3075_, 0, v___x_3014_);
lean_closure_set(v___f_3075_, 1, v___x_2884_);
lean_closure_set(v___f_3075_, 2, v_toMonadExceptOf_2885_);
lean_closure_set(v___f_3075_, 3, v___x_3073_);
lean_closure_set(v___f_3075_, 4, v___x_3074_);
lean_closure_set(v___f_3075_, 5, v_inst_2883_);
lean_closure_set(v___f_3075_, 6, v_onAlt_2888_);
lean_closure_set(v___f_3075_, 7, v_next_2894_);
lean_closure_set(v___f_3075_, 8, v_toBind_2879_);
lean_closure_set(v___f_3075_, 9, v___x_3072_);
lean_closure_set(v___f_3075_, 10, v___f_2889_);
lean_closure_set(v___f_3075_, 11, v_fst_2890_);
lean_closure_set(v___f_3075_, 12, v_inst_2891_);
lean_closure_set(v___f_3075_, 13, v_inst_2892_);
lean_closure_set(v___f_3075_, 14, v_numDiscrEqs_2893_);
lean_closure_set(v___f_3075_, 15, v___f_3071_);
lean_closure_set(v___f_3075_, 16, v_toPure_2878_);
lean_closure_set(v___f_3075_, 17, v___x_2958_);
lean_closure_set(v___f_3075_, 18, v___x_2957_);
v___x_3076_ = lean_nat_add(v_start_3040_, v___x_2958_);
lean_dec(v_start_3040_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 1, v___x_3076_);
v___x_3078_ = v___x_3065_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_array_3039_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v___x_3076_);
lean_ctor_set(v_reuseFailAlloc_3082_, 2, v_stop_3041_);
v___x_3078_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3079_, 0, v_fst_2905_);
lean_closure_set(v___f_3079_, 1, v___x_2989_);
lean_closure_set(v___f_3079_, 2, v___x_2961_);
lean_closure_set(v___f_3079_, 3, v___x_3017_);
lean_closure_set(v___f_3079_, 4, v___x_3045_);
lean_closure_set(v___f_3079_, 5, v___x_3078_);
lean_closure_set(v___f_3079_, 6, v_toPure_2878_);
v___x_3080_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2892_, v_inst_2891_, v___x_2986_, v___x_3042_, v___f_3075_);
lean_inc(v_toBind_2879_);
v___x_3081_ = lean_apply_4(v_toBind_2879_, lean_box(0), lean_box(0), v___x_3080_, v___f_3079_);
v___y_2930_ = v___x_3081_;
goto v___jp_2929_;
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
v___jp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
lean_inc(v_toBind_2879_);
v___x_2931_ = lean_apply_4(v_toBind_2879_, lean_box(0), lean_box(0), v___y_2930_, v___f_2880_);
v___x_2932_ = lean_apply_4(v_toBind_2879_, lean_box(0), lean_box(0), v___x_2931_, v___f_2928_);
return v___x_2932_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed(lean_object** _args){
lean_object* v___x_3117_ = _args[0];
lean_object* v_toPure_3118_ = _args[1];
lean_object* v_toBind_3119_ = _args[2];
lean_object* v___f_3120_ = _args[3];
lean_object* v___x_3121_ = _args[4];
lean_object* v___x_3122_ = _args[5];
lean_object* v_inst_3123_ = _args[6];
lean_object* v___x_3124_ = _args[7];
lean_object* v_toMonadExceptOf_3125_ = _args[8];
lean_object* v___x_3126_ = _args[9];
lean_object* v_useSplitter_3127_ = _args[10];
lean_object* v_onAlt_3128_ = _args[11];
lean_object* v___f_3129_ = _args[12];
lean_object* v_fst_3130_ = _args[13];
lean_object* v_inst_3131_ = _args[14];
lean_object* v_inst_3132_ = _args[15];
lean_object* v_numDiscrEqs_3133_ = _args[16];
lean_object* v_next_3134_ = _args[17];
lean_object* v_acc_3135_ = _args[18];
lean_object* v_h_3136_ = _args[19];
lean_object* v_G_3137_ = _args[20];
_start:
{
uint8_t v___x_13725__boxed_3138_; uint8_t v_useSplitter_boxed_3139_; lean_object* v_res_3140_; 
v___x_13725__boxed_3138_ = lean_unbox(v___x_3126_);
v_useSplitter_boxed_3139_ = lean_unbox(v_useSplitter_3127_);
v_res_3140_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3117_, v_toPure_3118_, v_toBind_3119_, v___f_3120_, v___x_3121_, v___x_3122_, v_inst_3123_, v___x_3124_, v_toMonadExceptOf_3125_, v___x_13725__boxed_3138_, v_useSplitter_boxed_3139_, v_onAlt_3128_, v___f_3129_, v_fst_3130_, v_inst_3131_, v_inst_3132_, v_numDiscrEqs_3133_, v_next_3134_, v_acc_3135_, v_h_3136_, v_G_3137_);
lean_dec(v___x_3122_);
lean_dec(v___x_3121_);
lean_dec(v___x_3117_);
return v_res_3140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3141_, lean_object* v_numParams_3142_, lean_object* v_numDiscrs_3143_, lean_object* v_altInfos_3144_, lean_object* v_uElimPos_x3f_3145_, lean_object* v_snd_3146_, lean_object* v_overlaps_3147_, lean_object* v_splitterName_3148_, lean_object* v_matcherLevels_3149_, lean_object* v_params_x27_3150_, lean_object* v_fst_3151_, lean_object* v_discrs_x27_3152_, lean_object* v_fst_3153_, lean_object* v_toPure_3154_, lean_object* v_____do__lift_3155_){
_start:
{
lean_object* v_remaining_x27_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_remaining_x27_3156_ = l_Array_append___redArg(v_fst_3141_, v_____do__lift_3155_);
v___x_3157_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3157_, 0, v_numParams_3142_);
lean_ctor_set(v___x_3157_, 1, v_numDiscrs_3143_);
lean_ctor_set(v___x_3157_, 2, v_altInfos_3144_);
lean_ctor_set(v___x_3157_, 3, v_uElimPos_x3f_3145_);
lean_ctor_set(v___x_3157_, 4, v_snd_3146_);
lean_ctor_set(v___x_3157_, 5, v_overlaps_3147_);
v___x_3158_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
lean_ctor_set(v___x_3158_, 1, v_splitterName_3148_);
lean_ctor_set(v___x_3158_, 2, v_matcherLevels_3149_);
lean_ctor_set(v___x_3158_, 3, v_params_x27_3150_);
lean_ctor_set(v___x_3158_, 4, v_fst_3151_);
lean_ctor_set(v___x_3158_, 5, v_discrs_x27_3152_);
lean_ctor_set(v___x_3158_, 6, v_fst_3153_);
lean_ctor_set(v___x_3158_, 7, v_remaining_x27_3156_);
v___x_3159_ = lean_apply_2(v_toPure_3154_, lean_box(0), v___x_3158_);
return v___x_3159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3160_, lean_object* v_numParams_3161_, lean_object* v_numDiscrs_3162_, lean_object* v_altInfos_3163_, lean_object* v_uElimPos_x3f_3164_, lean_object* v_snd_3165_, lean_object* v_overlaps_3166_, lean_object* v_splitterName_3167_, lean_object* v_matcherLevels_3168_, lean_object* v_params_x27_3169_, lean_object* v_fst_3170_, lean_object* v_discrs_x27_3171_, lean_object* v_fst_3172_, lean_object* v_toPure_3173_, lean_object* v_____do__lift_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3160_, v_numParams_3161_, v_numDiscrs_3162_, v_altInfos_3163_, v_uElimPos_x3f_3164_, v_snd_3165_, v_overlaps_3166_, v_splitterName_3167_, v_matcherLevels_3168_, v_params_x27_3169_, v_fst_3170_, v_discrs_x27_3171_, v_fst_3172_, v_toPure_3173_, v_____do__lift_3174_);
lean_dec_ref(v_____do__lift_3174_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3176_, lean_object* v_numParams_3177_, lean_object* v_numDiscrs_3178_, lean_object* v_altInfos_3179_, lean_object* v_uElimPos_x3f_3180_, lean_object* v_snd_3181_, lean_object* v_overlaps_3182_, lean_object* v_splitterName_3183_, lean_object* v_matcherLevels_3184_, lean_object* v_params_x27_3185_, lean_object* v_fst_3186_, lean_object* v_discrs_x27_3187_, lean_object* v_toPure_3188_, lean_object* v_onRemaining_3189_, lean_object* v_remaining_3190_, lean_object* v_toBind_3191_, lean_object* v_____s_3192_){
_start:
{
lean_object* v_fst_3193_; lean_object* v___f_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_fst_3193_ = lean_ctor_get(v_____s_3192_, 0);
lean_inc(v_fst_3193_);
lean_dec_ref(v_____s_3192_);
v___f_3194_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3194_, 0, v_fst_3176_);
lean_closure_set(v___f_3194_, 1, v_numParams_3177_);
lean_closure_set(v___f_3194_, 2, v_numDiscrs_3178_);
lean_closure_set(v___f_3194_, 3, v_altInfos_3179_);
lean_closure_set(v___f_3194_, 4, v_uElimPos_x3f_3180_);
lean_closure_set(v___f_3194_, 5, v_snd_3181_);
lean_closure_set(v___f_3194_, 6, v_overlaps_3182_);
lean_closure_set(v___f_3194_, 7, v_splitterName_3183_);
lean_closure_set(v___f_3194_, 8, v_matcherLevels_3184_);
lean_closure_set(v___f_3194_, 9, v_params_x27_3185_);
lean_closure_set(v___f_3194_, 10, v_fst_3186_);
lean_closure_set(v___f_3194_, 11, v_discrs_x27_3187_);
lean_closure_set(v___f_3194_, 12, v_fst_3193_);
lean_closure_set(v___f_3194_, 13, v_toPure_3188_);
v___x_3195_ = lean_apply_1(v_onRemaining_3189_, v_remaining_3190_);
v___x_3196_ = lean_apply_4(v_toBind_3191_, lean_box(0), lean_box(0), v___x_3195_, v___f_3194_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3197_ = _args[0];
lean_object* v_numParams_3198_ = _args[1];
lean_object* v_numDiscrs_3199_ = _args[2];
lean_object* v_altInfos_3200_ = _args[3];
lean_object* v_uElimPos_x3f_3201_ = _args[4];
lean_object* v_snd_3202_ = _args[5];
lean_object* v_overlaps_3203_ = _args[6];
lean_object* v_splitterName_3204_ = _args[7];
lean_object* v_matcherLevels_3205_ = _args[8];
lean_object* v_params_x27_3206_ = _args[9];
lean_object* v_fst_3207_ = _args[10];
lean_object* v_discrs_x27_3208_ = _args[11];
lean_object* v_toPure_3209_ = _args[12];
lean_object* v_onRemaining_3210_ = _args[13];
lean_object* v_remaining_3211_ = _args[14];
lean_object* v_toBind_3212_ = _args[15];
lean_object* v_____s_3213_ = _args[16];
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3197_, v_numParams_3198_, v_numDiscrs_3199_, v_altInfos_3200_, v_uElimPos_x3f_3201_, v_snd_3202_, v_overlaps_3203_, v_splitterName_3204_, v_matcherLevels_3205_, v_params_x27_3206_, v_fst_3207_, v_discrs_x27_3208_, v_toPure_3209_, v_onRemaining_3210_, v_remaining_3211_, v_toBind_3212_, v_____s_3213_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3215_, lean_object* v_fst_3216_, lean_object* v_numParams_3217_, lean_object* v_numDiscrs_3218_, lean_object* v_altInfos_3219_, lean_object* v_uElimPos_x3f_3220_, lean_object* v_snd_3221_, lean_object* v_overlaps_3222_, lean_object* v_splitterName_3223_, lean_object* v_matcherLevels_3224_, lean_object* v_params_x27_3225_, lean_object* v_fst_3226_, lean_object* v_discrs_x27_3227_, lean_object* v_toPure_3228_, lean_object* v_onRemaining_3229_, lean_object* v_remaining_3230_, lean_object* v_toBind_3231_, lean_object* v_origAltTypes_3232_, lean_object* v_alts_3233_, lean_object* v___x_3234_, lean_object* v___x_3235_, lean_object* v_remaining_x27_3236_, lean_object* v___f_3237_, lean_object* v_altTypes_3238_){
_start:
{
lean_object* v_altInfos_3239_; lean_object* v___f_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
v_altInfos_3239_ = lean_ctor_get(v_splitterMatchInfo_3215_, 2);
lean_inc_ref(v_altInfos_3239_);
lean_dec_ref(v_splitterMatchInfo_3215_);
lean_inc(v_toBind_3231_);
lean_inc_ref(v_altInfos_3219_);
v___f_3240_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3240_, 0, v_fst_3216_);
lean_closure_set(v___f_3240_, 1, v_numParams_3217_);
lean_closure_set(v___f_3240_, 2, v_numDiscrs_3218_);
lean_closure_set(v___f_3240_, 3, v_altInfos_3219_);
lean_closure_set(v___f_3240_, 4, v_uElimPos_x3f_3220_);
lean_closure_set(v___f_3240_, 5, v_snd_3221_);
lean_closure_set(v___f_3240_, 6, v_overlaps_3222_);
lean_closure_set(v___f_3240_, 7, v_splitterName_3223_);
lean_closure_set(v___f_3240_, 8, v_matcherLevels_3224_);
lean_closure_set(v___f_3240_, 9, v_params_x27_3225_);
lean_closure_set(v___f_3240_, 10, v_fst_3226_);
lean_closure_set(v___f_3240_, 11, v_discrs_x27_3227_);
lean_closure_set(v___f_3240_, 12, v_toPure_3228_);
lean_closure_set(v___f_3240_, 13, v_onRemaining_3229_);
lean_closure_set(v___f_3240_, 14, v_remaining_3230_);
lean_closure_set(v___f_3240_, 15, v_toBind_3231_);
v___x_3241_ = lean_array_get_size(v_altInfos_3219_);
v___x_3242_ = lean_array_get_size(v_altInfos_3239_);
v___x_3243_ = lean_array_get_size(v_origAltTypes_3232_);
v___x_3244_ = lean_array_get_size(v_altTypes_3238_);
lean_inc_n(v___x_3234_, 5);
v___x_3245_ = l_Array_toSubarray___redArg(v_alts_3233_, v___x_3234_, v___x_3235_);
v___x_3246_ = l_Array_toSubarray___redArg(v_altInfos_3219_, v___x_3234_, v___x_3241_);
v___x_3247_ = l_Array_toSubarray___redArg(v_altInfos_3239_, v___x_3234_, v___x_3242_);
v___x_3248_ = l_Array_toSubarray___redArg(v_origAltTypes_3232_, v___x_3234_, v___x_3243_);
v___x_3249_ = l_Array_toSubarray___redArg(v_altTypes_3238_, v___x_3234_, v___x_3244_);
v___x_3250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___x_3251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3247_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3246_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3245_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v_remaining_x27_3236_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3237_, v___x_3234_, v___x_3254_, lean_box(0));
v___x_3256_ = lean_apply_4(v_toBind_3231_, lean_box(0), lean_box(0), v___x_3255_, v___f_3240_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3257_ = _args[0];
lean_object* v_fst_3258_ = _args[1];
lean_object* v_numParams_3259_ = _args[2];
lean_object* v_numDiscrs_3260_ = _args[3];
lean_object* v_altInfos_3261_ = _args[4];
lean_object* v_uElimPos_x3f_3262_ = _args[5];
lean_object* v_snd_3263_ = _args[6];
lean_object* v_overlaps_3264_ = _args[7];
lean_object* v_splitterName_3265_ = _args[8];
lean_object* v_matcherLevels_3266_ = _args[9];
lean_object* v_params_x27_3267_ = _args[10];
lean_object* v_fst_3268_ = _args[11];
lean_object* v_discrs_x27_3269_ = _args[12];
lean_object* v_toPure_3270_ = _args[13];
lean_object* v_onRemaining_3271_ = _args[14];
lean_object* v_remaining_3272_ = _args[15];
lean_object* v_toBind_3273_ = _args[16];
lean_object* v_origAltTypes_3274_ = _args[17];
lean_object* v_alts_3275_ = _args[18];
lean_object* v___x_3276_ = _args[19];
lean_object* v___x_3277_ = _args[20];
lean_object* v_remaining_x27_3278_ = _args[21];
lean_object* v___f_3279_ = _args[22];
lean_object* v_altTypes_3280_ = _args[23];
_start:
{
lean_object* v_res_3281_; 
v_res_3281_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3257_, v_fst_3258_, v_numParams_3259_, v_numDiscrs_3260_, v_altInfos_3261_, v_uElimPos_x3f_3262_, v_snd_3263_, v_overlaps_3264_, v_splitterName_3265_, v_matcherLevels_3266_, v_params_x27_3267_, v_fst_3268_, v_discrs_x27_3269_, v_toPure_3270_, v_onRemaining_3271_, v_remaining_3272_, v_toBind_3273_, v_origAltTypes_3274_, v_alts_3275_, v___x_3276_, v___x_3277_, v_remaining_x27_3278_, v___f_3279_, v_altTypes_3280_);
return v_res_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3282_, lean_object* v_aux2_3283_, lean_object* v_inst_3284_, lean_object* v_toBind_3285_, lean_object* v___f_3286_, lean_object* v_____r_3287_){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3288_, 0, v___x_3282_);
lean_closure_set(v___x_3288_, 1, v_aux2_3283_);
v___x_3289_ = lean_apply_2(v_inst_3284_, lean_box(0), v___x_3288_);
v___x_3290_ = lean_apply_4(v_toBind_3285_, lean_box(0), lean_box(0), v___x_3289_, v___f_3286_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3294_, lean_object* v_params_x27_3295_, lean_object* v_fst_3296_, lean_object* v_discrs_x27_3297_, lean_object* v_fst_3298_, lean_object* v_numParams_3299_, lean_object* v_numDiscrs_3300_, lean_object* v_altInfos_3301_, lean_object* v_uElimPos_x3f_3302_, lean_object* v_snd_3303_, lean_object* v_overlaps_3304_, lean_object* v_matcherLevels_3305_, lean_object* v_toPure_3306_, lean_object* v_onRemaining_3307_, lean_object* v_remaining_3308_, lean_object* v_toBind_3309_, lean_object* v_origAltTypes_3310_, lean_object* v_alts_3311_, lean_object* v___x_3312_, lean_object* v___x_3313_, lean_object* v_remaining_x27_3314_, lean_object* v___f_3315_, lean_object* v_inst_3316_, lean_object* v___x_3317_, uint8_t v___x_3318_, lean_object* v_liftWith_3319_, lean_object* v_restoreM_3320_, lean_object* v_matchEqns_3321_){
_start:
{
lean_object* v_splitterName_3322_; lean_object* v_splitterMatchInfo_3323_; lean_object* v___x_3324_; lean_object* v_aux2_3325_; lean_object* v_aux2_3326_; lean_object* v_aux2_3327_; lean_object* v___x_3328_; lean_object* v___f_3329_; lean_object* v___f_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___f_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___f_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v_splitterName_3322_ = lean_ctor_get(v_matchEqns_3321_, 1);
lean_inc_n(v_splitterName_3322_, 2);
v_splitterMatchInfo_3323_ = lean_ctor_get(v_matchEqns_3321_, 2);
lean_inc_ref(v_splitterMatchInfo_3323_);
lean_dec_ref(v_matchEqns_3321_);
v___x_3324_ = l_Lean_mkConst(v_splitterName_3322_, v___x_3294_);
v_aux2_3325_ = l_Lean_mkAppN(v___x_3324_, v_params_x27_3295_);
lean_inc_ref(v_fst_3296_);
v_aux2_3326_ = l_Lean_Expr_app___override(v_aux2_3325_, v_fst_3296_);
v_aux2_3327_ = l_Lean_mkAppN(v_aux2_3326_, v_discrs_x27_3297_);
lean_inc_ref_n(v_aux2_3327_, 2);
v___x_3328_ = l_Lean_indentExpr(v_aux2_3327_);
lean_inc(v___x_3313_);
lean_inc_n(v_toBind_3309_, 3);
v___f_3329_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3329_, 0, v_splitterMatchInfo_3323_);
lean_closure_set(v___f_3329_, 1, v_fst_3298_);
lean_closure_set(v___f_3329_, 2, v_numParams_3299_);
lean_closure_set(v___f_3329_, 3, v_numDiscrs_3300_);
lean_closure_set(v___f_3329_, 4, v_altInfos_3301_);
lean_closure_set(v___f_3329_, 5, v_uElimPos_x3f_3302_);
lean_closure_set(v___f_3329_, 6, v_snd_3303_);
lean_closure_set(v___f_3329_, 7, v_overlaps_3304_);
lean_closure_set(v___f_3329_, 8, v_splitterName_3322_);
lean_closure_set(v___f_3329_, 9, v_matcherLevels_3305_);
lean_closure_set(v___f_3329_, 10, v_params_x27_3295_);
lean_closure_set(v___f_3329_, 11, v_fst_3296_);
lean_closure_set(v___f_3329_, 12, v_discrs_x27_3297_);
lean_closure_set(v___f_3329_, 13, v_toPure_3306_);
lean_closure_set(v___f_3329_, 14, v_onRemaining_3307_);
lean_closure_set(v___f_3329_, 15, v_remaining_3308_);
lean_closure_set(v___f_3329_, 16, v_toBind_3309_);
lean_closure_set(v___f_3329_, 17, v_origAltTypes_3310_);
lean_closure_set(v___f_3329_, 18, v_alts_3311_);
lean_closure_set(v___f_3329_, 19, v___x_3312_);
lean_closure_set(v___f_3329_, 20, v___x_3313_);
lean_closure_set(v___f_3329_, 21, v_remaining_x27_3314_);
lean_closure_set(v___f_3329_, 22, v___f_3315_);
lean_inc(v_inst_3316_);
v___f_3330_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3330_, 0, v___x_3313_);
lean_closure_set(v___f_3330_, 1, v_aux2_3327_);
lean_closure_set(v___f_3330_, 2, v_inst_3316_);
lean_closure_set(v___f_3330_, 3, v_toBind_3309_);
lean_closure_set(v___f_3330_, 4, v___f_3329_);
v___x_3331_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v___x_3328_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3332_);
lean_ctor_set(v___x_3333_, 1, v___x_3317_);
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3334_, 0, v___x_3333_);
v___x_3335_ = lean_box(v___x_3318_);
v___x_3336_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3336_, 0, v_aux2_3327_);
lean_closure_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = lean_apply_2(v_inst_3316_, lean_box(0), v___x_3336_);
v___f_3338_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3338_, 0, v___x_3337_);
lean_closure_set(v___f_3338_, 1, v___f_3334_);
v___x_3339_ = lean_apply_2(v_liftWith_3319_, lean_box(0), v___f_3338_);
v___x_3340_ = lean_apply_1(v_restoreM_3320_, lean_box(0));
v___x_3341_ = lean_apply_4(v_toBind_3309_, lean_box(0), lean_box(0), v___x_3339_, v___x_3340_);
v___x_3342_ = lean_apply_4(v_toBind_3309_, lean_box(0), lean_box(0), v___x_3341_, v___f_3330_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3343_ = _args[0];
lean_object* v_params_x27_3344_ = _args[1];
lean_object* v_fst_3345_ = _args[2];
lean_object* v_discrs_x27_3346_ = _args[3];
lean_object* v_fst_3347_ = _args[4];
lean_object* v_numParams_3348_ = _args[5];
lean_object* v_numDiscrs_3349_ = _args[6];
lean_object* v_altInfos_3350_ = _args[7];
lean_object* v_uElimPos_x3f_3351_ = _args[8];
lean_object* v_snd_3352_ = _args[9];
lean_object* v_overlaps_3353_ = _args[10];
lean_object* v_matcherLevels_3354_ = _args[11];
lean_object* v_toPure_3355_ = _args[12];
lean_object* v_onRemaining_3356_ = _args[13];
lean_object* v_remaining_3357_ = _args[14];
lean_object* v_toBind_3358_ = _args[15];
lean_object* v_origAltTypes_3359_ = _args[16];
lean_object* v_alts_3360_ = _args[17];
lean_object* v___x_3361_ = _args[18];
lean_object* v___x_3362_ = _args[19];
lean_object* v_remaining_x27_3363_ = _args[20];
lean_object* v___f_3364_ = _args[21];
lean_object* v_inst_3365_ = _args[22];
lean_object* v___x_3366_ = _args[23];
lean_object* v___x_3367_ = _args[24];
lean_object* v_liftWith_3368_ = _args[25];
lean_object* v_restoreM_3369_ = _args[26];
lean_object* v_matchEqns_3370_ = _args[27];
_start:
{
uint8_t v___x_14249__boxed_3371_; lean_object* v_res_3372_; 
v___x_14249__boxed_3371_ = lean_unbox(v___x_3367_);
v_res_3372_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3343_, v_params_x27_3344_, v_fst_3345_, v_discrs_x27_3346_, v_fst_3347_, v_numParams_3348_, v_numDiscrs_3349_, v_altInfos_3350_, v_uElimPos_x3f_3351_, v_snd_3352_, v_overlaps_3353_, v_matcherLevels_3354_, v_toPure_3355_, v_onRemaining_3356_, v_remaining_3357_, v_toBind_3358_, v_origAltTypes_3359_, v_alts_3360_, v___x_3361_, v___x_3362_, v_remaining_x27_3363_, v___f_3364_, v_inst_3365_, v___x_3366_, v___x_14249__boxed_3371_, v_liftWith_3368_, v_restoreM_3369_, v_matchEqns_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3373_, lean_object* v_params_x27_3374_, lean_object* v_fst_3375_, lean_object* v_discrs_x27_3376_, lean_object* v_fst_3377_, lean_object* v_numParams_3378_, lean_object* v_numDiscrs_3379_, lean_object* v_altInfos_3380_, lean_object* v_uElimPos_x3f_3381_, lean_object* v_snd_3382_, lean_object* v_overlaps_3383_, lean_object* v_matcherLevels_3384_, lean_object* v_toPure_3385_, lean_object* v_onRemaining_3386_, lean_object* v_remaining_3387_, lean_object* v_toBind_3388_, lean_object* v_alts_3389_, lean_object* v___x_3390_, lean_object* v___x_3391_, lean_object* v_remaining_x27_3392_, lean_object* v___f_3393_, lean_object* v_inst_3394_, lean_object* v___x_3395_, uint8_t v___x_3396_, lean_object* v_liftWith_3397_, lean_object* v_restoreM_3398_, lean_object* v_matcherName_3399_, lean_object* v_origAltTypes_3400_){
_start:
{
lean_object* v___x_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3401_ = lean_box(v___x_3396_);
lean_inc(v_inst_3394_);
lean_inc(v_toBind_3388_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3402_, 0, v___x_3373_);
lean_closure_set(v___f_3402_, 1, v_params_x27_3374_);
lean_closure_set(v___f_3402_, 2, v_fst_3375_);
lean_closure_set(v___f_3402_, 3, v_discrs_x27_3376_);
lean_closure_set(v___f_3402_, 4, v_fst_3377_);
lean_closure_set(v___f_3402_, 5, v_numParams_3378_);
lean_closure_set(v___f_3402_, 6, v_numDiscrs_3379_);
lean_closure_set(v___f_3402_, 7, v_altInfos_3380_);
lean_closure_set(v___f_3402_, 8, v_uElimPos_x3f_3381_);
lean_closure_set(v___f_3402_, 9, v_snd_3382_);
lean_closure_set(v___f_3402_, 10, v_overlaps_3383_);
lean_closure_set(v___f_3402_, 11, v_matcherLevels_3384_);
lean_closure_set(v___f_3402_, 12, v_toPure_3385_);
lean_closure_set(v___f_3402_, 13, v_onRemaining_3386_);
lean_closure_set(v___f_3402_, 14, v_remaining_3387_);
lean_closure_set(v___f_3402_, 15, v_toBind_3388_);
lean_closure_set(v___f_3402_, 16, v_origAltTypes_3400_);
lean_closure_set(v___f_3402_, 17, v_alts_3389_);
lean_closure_set(v___f_3402_, 18, v___x_3390_);
lean_closure_set(v___f_3402_, 19, v___x_3391_);
lean_closure_set(v___f_3402_, 20, v_remaining_x27_3392_);
lean_closure_set(v___f_3402_, 21, v___f_3393_);
lean_closure_set(v___f_3402_, 22, v_inst_3394_);
lean_closure_set(v___f_3402_, 23, v___x_3395_);
lean_closure_set(v___f_3402_, 24, v___x_3401_);
lean_closure_set(v___f_3402_, 25, v_liftWith_3397_);
lean_closure_set(v___f_3402_, 26, v_restoreM_3398_);
v___x_3403_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3403_, 0, v_matcherName_3399_);
v___x_3404_ = lean_apply_2(v_inst_3394_, lean_box(0), v___x_3403_);
v___x_3405_ = lean_apply_4(v_toBind_3388_, lean_box(0), lean_box(0), v___x_3404_, v___f_3402_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3406_ = _args[0];
lean_object* v_params_x27_3407_ = _args[1];
lean_object* v_fst_3408_ = _args[2];
lean_object* v_discrs_x27_3409_ = _args[3];
lean_object* v_fst_3410_ = _args[4];
lean_object* v_numParams_3411_ = _args[5];
lean_object* v_numDiscrs_3412_ = _args[6];
lean_object* v_altInfos_3413_ = _args[7];
lean_object* v_uElimPos_x3f_3414_ = _args[8];
lean_object* v_snd_3415_ = _args[9];
lean_object* v_overlaps_3416_ = _args[10];
lean_object* v_matcherLevels_3417_ = _args[11];
lean_object* v_toPure_3418_ = _args[12];
lean_object* v_onRemaining_3419_ = _args[13];
lean_object* v_remaining_3420_ = _args[14];
lean_object* v_toBind_3421_ = _args[15];
lean_object* v_alts_3422_ = _args[16];
lean_object* v___x_3423_ = _args[17];
lean_object* v___x_3424_ = _args[18];
lean_object* v_remaining_x27_3425_ = _args[19];
lean_object* v___f_3426_ = _args[20];
lean_object* v_inst_3427_ = _args[21];
lean_object* v___x_3428_ = _args[22];
lean_object* v___x_3429_ = _args[23];
lean_object* v_liftWith_3430_ = _args[24];
lean_object* v_restoreM_3431_ = _args[25];
lean_object* v_matcherName_3432_ = _args[26];
lean_object* v_origAltTypes_3433_ = _args[27];
_start:
{
uint8_t v___x_14311__boxed_3434_; lean_object* v_res_3435_; 
v___x_14311__boxed_3434_ = lean_unbox(v___x_3429_);
v_res_3435_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3406_, v_params_x27_3407_, v_fst_3408_, v_discrs_x27_3409_, v_fst_3410_, v_numParams_3411_, v_numDiscrs_3412_, v_altInfos_3413_, v_uElimPos_x3f_3414_, v_snd_3415_, v_overlaps_3416_, v_matcherLevels_3417_, v_toPure_3418_, v_onRemaining_3419_, v_remaining_3420_, v_toBind_3421_, v_alts_3422_, v___x_3423_, v___x_3424_, v_remaining_x27_3425_, v___f_3426_, v_inst_3427_, v___x_3428_, v___x_14311__boxed_3434_, v_liftWith_3430_, v_restoreM_3431_, v_matcherName_3432_, v_origAltTypes_3433_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3436_, lean_object* v_toPure_3437_, lean_object* v_toBind_3438_, lean_object* v___f_3439_, lean_object* v___x_3440_, lean_object* v___x_3441_, lean_object* v_inst_3442_, lean_object* v___x_3443_, lean_object* v_toMonadExceptOf_3444_, uint8_t v___x_3445_, uint8_t v_useSplitter_3446_, lean_object* v_onAlt_3447_, lean_object* v___f_3448_, lean_object* v_fst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_numDiscrEqs_3452_, lean_object* v___x_3453_, lean_object* v_params_x27_3454_, lean_object* v_fst_3455_, lean_object* v_discrs_x27_3456_, lean_object* v_fst_3457_, lean_object* v_numParams_3458_, lean_object* v_numDiscrs_3459_, lean_object* v_altInfos_3460_, lean_object* v_uElimPos_x3f_3461_, lean_object* v_snd_3462_, lean_object* v_overlaps_3463_, lean_object* v_matcherLevels_3464_, lean_object* v_onRemaining_3465_, lean_object* v_remaining_3466_, lean_object* v_remaining_x27_3467_, lean_object* v___x_3468_, uint8_t v___x_3469_, lean_object* v_liftWith_3470_, lean_object* v_restoreM_3471_, lean_object* v_matcherName_3472_, lean_object* v_aux1_3473_, lean_object* v_____r_3474_){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___f_3478_; lean_object* v___x_3479_; lean_object* v___f_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3475_ = lean_array_get_size(v_alts_3436_);
v___x_3476_ = lean_box(v___x_3445_);
v___x_3477_ = lean_box(v_useSplitter_3446_);
lean_inc_n(v_inst_3442_, 2);
lean_inc(v___x_3440_);
lean_inc_n(v_toBind_3438_, 2);
lean_inc(v_toPure_3437_);
v___f_3478_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 21, 17);
lean_closure_set(v___f_3478_, 0, v___x_3475_);
lean_closure_set(v___f_3478_, 1, v_toPure_3437_);
lean_closure_set(v___f_3478_, 2, v_toBind_3438_);
lean_closure_set(v___f_3478_, 3, v___f_3439_);
lean_closure_set(v___f_3478_, 4, v___x_3440_);
lean_closure_set(v___f_3478_, 5, v___x_3441_);
lean_closure_set(v___f_3478_, 6, v_inst_3442_);
lean_closure_set(v___f_3478_, 7, v___x_3443_);
lean_closure_set(v___f_3478_, 8, v_toMonadExceptOf_3444_);
lean_closure_set(v___f_3478_, 9, v___x_3476_);
lean_closure_set(v___f_3478_, 10, v___x_3477_);
lean_closure_set(v___f_3478_, 11, v_onAlt_3447_);
lean_closure_set(v___f_3478_, 12, v___f_3448_);
lean_closure_set(v___f_3478_, 13, v_fst_3449_);
lean_closure_set(v___f_3478_, 14, v_inst_3450_);
lean_closure_set(v___f_3478_, 15, v_inst_3451_);
lean_closure_set(v___f_3478_, 16, v_numDiscrEqs_3452_);
v___x_3479_ = lean_box(v___x_3469_);
v___f_3480_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 28, 27);
lean_closure_set(v___f_3480_, 0, v___x_3453_);
lean_closure_set(v___f_3480_, 1, v_params_x27_3454_);
lean_closure_set(v___f_3480_, 2, v_fst_3455_);
lean_closure_set(v___f_3480_, 3, v_discrs_x27_3456_);
lean_closure_set(v___f_3480_, 4, v_fst_3457_);
lean_closure_set(v___f_3480_, 5, v_numParams_3458_);
lean_closure_set(v___f_3480_, 6, v_numDiscrs_3459_);
lean_closure_set(v___f_3480_, 7, v_altInfos_3460_);
lean_closure_set(v___f_3480_, 8, v_uElimPos_x3f_3461_);
lean_closure_set(v___f_3480_, 9, v_snd_3462_);
lean_closure_set(v___f_3480_, 10, v_overlaps_3463_);
lean_closure_set(v___f_3480_, 11, v_matcherLevels_3464_);
lean_closure_set(v___f_3480_, 12, v_toPure_3437_);
lean_closure_set(v___f_3480_, 13, v_onRemaining_3465_);
lean_closure_set(v___f_3480_, 14, v_remaining_3466_);
lean_closure_set(v___f_3480_, 15, v_toBind_3438_);
lean_closure_set(v___f_3480_, 16, v_alts_3436_);
lean_closure_set(v___f_3480_, 17, v___x_3440_);
lean_closure_set(v___f_3480_, 18, v___x_3475_);
lean_closure_set(v___f_3480_, 19, v_remaining_x27_3467_);
lean_closure_set(v___f_3480_, 20, v___f_3478_);
lean_closure_set(v___f_3480_, 21, v_inst_3442_);
lean_closure_set(v___f_3480_, 22, v___x_3468_);
lean_closure_set(v___f_3480_, 23, v___x_3479_);
lean_closure_set(v___f_3480_, 24, v_liftWith_3470_);
lean_closure_set(v___f_3480_, 25, v_restoreM_3471_);
lean_closure_set(v___f_3480_, 26, v_matcherName_3472_);
v___x_3481_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3481_, 0, v___x_3475_);
lean_closure_set(v___x_3481_, 1, v_aux1_3473_);
v___x_3482_ = lean_apply_2(v_inst_3442_, lean_box(0), v___x_3481_);
v___x_3483_ = lean_apply_4(v_toBind_3438_, lean_box(0), lean_box(0), v___x_3482_, v___f_3480_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3484_ = _args[0];
lean_object* v_toPure_3485_ = _args[1];
lean_object* v_toBind_3486_ = _args[2];
lean_object* v___f_3487_ = _args[3];
lean_object* v___x_3488_ = _args[4];
lean_object* v___x_3489_ = _args[5];
lean_object* v_inst_3490_ = _args[6];
lean_object* v___x_3491_ = _args[7];
lean_object* v_toMonadExceptOf_3492_ = _args[8];
lean_object* v___x_3493_ = _args[9];
lean_object* v_useSplitter_3494_ = _args[10];
lean_object* v_onAlt_3495_ = _args[11];
lean_object* v___f_3496_ = _args[12];
lean_object* v_fst_3497_ = _args[13];
lean_object* v_inst_3498_ = _args[14];
lean_object* v_inst_3499_ = _args[15];
lean_object* v_numDiscrEqs_3500_ = _args[16];
lean_object* v___x_3501_ = _args[17];
lean_object* v_params_x27_3502_ = _args[18];
lean_object* v_fst_3503_ = _args[19];
lean_object* v_discrs_x27_3504_ = _args[20];
lean_object* v_fst_3505_ = _args[21];
lean_object* v_numParams_3506_ = _args[22];
lean_object* v_numDiscrs_3507_ = _args[23];
lean_object* v_altInfos_3508_ = _args[24];
lean_object* v_uElimPos_x3f_3509_ = _args[25];
lean_object* v_snd_3510_ = _args[26];
lean_object* v_overlaps_3511_ = _args[27];
lean_object* v_matcherLevels_3512_ = _args[28];
lean_object* v_onRemaining_3513_ = _args[29];
lean_object* v_remaining_3514_ = _args[30];
lean_object* v_remaining_x27_3515_ = _args[31];
lean_object* v___x_3516_ = _args[32];
lean_object* v___x_3517_ = _args[33];
lean_object* v_liftWith_3518_ = _args[34];
lean_object* v_restoreM_3519_ = _args[35];
lean_object* v_matcherName_3520_ = _args[36];
lean_object* v_aux1_3521_ = _args[37];
lean_object* v_____r_3522_ = _args[38];
_start:
{
uint8_t v___x_14345__boxed_3523_; uint8_t v_useSplitter_boxed_3524_; uint8_t v___x_14353__boxed_3525_; lean_object* v_res_3526_; 
v___x_14345__boxed_3523_ = lean_unbox(v___x_3493_);
v_useSplitter_boxed_3524_ = lean_unbox(v_useSplitter_3494_);
v___x_14353__boxed_3525_ = lean_unbox(v___x_3517_);
v_res_3526_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3484_, v_toPure_3485_, v_toBind_3486_, v___f_3487_, v___x_3488_, v___x_3489_, v_inst_3490_, v___x_3491_, v_toMonadExceptOf_3492_, v___x_14345__boxed_3523_, v_useSplitter_boxed_3524_, v_onAlt_3495_, v___f_3496_, v_fst_3497_, v_inst_3498_, v_inst_3499_, v_numDiscrEqs_3500_, v___x_3501_, v_params_x27_3502_, v_fst_3503_, v_discrs_x27_3504_, v_fst_3505_, v_numParams_3506_, v_numDiscrs_3507_, v_altInfos_3508_, v_uElimPos_x3f_3509_, v_snd_3510_, v_overlaps_3511_, v_matcherLevels_3512_, v_onRemaining_3513_, v_remaining_3514_, v_remaining_x27_3515_, v___x_3516_, v___x_14353__boxed_3525_, v_liftWith_3518_, v_restoreM_3519_, v_matcherName_3520_, v_aux1_3521_, v_____r_3522_);
return v_res_3526_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3529_ = l_Lean_stringToMessageData(v___x_3528_);
return v___x_3529_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3(void){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2));
v___x_3532_ = l_Lean_stringToMessageData(v___x_3531_);
return v___x_3532_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5(void){
_start:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3534_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4));
v___x_3535_ = l_Lean_stringToMessageData(v___x_3534_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v_numParams_3536_, lean_object* v_numDiscrs_3537_, lean_object* v_altInfos_3538_, lean_object* v_uElimPos_x3f_3539_, lean_object* v_snd_3540_, lean_object* v_overlaps_3541_, lean_object* v_matcherName_3542_, lean_object* v_matcherLevels_3543_, lean_object* v_params_x27_3544_, lean_object* v_fst_3545_, lean_object* v_discrs_x27_3546_, lean_object* v_toPure_3547_, lean_object* v_onRemaining_3548_, lean_object* v_remaining_3549_, lean_object* v_toBind_3550_, lean_object* v_inst_3551_, lean_object* v_alts_3552_, lean_object* v___f_3553_, uint8_t v___x_3554_, lean_object* v_inst_3555_, lean_object* v_remaining_x27_3556_, lean_object* v_onAlt_3557_, lean_object* v_inst_3558_, lean_object* v___f_3559_, lean_object* v_matcherApp_3560_, lean_object* v___x_3561_, uint8_t v_useSplitter_3562_, uint8_t v_isCasesOn_3563_, lean_object* v___f_3564_, lean_object* v___x_3565_, lean_object* v___x_3566_, lean_object* v_toMonadExceptOf_3567_, lean_object* v___f_3568_, lean_object* v_numDiscrEqs_3569_, lean_object* v_____s_3570_){
_start:
{
lean_object* v_snd_3571_; lean_object* v_fst_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3638_; 
v_snd_3571_ = lean_ctor_get(v_____s_3570_, 1);
v_fst_3572_ = lean_ctor_get(v_____s_3570_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_____s_3570_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3574_ = v_____s_3570_;
v_isShared_3575_ = v_isSharedCheck_3638_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_snd_3571_);
lean_inc(v_fst_3572_);
lean_dec(v_____s_3570_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3638_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v_fst_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3636_; 
v_fst_3576_ = lean_ctor_get(v_snd_3571_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v_snd_3571_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v_snd_3571_, 1);
lean_dec(v_unused_3637_);
v___x_3578_ = v_snd_3571_;
v_isShared_3579_ = v_isSharedCheck_3636_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_fst_3576_);
lean_dec(v_snd_3571_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3636_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___f_3580_; 
lean_inc(v_toBind_3550_);
lean_inc_ref(v_remaining_3549_);
lean_inc(v_onRemaining_3548_);
lean_inc(v_toPure_3547_);
lean_inc_ref(v_discrs_x27_3546_);
lean_inc_ref(v_fst_3545_);
lean_inc_ref(v_params_x27_3544_);
lean_inc_ref(v_matcherLevels_3543_);
lean_inc(v_matcherName_3542_);
lean_inc_ref(v_overlaps_3541_);
lean_inc_ref(v_snd_3540_);
lean_inc(v_uElimPos_x3f_3539_);
lean_inc_ref(v_altInfos_3538_);
lean_inc(v_numDiscrs_3537_);
lean_inc(v_numParams_3536_);
lean_inc(v_fst_3572_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3580_, 0, v_fst_3572_);
lean_closure_set(v___f_3580_, 1, v_numParams_3536_);
lean_closure_set(v___f_3580_, 2, v_numDiscrs_3537_);
lean_closure_set(v___f_3580_, 3, v_altInfos_3538_);
lean_closure_set(v___f_3580_, 4, v_uElimPos_x3f_3539_);
lean_closure_set(v___f_3580_, 5, v_snd_3540_);
lean_closure_set(v___f_3580_, 6, v_overlaps_3541_);
lean_closure_set(v___f_3580_, 7, v_matcherName_3542_);
lean_closure_set(v___f_3580_, 8, v_matcherLevels_3543_);
lean_closure_set(v___f_3580_, 9, v_params_x27_3544_);
lean_closure_set(v___f_3580_, 10, v_fst_3545_);
lean_closure_set(v___f_3580_, 11, v_discrs_x27_3546_);
lean_closure_set(v___f_3580_, 12, v_toPure_3547_);
lean_closure_set(v___f_3580_, 13, v_onRemaining_3548_);
lean_closure_set(v___f_3580_, 14, v_remaining_3549_);
lean_closure_set(v___f_3580_, 15, v_toBind_3550_);
if (v_useSplitter_3562_ == 0)
{
lean_del_object(v___x_3574_);
lean_dec(v_fst_3572_);
lean_dec(v_numDiscrEqs_3569_);
lean_dec(v___f_3568_);
lean_dec_ref(v_toMonadExceptOf_3567_);
lean_dec(v___x_3566_);
lean_dec(v___x_3565_);
lean_dec(v___f_3564_);
lean_dec_ref(v_remaining_3549_);
lean_dec(v_onRemaining_3548_);
lean_dec_ref(v_overlaps_3541_);
lean_dec_ref(v_snd_3540_);
lean_dec(v_uElimPos_x3f_3539_);
lean_dec_ref(v_altInfos_3538_);
lean_dec(v_numDiscrs_3537_);
lean_dec(v_numParams_3536_);
goto v___jp_3581_;
}
else
{
if (v_isCasesOn_3563_ == 0)
{
lean_object* v_liftWith_3608_; lean_object* v_restoreM_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v_aux1_3612_; lean_object* v_aux1_3613_; lean_object* v_aux1_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
lean_dec_ref(v___f_3580_);
lean_del_object(v___x_3578_);
lean_dec_ref(v_matcherApp_3560_);
lean_dec(v___f_3559_);
lean_dec(v___f_3553_);
v_liftWith_3608_ = lean_ctor_get(v_inst_3551_, 0);
lean_inc(v_liftWith_3608_);
v_restoreM_3609_ = lean_ctor_get(v_inst_3551_, 1);
lean_inc(v_restoreM_3609_);
lean_inc_ref(v_matcherLevels_3543_);
v___x_3610_ = lean_array_to_list(v_matcherLevels_3543_);
lean_inc(v___x_3610_);
lean_inc(v_matcherName_3542_);
v___x_3611_ = l_Lean_mkConst(v_matcherName_3542_, v___x_3610_);
v_aux1_3612_ = l_Lean_mkAppN(v___x_3611_, v_params_x27_3544_);
lean_inc_ref(v_fst_3545_);
v_aux1_3613_ = l_Lean_Expr_app___override(v_aux1_3612_, v_fst_3545_);
v_aux1_3614_ = l_Lean_mkAppN(v_aux1_3613_, v_discrs_x27_3546_);
lean_inc_ref(v_aux1_3614_);
v___x_3615_ = l_Lean_indentExpr(v_aux1_3614_);
v___x_3616_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 7);
lean_ctor_set(v___x_3574_, 1, v___x_3615_);
lean_ctor_set(v___x_3574_, 0, v___x_3616_);
v___x_3618_ = v___x_3574_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3635_, 1, v___x_3615_);
v___x_3618_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___f_3621_; uint8_t v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___f_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___f_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3619_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___f_3621_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3621_, 0, v___x_3620_);
v___x_3622_ = 0;
v___x_3623_ = lean_box(v___x_3554_);
v___x_3624_ = lean_box(v_useSplitter_3562_);
v___x_3625_ = lean_box(v___x_3622_);
lean_inc_ref(v_aux1_3614_);
lean_inc(v_restoreM_3609_);
lean_inc(v_liftWith_3608_);
lean_inc(v_inst_3555_);
lean_inc_n(v_toBind_3550_, 2);
v___f_3626_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 39, 38);
lean_closure_set(v___f_3626_, 0, v_alts_3552_);
lean_closure_set(v___f_3626_, 1, v_toPure_3547_);
lean_closure_set(v___f_3626_, 2, v_toBind_3550_);
lean_closure_set(v___f_3626_, 3, v___f_3564_);
lean_closure_set(v___f_3626_, 4, v___x_3561_);
lean_closure_set(v___f_3626_, 5, v___x_3565_);
lean_closure_set(v___f_3626_, 6, v_inst_3555_);
lean_closure_set(v___f_3626_, 7, v___x_3566_);
lean_closure_set(v___f_3626_, 8, v_toMonadExceptOf_3567_);
lean_closure_set(v___f_3626_, 9, v___x_3623_);
lean_closure_set(v___f_3626_, 10, v___x_3624_);
lean_closure_set(v___f_3626_, 11, v_onAlt_3557_);
lean_closure_set(v___f_3626_, 12, v___f_3568_);
lean_closure_set(v___f_3626_, 13, v_fst_3576_);
lean_closure_set(v___f_3626_, 14, v_inst_3551_);
lean_closure_set(v___f_3626_, 15, v_inst_3558_);
lean_closure_set(v___f_3626_, 16, v_numDiscrEqs_3569_);
lean_closure_set(v___f_3626_, 17, v___x_3610_);
lean_closure_set(v___f_3626_, 18, v_params_x27_3544_);
lean_closure_set(v___f_3626_, 19, v_fst_3545_);
lean_closure_set(v___f_3626_, 20, v_discrs_x27_3546_);
lean_closure_set(v___f_3626_, 21, v_fst_3572_);
lean_closure_set(v___f_3626_, 22, v_numParams_3536_);
lean_closure_set(v___f_3626_, 23, v_numDiscrs_3537_);
lean_closure_set(v___f_3626_, 24, v_altInfos_3538_);
lean_closure_set(v___f_3626_, 25, v_uElimPos_x3f_3539_);
lean_closure_set(v___f_3626_, 26, v_snd_3540_);
lean_closure_set(v___f_3626_, 27, v_overlaps_3541_);
lean_closure_set(v___f_3626_, 28, v_matcherLevels_3543_);
lean_closure_set(v___f_3626_, 29, v_onRemaining_3548_);
lean_closure_set(v___f_3626_, 30, v_remaining_3549_);
lean_closure_set(v___f_3626_, 31, v_remaining_x27_3556_);
lean_closure_set(v___f_3626_, 32, v___x_3619_);
lean_closure_set(v___f_3626_, 33, v___x_3625_);
lean_closure_set(v___f_3626_, 34, v_liftWith_3608_);
lean_closure_set(v___f_3626_, 35, v_restoreM_3609_);
lean_closure_set(v___f_3626_, 36, v_matcherName_3542_);
lean_closure_set(v___f_3626_, 37, v_aux1_3614_);
v___x_3627_ = lean_box(v___x_3622_);
v___x_3628_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3628_, 0, v_aux1_3614_);
lean_closure_set(v___x_3628_, 1, v___x_3627_);
v___x_3629_ = lean_apply_2(v_inst_3555_, lean_box(0), v___x_3628_);
v___f_3630_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3630_, 0, v___x_3629_);
lean_closure_set(v___f_3630_, 1, v___f_3621_);
v___x_3631_ = lean_apply_2(v_liftWith_3608_, lean_box(0), v___f_3630_);
v___x_3632_ = lean_apply_1(v_restoreM_3609_, lean_box(0));
v___x_3633_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3631_, v___x_3632_);
v___x_3634_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3633_, v___f_3626_);
return v___x_3634_;
}
}
else
{
lean_del_object(v___x_3574_);
lean_dec(v_fst_3572_);
lean_dec(v_numDiscrEqs_3569_);
lean_dec(v___f_3568_);
lean_dec_ref(v_toMonadExceptOf_3567_);
lean_dec(v___x_3566_);
lean_dec(v___x_3565_);
lean_dec(v___f_3564_);
lean_dec_ref(v_remaining_3549_);
lean_dec(v_onRemaining_3548_);
lean_dec_ref(v_overlaps_3541_);
lean_dec_ref(v_snd_3540_);
lean_dec(v_uElimPos_x3f_3539_);
lean_dec_ref(v_altInfos_3538_);
lean_dec(v_numDiscrs_3537_);
lean_dec(v_numParams_3536_);
goto v___jp_3581_;
}
}
v___jp_3581_:
{
lean_object* v_liftWith_3582_; lean_object* v_restoreM_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v_aux_3586_; lean_object* v_aux_3587_; lean_object* v_aux_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v_liftWith_3582_ = lean_ctor_get(v_inst_3551_, 0);
lean_inc(v_liftWith_3582_);
v_restoreM_3583_ = lean_ctor_get(v_inst_3551_, 1);
lean_inc(v_restoreM_3583_);
v___x_3584_ = lean_array_to_list(v_matcherLevels_3543_);
v___x_3585_ = l_Lean_mkConst(v_matcherName_3542_, v___x_3584_);
v_aux_3586_ = l_Lean_mkAppN(v___x_3585_, v_params_x27_3544_);
lean_dec_ref(v_params_x27_3544_);
v_aux_3587_ = l_Lean_Expr_app___override(v_aux_3586_, v_fst_3545_);
v_aux_3588_ = l_Lean_mkAppN(v_aux_3587_, v_discrs_x27_3546_);
lean_dec_ref(v_discrs_x27_3546_);
lean_inc_ref_n(v_aux_3588_, 2);
v___x_3589_ = l_Lean_indentExpr(v_aux_3588_);
v___x_3590_ = 1;
v___x_3591_ = lean_box(v___x_3554_);
v___x_3592_ = lean_box(v___x_3590_);
lean_inc(v_inst_3555_);
lean_inc(v_toBind_3550_);
v___f_3593_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3593_, 0, v_alts_3552_);
lean_closure_set(v___f_3593_, 1, v_toPure_3547_);
lean_closure_set(v___f_3593_, 2, v_toBind_3550_);
lean_closure_set(v___f_3593_, 3, v___f_3553_);
lean_closure_set(v___f_3593_, 4, v___x_3591_);
lean_closure_set(v___f_3593_, 5, v___x_3592_);
lean_closure_set(v___f_3593_, 6, v_inst_3555_);
lean_closure_set(v___f_3593_, 7, v_remaining_x27_3556_);
lean_closure_set(v___f_3593_, 8, v_onAlt_3557_);
lean_closure_set(v___f_3593_, 9, v_inst_3551_);
lean_closure_set(v___f_3593_, 10, v_inst_3558_);
lean_closure_set(v___f_3593_, 11, v___f_3559_);
lean_closure_set(v___f_3593_, 12, v_fst_3576_);
lean_closure_set(v___f_3593_, 13, v_matcherApp_3560_);
lean_closure_set(v___f_3593_, 14, v___x_3561_);
lean_closure_set(v___f_3593_, 15, v___f_3580_);
lean_closure_set(v___f_3593_, 16, v_aux_3588_);
v___x_3594_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 7);
lean_ctor_set(v___x_3578_, 1, v___x_3589_);
lean_ctor_set(v___x_3578_, 0, v___x_3594_);
v___x_3596_ = v___x_3578_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3594_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v___x_3589_);
v___x_3596_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___f_3597_; uint8_t v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___f_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___f_3597_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3597_, 0, v___x_3596_);
v___x_3598_ = 0;
v___x_3599_ = lean_box(v___x_3598_);
v___x_3600_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3600_, 0, v_aux_3588_);
lean_closure_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_apply_2(v_inst_3555_, lean_box(0), v___x_3600_);
v___f_3602_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3602_, 0, v___x_3601_);
lean_closure_set(v___f_3602_, 1, v___f_3597_);
v___x_3603_ = lean_apply_2(v_liftWith_3582_, lean_box(0), v___f_3602_);
v___x_3604_ = lean_apply_1(v_restoreM_3583_, lean_box(0));
lean_inc(v_toBind_3550_);
v___x_3605_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3603_, v___x_3604_);
v___x_3606_ = lean_apply_4(v_toBind_3550_, lean_box(0), lean_box(0), v___x_3605_, v___f_3593_);
return v___x_3606_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v_numParams_3639_ = _args[0];
lean_object* v_numDiscrs_3640_ = _args[1];
lean_object* v_altInfos_3641_ = _args[2];
lean_object* v_uElimPos_x3f_3642_ = _args[3];
lean_object* v_snd_3643_ = _args[4];
lean_object* v_overlaps_3644_ = _args[5];
lean_object* v_matcherName_3645_ = _args[6];
lean_object* v_matcherLevels_3646_ = _args[7];
lean_object* v_params_x27_3647_ = _args[8];
lean_object* v_fst_3648_ = _args[9];
lean_object* v_discrs_x27_3649_ = _args[10];
lean_object* v_toPure_3650_ = _args[11];
lean_object* v_onRemaining_3651_ = _args[12];
lean_object* v_remaining_3652_ = _args[13];
lean_object* v_toBind_3653_ = _args[14];
lean_object* v_inst_3654_ = _args[15];
lean_object* v_alts_3655_ = _args[16];
lean_object* v___f_3656_ = _args[17];
lean_object* v___x_3657_ = _args[18];
lean_object* v_inst_3658_ = _args[19];
lean_object* v_remaining_x27_3659_ = _args[20];
lean_object* v_onAlt_3660_ = _args[21];
lean_object* v_inst_3661_ = _args[22];
lean_object* v___f_3662_ = _args[23];
lean_object* v_matcherApp_3663_ = _args[24];
lean_object* v___x_3664_ = _args[25];
lean_object* v_useSplitter_3665_ = _args[26];
lean_object* v_isCasesOn_3666_ = _args[27];
lean_object* v___f_3667_ = _args[28];
lean_object* v___x_3668_ = _args[29];
lean_object* v___x_3669_ = _args[30];
lean_object* v_toMonadExceptOf_3670_ = _args[31];
lean_object* v___f_3671_ = _args[32];
lean_object* v_numDiscrEqs_3672_ = _args[33];
lean_object* v_____s_3673_ = _args[34];
_start:
{
uint8_t v___x_14425__boxed_3674_; uint8_t v_useSplitter_boxed_3675_; uint8_t v_isCasesOn_boxed_3676_; lean_object* v_res_3677_; 
v___x_14425__boxed_3674_ = lean_unbox(v___x_3657_);
v_useSplitter_boxed_3675_ = lean_unbox(v_useSplitter_3665_);
v_isCasesOn_boxed_3676_ = lean_unbox(v_isCasesOn_3666_);
v_res_3677_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3639_, v_numDiscrs_3640_, v_altInfos_3641_, v_uElimPos_x3f_3642_, v_snd_3643_, v_overlaps_3644_, v_matcherName_3645_, v_matcherLevels_3646_, v_params_x27_3647_, v_fst_3648_, v_discrs_x27_3649_, v_toPure_3650_, v_onRemaining_3651_, v_remaining_3652_, v_toBind_3653_, v_inst_3654_, v_alts_3655_, v___f_3656_, v___x_14425__boxed_3674_, v_inst_3658_, v_remaining_x27_3659_, v_onAlt_3660_, v_inst_3661_, v___f_3662_, v_matcherApp_3663_, v___x_3664_, v_useSplitter_boxed_3675_, v_isCasesOn_boxed_3676_, v___f_3667_, v___x_3668_, v___x_3669_, v_toMonadExceptOf_3670_, v___f_3671_, v_numDiscrEqs_3672_, v_____s_3673_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3678_, lean_object* v_numDiscrs_3679_, lean_object* v_altInfos_3680_, lean_object* v_uElimPos_x3f_3681_, lean_object* v_snd_3682_, lean_object* v_overlaps_3683_, lean_object* v_matcherName_3684_, lean_object* v_params_x27_3685_, lean_object* v_fst_3686_, lean_object* v_discrs_x27_3687_, lean_object* v_toPure_3688_, lean_object* v_onRemaining_3689_, lean_object* v_remaining_3690_, lean_object* v_toBind_3691_, lean_object* v_inst_3692_, lean_object* v_alts_3693_, lean_object* v___f_3694_, uint8_t v___x_3695_, lean_object* v_inst_3696_, lean_object* v_onAlt_3697_, lean_object* v_inst_3698_, lean_object* v___f_3699_, lean_object* v_matcherApp_3700_, uint8_t v_useSplitter_3701_, uint8_t v_isCasesOn_3702_, lean_object* v___f_3703_, lean_object* v___x_3704_, lean_object* v___x_3705_, lean_object* v_toMonadExceptOf_3706_, lean_object* v___f_3707_, lean_object* v_numDiscrEqs_3708_, lean_object* v_fst_3709_, lean_object* v___f_3710_, lean_object* v_matcherLevels_3711_){
_start:
{
lean_object* v___x_3712_; lean_object* v_remaining_x27_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___f_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; size_t v_sz_3724_; size_t v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3713_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3714_ = lean_box(v___x_3695_);
v___x_3715_ = lean_box(v_useSplitter_3701_);
v___x_3716_ = lean_box(v_isCasesOn_3702_);
lean_inc_ref(v_inst_3698_);
lean_inc(v_toBind_3691_);
lean_inc_ref(v_discrs_x27_3687_);
v___f_3717_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 35, 34);
lean_closure_set(v___f_3717_, 0, v_numParams_3678_);
lean_closure_set(v___f_3717_, 1, v_numDiscrs_3679_);
lean_closure_set(v___f_3717_, 2, v_altInfos_3680_);
lean_closure_set(v___f_3717_, 3, v_uElimPos_x3f_3681_);
lean_closure_set(v___f_3717_, 4, v_snd_3682_);
lean_closure_set(v___f_3717_, 5, v_overlaps_3683_);
lean_closure_set(v___f_3717_, 6, v_matcherName_3684_);
lean_closure_set(v___f_3717_, 7, v_matcherLevels_3711_);
lean_closure_set(v___f_3717_, 8, v_params_x27_3685_);
lean_closure_set(v___f_3717_, 9, v_fst_3686_);
lean_closure_set(v___f_3717_, 10, v_discrs_x27_3687_);
lean_closure_set(v___f_3717_, 11, v_toPure_3688_);
lean_closure_set(v___f_3717_, 12, v_onRemaining_3689_);
lean_closure_set(v___f_3717_, 13, v_remaining_3690_);
lean_closure_set(v___f_3717_, 14, v_toBind_3691_);
lean_closure_set(v___f_3717_, 15, v_inst_3692_);
lean_closure_set(v___f_3717_, 16, v_alts_3693_);
lean_closure_set(v___f_3717_, 17, v___f_3694_);
lean_closure_set(v___f_3717_, 18, v___x_3714_);
lean_closure_set(v___f_3717_, 19, v_inst_3696_);
lean_closure_set(v___f_3717_, 20, v_remaining_x27_3713_);
lean_closure_set(v___f_3717_, 21, v_onAlt_3697_);
lean_closure_set(v___f_3717_, 22, v_inst_3698_);
lean_closure_set(v___f_3717_, 23, v___f_3699_);
lean_closure_set(v___f_3717_, 24, v_matcherApp_3700_);
lean_closure_set(v___f_3717_, 25, v___x_3712_);
lean_closure_set(v___f_3717_, 26, v___x_3715_);
lean_closure_set(v___f_3717_, 27, v___x_3716_);
lean_closure_set(v___f_3717_, 28, v___f_3703_);
lean_closure_set(v___f_3717_, 29, v___x_3704_);
lean_closure_set(v___f_3717_, 30, v___x_3705_);
lean_closure_set(v___f_3717_, 31, v_toMonadExceptOf_3706_);
lean_closure_set(v___f_3717_, 32, v___f_3707_);
lean_closure_set(v___f_3717_, 33, v_numDiscrEqs_3708_);
v___x_3718_ = l_Array_reverse___redArg(v_fst_3709_);
v___x_3719_ = lean_array_get_size(v___x_3718_);
v___x_3720_ = l_Array_toSubarray___redArg(v___x_3718_, v___x_3712_, v___x_3719_);
v___x_3721_ = l_Array_reverse___redArg(v_discrs_x27_3687_);
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3712_);
lean_ctor_set(v___x_3722_, 1, v___x_3720_);
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v_remaining_x27_3713_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v_sz_3724_ = lean_array_size(v___x_3721_);
v___x_3725_ = ((size_t)0ULL);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3698_, v___x_3721_, v___f_3710_, v_sz_3724_, v___x_3725_, v___x_3723_);
v___x_3727_ = lean_apply_4(v_toBind_3691_, lean_box(0), lean_box(0), v___x_3726_, v___f_3717_);
return v___x_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3728_ = _args[0];
lean_object* v_numDiscrs_3729_ = _args[1];
lean_object* v_altInfos_3730_ = _args[2];
lean_object* v_uElimPos_x3f_3731_ = _args[3];
lean_object* v_snd_3732_ = _args[4];
lean_object* v_overlaps_3733_ = _args[5];
lean_object* v_matcherName_3734_ = _args[6];
lean_object* v_params_x27_3735_ = _args[7];
lean_object* v_fst_3736_ = _args[8];
lean_object* v_discrs_x27_3737_ = _args[9];
lean_object* v_toPure_3738_ = _args[10];
lean_object* v_onRemaining_3739_ = _args[11];
lean_object* v_remaining_3740_ = _args[12];
lean_object* v_toBind_3741_ = _args[13];
lean_object* v_inst_3742_ = _args[14];
lean_object* v_alts_3743_ = _args[15];
lean_object* v___f_3744_ = _args[16];
lean_object* v___x_3745_ = _args[17];
lean_object* v_inst_3746_ = _args[18];
lean_object* v_onAlt_3747_ = _args[19];
lean_object* v_inst_3748_ = _args[20];
lean_object* v___f_3749_ = _args[21];
lean_object* v_matcherApp_3750_ = _args[22];
lean_object* v_useSplitter_3751_ = _args[23];
lean_object* v_isCasesOn_3752_ = _args[24];
lean_object* v___f_3753_ = _args[25];
lean_object* v___x_3754_ = _args[26];
lean_object* v___x_3755_ = _args[27];
lean_object* v_toMonadExceptOf_3756_ = _args[28];
lean_object* v___f_3757_ = _args[29];
lean_object* v_numDiscrEqs_3758_ = _args[30];
lean_object* v_fst_3759_ = _args[31];
lean_object* v___f_3760_ = _args[32];
lean_object* v_matcherLevels_3761_ = _args[33];
_start:
{
uint8_t v___x_14587__boxed_3762_; uint8_t v_useSplitter_boxed_3763_; uint8_t v_isCasesOn_boxed_3764_; lean_object* v_res_3765_; 
v___x_14587__boxed_3762_ = lean_unbox(v___x_3745_);
v_useSplitter_boxed_3763_ = lean_unbox(v_useSplitter_3751_);
v_isCasesOn_boxed_3764_ = lean_unbox(v_isCasesOn_3752_);
v_res_3765_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3728_, v_numDiscrs_3729_, v_altInfos_3730_, v_uElimPos_x3f_3731_, v_snd_3732_, v_overlaps_3733_, v_matcherName_3734_, v_params_x27_3735_, v_fst_3736_, v_discrs_x27_3737_, v_toPure_3738_, v_onRemaining_3739_, v_remaining_3740_, v_toBind_3741_, v_inst_3742_, v_alts_3743_, v___f_3744_, v___x_14587__boxed_3762_, v_inst_3746_, v_onAlt_3747_, v_inst_3748_, v___f_3749_, v_matcherApp_3750_, v_useSplitter_boxed_3763_, v_isCasesOn_boxed_3764_, v___f_3753_, v___x_3754_, v___x_3755_, v_toMonadExceptOf_3756_, v___f_3757_, v_numDiscrEqs_3758_, v_fst_3759_, v___f_3760_, v_matcherLevels_3761_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v___f_3766_, lean_object* v_matcherLevels_3767_){
_start:
{
lean_object* v___x_3768_; 
v___x_3768_ = lean_apply_1(v___f_3766_, v_matcherLevels_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3769_, lean_object* v_matcherName_3770_, lean_object* v_params_x27_3771_, lean_object* v_discrs_x27_3772_, lean_object* v_toPure_3773_, lean_object* v_onRemaining_3774_, lean_object* v_remaining_3775_, lean_object* v_toBind_3776_, lean_object* v_inst_3777_, lean_object* v_alts_3778_, lean_object* v___f_3779_, uint8_t v___x_3780_, lean_object* v_inst_3781_, lean_object* v_onAlt_3782_, lean_object* v_inst_3783_, lean_object* v___f_3784_, lean_object* v_matcherApp_3785_, uint8_t v_useSplitter_3786_, uint8_t v_isCasesOn_3787_, lean_object* v___f_3788_, lean_object* v___x_3789_, lean_object* v___x_3790_, lean_object* v_toMonadExceptOf_3791_, lean_object* v___f_3792_, lean_object* v_numDiscrEqs_3793_, lean_object* v___f_3794_, lean_object* v_matcherLevels_3795_, lean_object* v_____x_3796_){
_start:
{
lean_object* v_snd_3797_; lean_object* v_snd_3798_; lean_object* v_fst_3799_; lean_object* v_fst_3800_; lean_object* v_fst_3801_; lean_object* v_snd_3802_; lean_object* v_numParams_3803_; lean_object* v_numDiscrs_3804_; lean_object* v_altInfos_3805_; lean_object* v_uElimPos_x3f_3806_; lean_object* v_overlaps_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___f_3811_; 
v_snd_3797_ = lean_ctor_get(v_____x_3796_, 1);
lean_inc(v_snd_3797_);
v_snd_3798_ = lean_ctor_get(v_snd_3797_, 1);
lean_inc(v_snd_3798_);
v_fst_3799_ = lean_ctor_get(v_____x_3796_, 0);
lean_inc(v_fst_3799_);
lean_dec_ref(v_____x_3796_);
v_fst_3800_ = lean_ctor_get(v_snd_3797_, 0);
lean_inc(v_fst_3800_);
lean_dec(v_snd_3797_);
v_fst_3801_ = lean_ctor_get(v_snd_3798_, 0);
lean_inc(v_fst_3801_);
v_snd_3802_ = lean_ctor_get(v_snd_3798_, 1);
lean_inc(v_snd_3802_);
lean_dec(v_snd_3798_);
v_numParams_3803_ = lean_ctor_get(v_toMatcherInfo_3769_, 0);
lean_inc(v_numParams_3803_);
v_numDiscrs_3804_ = lean_ctor_get(v_toMatcherInfo_3769_, 1);
lean_inc(v_numDiscrs_3804_);
v_altInfos_3805_ = lean_ctor_get(v_toMatcherInfo_3769_, 2);
lean_inc_ref(v_altInfos_3805_);
v_uElimPos_x3f_3806_ = lean_ctor_get(v_toMatcherInfo_3769_, 3);
lean_inc_n(v_uElimPos_x3f_3806_, 2);
v_overlaps_3807_ = lean_ctor_get(v_toMatcherInfo_3769_, 5);
lean_inc_ref(v_overlaps_3807_);
lean_dec_ref(v_toMatcherInfo_3769_);
v___x_3808_ = lean_box(v___x_3780_);
v___x_3809_ = lean_box(v_useSplitter_3786_);
v___x_3810_ = lean_box(v_isCasesOn_3787_);
lean_inc(v_toBind_3776_);
lean_inc(v_toPure_3773_);
v___f_3811_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 34, 33);
lean_closure_set(v___f_3811_, 0, v_numParams_3803_);
lean_closure_set(v___f_3811_, 1, v_numDiscrs_3804_);
lean_closure_set(v___f_3811_, 2, v_altInfos_3805_);
lean_closure_set(v___f_3811_, 3, v_uElimPos_x3f_3806_);
lean_closure_set(v___f_3811_, 4, v_snd_3802_);
lean_closure_set(v___f_3811_, 5, v_overlaps_3807_);
lean_closure_set(v___f_3811_, 6, v_matcherName_3770_);
lean_closure_set(v___f_3811_, 7, v_params_x27_3771_);
lean_closure_set(v___f_3811_, 8, v_fst_3799_);
lean_closure_set(v___f_3811_, 9, v_discrs_x27_3772_);
lean_closure_set(v___f_3811_, 10, v_toPure_3773_);
lean_closure_set(v___f_3811_, 11, v_onRemaining_3774_);
lean_closure_set(v___f_3811_, 12, v_remaining_3775_);
lean_closure_set(v___f_3811_, 13, v_toBind_3776_);
lean_closure_set(v___f_3811_, 14, v_inst_3777_);
lean_closure_set(v___f_3811_, 15, v_alts_3778_);
lean_closure_set(v___f_3811_, 16, v___f_3779_);
lean_closure_set(v___f_3811_, 17, v___x_3808_);
lean_closure_set(v___f_3811_, 18, v_inst_3781_);
lean_closure_set(v___f_3811_, 19, v_onAlt_3782_);
lean_closure_set(v___f_3811_, 20, v_inst_3783_);
lean_closure_set(v___f_3811_, 21, v___f_3784_);
lean_closure_set(v___f_3811_, 22, v_matcherApp_3785_);
lean_closure_set(v___f_3811_, 23, v___x_3809_);
lean_closure_set(v___f_3811_, 24, v___x_3810_);
lean_closure_set(v___f_3811_, 25, v___f_3788_);
lean_closure_set(v___f_3811_, 26, v___x_3789_);
lean_closure_set(v___f_3811_, 27, v___x_3790_);
lean_closure_set(v___f_3811_, 28, v_toMonadExceptOf_3791_);
lean_closure_set(v___f_3811_, 29, v___f_3792_);
lean_closure_set(v___f_3811_, 30, v_numDiscrEqs_3793_);
lean_closure_set(v___f_3811_, 31, v_fst_3801_);
lean_closure_set(v___f_3811_, 32, v___f_3794_);
if (lean_obj_tag(v_uElimPos_x3f_3806_) == 0)
{
lean_object* v___f_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
lean_dec(v_fst_3800_);
v___f_3812_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3812_, 0, v___f_3811_);
v___x_3813_ = lean_apply_2(v_toPure_3773_, lean_box(0), v_matcherLevels_3795_);
v___x_3814_ = lean_apply_4(v_toBind_3776_, lean_box(0), lean_box(0), v___x_3813_, v___f_3812_);
return v___x_3814_;
}
else
{
lean_object* v_val_3815_; lean_object* v___f_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_val_3815_ = lean_ctor_get(v_uElimPos_x3f_3806_, 0);
lean_inc(v_val_3815_);
lean_dec_ref_known(v_uElimPos_x3f_3806_, 1);
v___f_3816_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3816_, 0, v___f_3811_);
v___x_3817_ = lean_array_set(v_matcherLevels_3795_, v_val_3815_, v_fst_3800_);
lean_dec(v_val_3815_);
v___x_3818_ = lean_apply_2(v_toPure_3773_, lean_box(0), v___x_3817_);
v___x_3819_ = lean_apply_4(v_toBind_3776_, lean_box(0), lean_box(0), v___x_3818_, v___f_3816_);
return v___x_3819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3820_ = _args[0];
lean_object* v_matcherName_3821_ = _args[1];
lean_object* v_params_x27_3822_ = _args[2];
lean_object* v_discrs_x27_3823_ = _args[3];
lean_object* v_toPure_3824_ = _args[4];
lean_object* v_onRemaining_3825_ = _args[5];
lean_object* v_remaining_3826_ = _args[6];
lean_object* v_toBind_3827_ = _args[7];
lean_object* v_inst_3828_ = _args[8];
lean_object* v_alts_3829_ = _args[9];
lean_object* v___f_3830_ = _args[10];
lean_object* v___x_3831_ = _args[11];
lean_object* v_inst_3832_ = _args[12];
lean_object* v_onAlt_3833_ = _args[13];
lean_object* v_inst_3834_ = _args[14];
lean_object* v___f_3835_ = _args[15];
lean_object* v_matcherApp_3836_ = _args[16];
lean_object* v_useSplitter_3837_ = _args[17];
lean_object* v_isCasesOn_3838_ = _args[18];
lean_object* v___f_3839_ = _args[19];
lean_object* v___x_3840_ = _args[20];
lean_object* v___x_3841_ = _args[21];
lean_object* v_toMonadExceptOf_3842_ = _args[22];
lean_object* v___f_3843_ = _args[23];
lean_object* v_numDiscrEqs_3844_ = _args[24];
lean_object* v___f_3845_ = _args[25];
lean_object* v_matcherLevels_3846_ = _args[26];
lean_object* v_____x_3847_ = _args[27];
_start:
{
uint8_t v___x_14659__boxed_3848_; uint8_t v_useSplitter_boxed_3849_; uint8_t v_isCasesOn_boxed_3850_; lean_object* v_res_3851_; 
v___x_14659__boxed_3848_ = lean_unbox(v___x_3831_);
v_useSplitter_boxed_3849_ = lean_unbox(v_useSplitter_3837_);
v_isCasesOn_boxed_3850_ = lean_unbox(v_isCasesOn_3838_);
v_res_3851_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3820_, v_matcherName_3821_, v_params_x27_3822_, v_discrs_x27_3823_, v_toPure_3824_, v_onRemaining_3825_, v_remaining_3826_, v_toBind_3827_, v_inst_3828_, v_alts_3829_, v___f_3830_, v___x_14659__boxed_3848_, v_inst_3832_, v_onAlt_3833_, v_inst_3834_, v___f_3835_, v_matcherApp_3836_, v_useSplitter_boxed_3849_, v_isCasesOn_boxed_3850_, v___f_3839_, v___x_3840_, v___x_3841_, v_toMonadExceptOf_3842_, v___f_3843_, v_numDiscrEqs_3844_, v___f_3845_, v_matcherLevels_3846_, v_____x_3847_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3852_, lean_object* v_inst_3853_, lean_object* v_toBind_3854_, lean_object* v_toMatcherInfo_3855_, lean_object* v_inst_3856_, lean_object* v___f_3857_, lean_object* v_onMotive_3858_, lean_object* v_discrs_3859_, lean_object* v_inst_3860_, lean_object* v_matcherName_3861_, lean_object* v_params_x27_3862_, lean_object* v_onRemaining_3863_, lean_object* v_remaining_3864_, lean_object* v_inst_3865_, lean_object* v_alts_3866_, lean_object* v___f_3867_, lean_object* v_onAlt_3868_, lean_object* v___f_3869_, lean_object* v_matcherApp_3870_, uint8_t v_useSplitter_3871_, uint8_t v_isCasesOn_3872_, lean_object* v___f_3873_, lean_object* v___x_3874_, lean_object* v___x_3875_, lean_object* v_toMonadExceptOf_3876_, lean_object* v___f_3877_, lean_object* v_numDiscrEqs_3878_, lean_object* v___f_3879_, lean_object* v_matcherLevels_3880_, lean_object* v_motive_3881_, lean_object* v_discrs_x27_3882_){
_start:
{
lean_object* v___f_3883_; uint8_t v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___f_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_inc_ref_n(v_inst_3856_, 2);
lean_inc_ref(v_discrs_x27_3882_);
lean_inc_ref(v_toMatcherInfo_3855_);
lean_inc_n(v_toBind_3854_, 2);
lean_inc(v_inst_3853_);
lean_inc(v_toPure_3852_);
v___f_3883_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3883_, 0, v_toPure_3852_);
lean_closure_set(v___f_3883_, 1, v_inst_3853_);
lean_closure_set(v___f_3883_, 2, v_toBind_3854_);
lean_closure_set(v___f_3883_, 3, v_toMatcherInfo_3855_);
lean_closure_set(v___f_3883_, 4, v_discrs_x27_3882_);
lean_closure_set(v___f_3883_, 5, v_inst_3856_);
lean_closure_set(v___f_3883_, 6, v___f_3857_);
lean_closure_set(v___f_3883_, 7, v_onMotive_3858_);
lean_closure_set(v___f_3883_, 8, v_discrs_3859_);
lean_closure_set(v___f_3883_, 9, v_inst_3860_);
v___x_3884_ = 0;
v___x_3885_ = lean_box(v___x_3884_);
v___x_3886_ = lean_box(v_useSplitter_3871_);
v___x_3887_ = lean_box(v_isCasesOn_3872_);
lean_inc_ref(v_inst_3865_);
v___f_3888_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 28, 27);
lean_closure_set(v___f_3888_, 0, v_toMatcherInfo_3855_);
lean_closure_set(v___f_3888_, 1, v_matcherName_3861_);
lean_closure_set(v___f_3888_, 2, v_params_x27_3862_);
lean_closure_set(v___f_3888_, 3, v_discrs_x27_3882_);
lean_closure_set(v___f_3888_, 4, v_toPure_3852_);
lean_closure_set(v___f_3888_, 5, v_onRemaining_3863_);
lean_closure_set(v___f_3888_, 6, v_remaining_3864_);
lean_closure_set(v___f_3888_, 7, v_toBind_3854_);
lean_closure_set(v___f_3888_, 8, v_inst_3865_);
lean_closure_set(v___f_3888_, 9, v_alts_3866_);
lean_closure_set(v___f_3888_, 10, v___f_3867_);
lean_closure_set(v___f_3888_, 11, v___x_3885_);
lean_closure_set(v___f_3888_, 12, v_inst_3853_);
lean_closure_set(v___f_3888_, 13, v_onAlt_3868_);
lean_closure_set(v___f_3888_, 14, v_inst_3856_);
lean_closure_set(v___f_3888_, 15, v___f_3869_);
lean_closure_set(v___f_3888_, 16, v_matcherApp_3870_);
lean_closure_set(v___f_3888_, 17, v___x_3886_);
lean_closure_set(v___f_3888_, 18, v___x_3887_);
lean_closure_set(v___f_3888_, 19, v___f_3873_);
lean_closure_set(v___f_3888_, 20, v___x_3874_);
lean_closure_set(v___f_3888_, 21, v___x_3875_);
lean_closure_set(v___f_3888_, 22, v_toMonadExceptOf_3876_);
lean_closure_set(v___f_3888_, 23, v___f_3877_);
lean_closure_set(v___f_3888_, 24, v_numDiscrEqs_3878_);
lean_closure_set(v___f_3888_, 25, v___f_3879_);
lean_closure_set(v___f_3888_, 26, v_matcherLevels_3880_);
v___x_3889_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3865_, v_inst_3856_, v_motive_3881_, v___f_3883_, v___x_3884_);
v___x_3890_ = lean_apply_4(v_toBind_3854_, lean_box(0), lean_box(0), v___x_3889_, v___f_3888_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3891_ = _args[0];
lean_object* v_inst_3892_ = _args[1];
lean_object* v_toBind_3893_ = _args[2];
lean_object* v_toMatcherInfo_3894_ = _args[3];
lean_object* v_inst_3895_ = _args[4];
lean_object* v___f_3896_ = _args[5];
lean_object* v_onMotive_3897_ = _args[6];
lean_object* v_discrs_3898_ = _args[7];
lean_object* v_inst_3899_ = _args[8];
lean_object* v_matcherName_3900_ = _args[9];
lean_object* v_params_x27_3901_ = _args[10];
lean_object* v_onRemaining_3902_ = _args[11];
lean_object* v_remaining_3903_ = _args[12];
lean_object* v_inst_3904_ = _args[13];
lean_object* v_alts_3905_ = _args[14];
lean_object* v___f_3906_ = _args[15];
lean_object* v_onAlt_3907_ = _args[16];
lean_object* v___f_3908_ = _args[17];
lean_object* v_matcherApp_3909_ = _args[18];
lean_object* v_useSplitter_3910_ = _args[19];
lean_object* v_isCasesOn_3911_ = _args[20];
lean_object* v___f_3912_ = _args[21];
lean_object* v___x_3913_ = _args[22];
lean_object* v___x_3914_ = _args[23];
lean_object* v_toMonadExceptOf_3915_ = _args[24];
lean_object* v___f_3916_ = _args[25];
lean_object* v_numDiscrEqs_3917_ = _args[26];
lean_object* v___f_3918_ = _args[27];
lean_object* v_matcherLevels_3919_ = _args[28];
lean_object* v_motive_3920_ = _args[29];
lean_object* v_discrs_x27_3921_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3922_; uint8_t v_isCasesOn_boxed_3923_; lean_object* v_res_3924_; 
v_useSplitter_boxed_3922_ = lean_unbox(v_useSplitter_3910_);
v_isCasesOn_boxed_3923_ = lean_unbox(v_isCasesOn_3911_);
v_res_3924_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3891_, v_inst_3892_, v_toBind_3893_, v_toMatcherInfo_3894_, v_inst_3895_, v___f_3896_, v_onMotive_3897_, v_discrs_3898_, v_inst_3899_, v_matcherName_3900_, v_params_x27_3901_, v_onRemaining_3902_, v_remaining_3903_, v_inst_3904_, v_alts_3905_, v___f_3906_, v_onAlt_3907_, v___f_3908_, v_matcherApp_3909_, v_useSplitter_boxed_3922_, v_isCasesOn_boxed_3923_, v___f_3912_, v___x_3913_, v___x_3914_, v_toMonadExceptOf_3915_, v___f_3916_, v_numDiscrEqs_3917_, v___f_3918_, v_matcherLevels_3919_, v_motive_3920_, v_discrs_x27_3921_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3925_, lean_object* v_inst_3926_, lean_object* v_toBind_3927_, lean_object* v_toMatcherInfo_3928_, lean_object* v_inst_3929_, lean_object* v___f_3930_, lean_object* v_onMotive_3931_, lean_object* v_discrs_3932_, lean_object* v_inst_3933_, lean_object* v_matcherName_3934_, lean_object* v_onRemaining_3935_, lean_object* v_remaining_3936_, lean_object* v_inst_3937_, lean_object* v_alts_3938_, lean_object* v___f_3939_, lean_object* v_onAlt_3940_, lean_object* v___f_3941_, lean_object* v_matcherApp_3942_, uint8_t v_useSplitter_3943_, uint8_t v_isCasesOn_3944_, lean_object* v___f_3945_, lean_object* v___x_3946_, lean_object* v___x_3947_, lean_object* v_toMonadExceptOf_3948_, lean_object* v___f_3949_, lean_object* v_numDiscrEqs_3950_, lean_object* v___f_3951_, lean_object* v_matcherLevels_3952_, lean_object* v_motive_3953_, lean_object* v_onParams_3954_, lean_object* v_params_x27_3955_){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___f_3958_; size_t v_sz_3959_; size_t v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3956_ = lean_box(v_useSplitter_3943_);
v___x_3957_ = lean_box(v_isCasesOn_3944_);
lean_inc_ref(v_discrs_3932_);
lean_inc_ref(v_inst_3929_);
lean_inc(v_toBind_3927_);
v___f_3958_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 31, 30);
lean_closure_set(v___f_3958_, 0, v_toPure_3925_);
lean_closure_set(v___f_3958_, 1, v_inst_3926_);
lean_closure_set(v___f_3958_, 2, v_toBind_3927_);
lean_closure_set(v___f_3958_, 3, v_toMatcherInfo_3928_);
lean_closure_set(v___f_3958_, 4, v_inst_3929_);
lean_closure_set(v___f_3958_, 5, v___f_3930_);
lean_closure_set(v___f_3958_, 6, v_onMotive_3931_);
lean_closure_set(v___f_3958_, 7, v_discrs_3932_);
lean_closure_set(v___f_3958_, 8, v_inst_3933_);
lean_closure_set(v___f_3958_, 9, v_matcherName_3934_);
lean_closure_set(v___f_3958_, 10, v_params_x27_3955_);
lean_closure_set(v___f_3958_, 11, v_onRemaining_3935_);
lean_closure_set(v___f_3958_, 12, v_remaining_3936_);
lean_closure_set(v___f_3958_, 13, v_inst_3937_);
lean_closure_set(v___f_3958_, 14, v_alts_3938_);
lean_closure_set(v___f_3958_, 15, v___f_3939_);
lean_closure_set(v___f_3958_, 16, v_onAlt_3940_);
lean_closure_set(v___f_3958_, 17, v___f_3941_);
lean_closure_set(v___f_3958_, 18, v_matcherApp_3942_);
lean_closure_set(v___f_3958_, 19, v___x_3956_);
lean_closure_set(v___f_3958_, 20, v___x_3957_);
lean_closure_set(v___f_3958_, 21, v___f_3945_);
lean_closure_set(v___f_3958_, 22, v___x_3946_);
lean_closure_set(v___f_3958_, 23, v___x_3947_);
lean_closure_set(v___f_3958_, 24, v_toMonadExceptOf_3948_);
lean_closure_set(v___f_3958_, 25, v___f_3949_);
lean_closure_set(v___f_3958_, 26, v_numDiscrEqs_3950_);
lean_closure_set(v___f_3958_, 27, v___f_3951_);
lean_closure_set(v___f_3958_, 28, v_matcherLevels_3952_);
lean_closure_set(v___f_3958_, 29, v_motive_3953_);
v_sz_3959_ = lean_array_size(v_discrs_3932_);
v___x_3960_ = ((size_t)0ULL);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3929_, v_onParams_3954_, v_sz_3959_, v___x_3960_, v_discrs_3932_);
v___x_3962_ = lean_apply_4(v_toBind_3927_, lean_box(0), lean_box(0), v___x_3961_, v___f_3958_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3963_ = _args[0];
lean_object* v_inst_3964_ = _args[1];
lean_object* v_toBind_3965_ = _args[2];
lean_object* v_toMatcherInfo_3966_ = _args[3];
lean_object* v_inst_3967_ = _args[4];
lean_object* v___f_3968_ = _args[5];
lean_object* v_onMotive_3969_ = _args[6];
lean_object* v_discrs_3970_ = _args[7];
lean_object* v_inst_3971_ = _args[8];
lean_object* v_matcherName_3972_ = _args[9];
lean_object* v_onRemaining_3973_ = _args[10];
lean_object* v_remaining_3974_ = _args[11];
lean_object* v_inst_3975_ = _args[12];
lean_object* v_alts_3976_ = _args[13];
lean_object* v___f_3977_ = _args[14];
lean_object* v_onAlt_3978_ = _args[15];
lean_object* v___f_3979_ = _args[16];
lean_object* v_matcherApp_3980_ = _args[17];
lean_object* v_useSplitter_3981_ = _args[18];
lean_object* v_isCasesOn_3982_ = _args[19];
lean_object* v___f_3983_ = _args[20];
lean_object* v___x_3984_ = _args[21];
lean_object* v___x_3985_ = _args[22];
lean_object* v_toMonadExceptOf_3986_ = _args[23];
lean_object* v___f_3987_ = _args[24];
lean_object* v_numDiscrEqs_3988_ = _args[25];
lean_object* v___f_3989_ = _args[26];
lean_object* v_matcherLevels_3990_ = _args[27];
lean_object* v_motive_3991_ = _args[28];
lean_object* v_onParams_3992_ = _args[29];
lean_object* v_params_x27_3993_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3994_; uint8_t v_isCasesOn_boxed_3995_; lean_object* v_res_3996_; 
v_useSplitter_boxed_3994_ = lean_unbox(v_useSplitter_3981_);
v_isCasesOn_boxed_3995_ = lean_unbox(v_isCasesOn_3982_);
v_res_3996_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3963_, v_inst_3964_, v_toBind_3965_, v_toMatcherInfo_3966_, v_inst_3967_, v___f_3968_, v_onMotive_3969_, v_discrs_3970_, v_inst_3971_, v_matcherName_3972_, v_onRemaining_3973_, v_remaining_3974_, v_inst_3975_, v_alts_3976_, v___f_3977_, v_onAlt_3978_, v___f_3979_, v_matcherApp_3980_, v_useSplitter_boxed_3994_, v_isCasesOn_boxed_3995_, v___f_3983_, v___x_3984_, v___x_3985_, v_toMonadExceptOf_3986_, v___f_3987_, v_numDiscrEqs_3988_, v___f_3989_, v_matcherLevels_3990_, v_motive_3991_, v_onParams_3992_, v_params_x27_3993_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_3997_, lean_object* v_inst_3998_, lean_object* v_toBind_3999_, lean_object* v_toMatcherInfo_4000_, lean_object* v_inst_4001_, lean_object* v___f_4002_, lean_object* v_onMotive_4003_, lean_object* v_discrs_4004_, lean_object* v_inst_4005_, lean_object* v_matcherName_4006_, lean_object* v_onRemaining_4007_, lean_object* v_remaining_4008_, lean_object* v_inst_4009_, lean_object* v_alts_4010_, lean_object* v___f_4011_, lean_object* v_onAlt_4012_, lean_object* v___f_4013_, lean_object* v_matcherApp_4014_, uint8_t v_useSplitter_4015_, uint8_t v_isCasesOn_4016_, lean_object* v___f_4017_, lean_object* v___x_4018_, lean_object* v___x_4019_, lean_object* v_toMonadExceptOf_4020_, lean_object* v___f_4021_, lean_object* v___f_4022_, lean_object* v_matcherLevels_4023_, lean_object* v_motive_4024_, lean_object* v_onParams_4025_, lean_object* v_params_4026_, lean_object* v_numDiscrEqs_4027_){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___f_4030_; size_t v_sz_4031_; size_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4028_ = lean_box(v_useSplitter_4015_);
v___x_4029_ = lean_box(v_isCasesOn_4016_);
lean_inc(v_onParams_4025_);
lean_inc_ref(v_inst_4001_);
lean_inc(v_toBind_3999_);
v___f_4030_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 31, 30);
lean_closure_set(v___f_4030_, 0, v_toPure_3997_);
lean_closure_set(v___f_4030_, 1, v_inst_3998_);
lean_closure_set(v___f_4030_, 2, v_toBind_3999_);
lean_closure_set(v___f_4030_, 3, v_toMatcherInfo_4000_);
lean_closure_set(v___f_4030_, 4, v_inst_4001_);
lean_closure_set(v___f_4030_, 5, v___f_4002_);
lean_closure_set(v___f_4030_, 6, v_onMotive_4003_);
lean_closure_set(v___f_4030_, 7, v_discrs_4004_);
lean_closure_set(v___f_4030_, 8, v_inst_4005_);
lean_closure_set(v___f_4030_, 9, v_matcherName_4006_);
lean_closure_set(v___f_4030_, 10, v_onRemaining_4007_);
lean_closure_set(v___f_4030_, 11, v_remaining_4008_);
lean_closure_set(v___f_4030_, 12, v_inst_4009_);
lean_closure_set(v___f_4030_, 13, v_alts_4010_);
lean_closure_set(v___f_4030_, 14, v___f_4011_);
lean_closure_set(v___f_4030_, 15, v_onAlt_4012_);
lean_closure_set(v___f_4030_, 16, v___f_4013_);
lean_closure_set(v___f_4030_, 17, v_matcherApp_4014_);
lean_closure_set(v___f_4030_, 18, v___x_4028_);
lean_closure_set(v___f_4030_, 19, v___x_4029_);
lean_closure_set(v___f_4030_, 20, v___f_4017_);
lean_closure_set(v___f_4030_, 21, v___x_4018_);
lean_closure_set(v___f_4030_, 22, v___x_4019_);
lean_closure_set(v___f_4030_, 23, v_toMonadExceptOf_4020_);
lean_closure_set(v___f_4030_, 24, v___f_4021_);
lean_closure_set(v___f_4030_, 25, v_numDiscrEqs_4027_);
lean_closure_set(v___f_4030_, 26, v___f_4022_);
lean_closure_set(v___f_4030_, 27, v_matcherLevels_4023_);
lean_closure_set(v___f_4030_, 28, v_motive_4024_);
lean_closure_set(v___f_4030_, 29, v_onParams_4025_);
v_sz_4031_ = lean_array_size(v_params_4026_);
v___x_4032_ = ((size_t)0ULL);
v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4001_, v_onParams_4025_, v_sz_4031_, v___x_4032_, v_params_4026_);
v___x_4034_ = lean_apply_4(v_toBind_3999_, lean_box(0), lean_box(0), v___x_4033_, v___f_4030_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4035_ = _args[0];
lean_object* v_inst_4036_ = _args[1];
lean_object* v_toBind_4037_ = _args[2];
lean_object* v_toMatcherInfo_4038_ = _args[3];
lean_object* v_inst_4039_ = _args[4];
lean_object* v___f_4040_ = _args[5];
lean_object* v_onMotive_4041_ = _args[6];
lean_object* v_discrs_4042_ = _args[7];
lean_object* v_inst_4043_ = _args[8];
lean_object* v_matcherName_4044_ = _args[9];
lean_object* v_onRemaining_4045_ = _args[10];
lean_object* v_remaining_4046_ = _args[11];
lean_object* v_inst_4047_ = _args[12];
lean_object* v_alts_4048_ = _args[13];
lean_object* v___f_4049_ = _args[14];
lean_object* v_onAlt_4050_ = _args[15];
lean_object* v___f_4051_ = _args[16];
lean_object* v_matcherApp_4052_ = _args[17];
lean_object* v_useSplitter_4053_ = _args[18];
lean_object* v_isCasesOn_4054_ = _args[19];
lean_object* v___f_4055_ = _args[20];
lean_object* v___x_4056_ = _args[21];
lean_object* v___x_4057_ = _args[22];
lean_object* v_toMonadExceptOf_4058_ = _args[23];
lean_object* v___f_4059_ = _args[24];
lean_object* v___f_4060_ = _args[25];
lean_object* v_matcherLevels_4061_ = _args[26];
lean_object* v_motive_4062_ = _args[27];
lean_object* v_onParams_4063_ = _args[28];
lean_object* v_params_4064_ = _args[29];
lean_object* v_numDiscrEqs_4065_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4066_; uint8_t v_isCasesOn_boxed_4067_; lean_object* v_res_4068_; 
v_useSplitter_boxed_4066_ = lean_unbox(v_useSplitter_4053_);
v_isCasesOn_boxed_4067_ = lean_unbox(v_isCasesOn_4054_);
v_res_4068_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4035_, v_inst_4036_, v_toBind_4037_, v_toMatcherInfo_4038_, v_inst_4039_, v___f_4040_, v_onMotive_4041_, v_discrs_4042_, v_inst_4043_, v_matcherName_4044_, v_onRemaining_4045_, v_remaining_4046_, v_inst_4047_, v_alts_4048_, v___f_4049_, v_onAlt_4050_, v___f_4051_, v_matcherApp_4052_, v_useSplitter_boxed_4066_, v_isCasesOn_boxed_4067_, v___f_4055_, v___x_4056_, v___x_4057_, v_toMonadExceptOf_4058_, v___f_4059_, v___f_4060_, v_matcherLevels_4061_, v_motive_4062_, v_onParams_4063_, v_params_4064_, v_numDiscrEqs_4065_);
return v_res_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4069_, lean_object* v_numDiscrEqs_4070_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = lean_apply_1(v___f_4069_, v_numDiscrEqs_4070_);
return v___x_4071_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4074_ = l_Lean_stringToMessageData(v___x_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4077_ = l_Lean_stringToMessageData(v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4078_, lean_object* v_inst_4079_, lean_object* v_inst_4080_, lean_object* v_toBind_4081_, lean_object* v___f_4082_, lean_object* v_toPure_4083_, lean_object* v___f_4084_, lean_object* v_____do__lift_4085_){
_start:
{
if (lean_obj_tag(v_____do__lift_4085_) == 0)
{
lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
lean_dec(v___f_4084_);
lean_dec(v_toPure_4083_);
v___x_4086_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4087_ = l_Lean_MessageData_ofName(v_matcherName_4078_);
v___x_4088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4086_);
lean_ctor_set(v___x_4088_, 1, v___x_4087_);
v___x_4089_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = l_Lean_throwError___redArg(v_inst_4079_, v_inst_4080_, v___x_4090_);
v___x_4092_ = lean_apply_4(v_toBind_4081_, lean_box(0), lean_box(0), v___x_4091_, v___f_4082_);
return v___x_4092_;
}
else
{
lean_object* v_val_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec(v___f_4082_);
lean_dec_ref(v_inst_4080_);
lean_dec_ref(v_inst_4079_);
lean_dec(v_matcherName_4078_);
v_val_4093_ = lean_ctor_get(v_____do__lift_4085_, 0);
v___x_4094_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4093_);
v___x_4095_ = lean_apply_2(v_toPure_4083_, lean_box(0), v___x_4094_);
v___x_4096_ = lean_apply_4(v_toBind_4081_, lean_box(0), lean_box(0), v___x_4095_, v___f_4084_);
return v___x_4096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4097_, lean_object* v_inst_4098_, lean_object* v_inst_4099_, lean_object* v_toBind_4100_, lean_object* v___f_4101_, lean_object* v_toPure_4102_, lean_object* v___f_4103_, lean_object* v_____do__lift_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4097_, v_inst_4098_, v_inst_4099_, v_toBind_4100_, v___f_4101_, v_toPure_4102_, v___f_4103_, v_____do__lift_4104_);
lean_dec(v_____do__lift_4104_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4106_, lean_object* v_toPure_4107_, lean_object* v_inst_4108_, lean_object* v_toBind_4109_, lean_object* v_inst_4110_, lean_object* v___f_4111_, lean_object* v_onMotive_4112_, lean_object* v_inst_4113_, lean_object* v_onRemaining_4114_, lean_object* v_inst_4115_, lean_object* v___f_4116_, lean_object* v_onAlt_4117_, lean_object* v___f_4118_, uint8_t v_useSplitter_4119_, lean_object* v___f_4120_, lean_object* v___x_4121_, lean_object* v___x_4122_, lean_object* v_toMonadExceptOf_4123_, lean_object* v___f_4124_, lean_object* v___f_4125_, lean_object* v_onParams_4126_, lean_object* v_inst_4127_, lean_object* v_____do__lift_4128_){
_start:
{
lean_object* v_toMatcherInfo_4129_; lean_object* v_matcherName_4130_; lean_object* v_matcherLevels_4131_; lean_object* v_params_4132_; lean_object* v_motive_4133_; lean_object* v_discrs_4134_; lean_object* v_alts_4135_; lean_object* v_remaining_4136_; uint8_t v_isCasesOn_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___f_4140_; 
v_toMatcherInfo_4129_ = lean_ctor_get(v_matcherApp_4106_, 0);
lean_inc_ref(v_toMatcherInfo_4129_);
v_matcherName_4130_ = lean_ctor_get(v_matcherApp_4106_, 1);
lean_inc_n(v_matcherName_4130_, 3);
v_matcherLevels_4131_ = lean_ctor_get(v_matcherApp_4106_, 2);
lean_inc_ref(v_matcherLevels_4131_);
v_params_4132_ = lean_ctor_get(v_matcherApp_4106_, 3);
lean_inc_ref(v_params_4132_);
v_motive_4133_ = lean_ctor_get(v_matcherApp_4106_, 4);
lean_inc_ref(v_motive_4133_);
v_discrs_4134_ = lean_ctor_get(v_matcherApp_4106_, 5);
lean_inc_ref(v_discrs_4134_);
v_alts_4135_ = lean_ctor_get(v_matcherApp_4106_, 6);
lean_inc_ref(v_alts_4135_);
v_remaining_4136_ = lean_ctor_get(v_matcherApp_4106_, 7);
lean_inc_ref(v_remaining_4136_);
v_isCasesOn_4137_ = l_Lean_isCasesOnRecursor(v_____do__lift_4128_, v_matcherName_4130_);
v___x_4138_ = lean_box(v_useSplitter_4119_);
v___x_4139_ = lean_box(v_isCasesOn_4137_);
lean_inc_ref(v_inst_4113_);
lean_inc_ref(v_inst_4110_);
lean_inc(v_toBind_4109_);
lean_inc(v_toPure_4107_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 31, 30);
lean_closure_set(v___f_4140_, 0, v_toPure_4107_);
lean_closure_set(v___f_4140_, 1, v_inst_4108_);
lean_closure_set(v___f_4140_, 2, v_toBind_4109_);
lean_closure_set(v___f_4140_, 3, v_toMatcherInfo_4129_);
lean_closure_set(v___f_4140_, 4, v_inst_4110_);
lean_closure_set(v___f_4140_, 5, v___f_4111_);
lean_closure_set(v___f_4140_, 6, v_onMotive_4112_);
lean_closure_set(v___f_4140_, 7, v_discrs_4134_);
lean_closure_set(v___f_4140_, 8, v_inst_4113_);
lean_closure_set(v___f_4140_, 9, v_matcherName_4130_);
lean_closure_set(v___f_4140_, 10, v_onRemaining_4114_);
lean_closure_set(v___f_4140_, 11, v_remaining_4136_);
lean_closure_set(v___f_4140_, 12, v_inst_4115_);
lean_closure_set(v___f_4140_, 13, v_alts_4135_);
lean_closure_set(v___f_4140_, 14, v___f_4116_);
lean_closure_set(v___f_4140_, 15, v_onAlt_4117_);
lean_closure_set(v___f_4140_, 16, v___f_4118_);
lean_closure_set(v___f_4140_, 17, v_matcherApp_4106_);
lean_closure_set(v___f_4140_, 18, v___x_4138_);
lean_closure_set(v___f_4140_, 19, v___x_4139_);
lean_closure_set(v___f_4140_, 20, v___f_4120_);
lean_closure_set(v___f_4140_, 21, v___x_4121_);
lean_closure_set(v___f_4140_, 22, v___x_4122_);
lean_closure_set(v___f_4140_, 23, v_toMonadExceptOf_4123_);
lean_closure_set(v___f_4140_, 24, v___f_4124_);
lean_closure_set(v___f_4140_, 25, v___f_4125_);
lean_closure_set(v___f_4140_, 26, v_matcherLevels_4131_);
lean_closure_set(v___f_4140_, 27, v_motive_4133_);
lean_closure_set(v___f_4140_, 28, v_onParams_4126_);
lean_closure_set(v___f_4140_, 29, v_params_4132_);
if (v_isCasesOn_4137_ == 0)
{
lean_object* v___f_4141_; lean_object* v___f_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___f_4141_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4141_, 0, v___f_4140_);
lean_inc_ref(v___f_4141_);
lean_inc(v_toBind_4109_);
lean_inc_ref(v_inst_4110_);
lean_inc(v_matcherName_4130_);
v___f_4142_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4142_, 0, v_matcherName_4130_);
lean_closure_set(v___f_4142_, 1, v_inst_4110_);
lean_closure_set(v___f_4142_, 2, v_inst_4113_);
lean_closure_set(v___f_4142_, 3, v_toBind_4109_);
lean_closure_set(v___f_4142_, 4, v___f_4141_);
lean_closure_set(v___f_4142_, 5, v_toPure_4107_);
lean_closure_set(v___f_4142_, 6, v___f_4141_);
v___x_4143_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4110_, v_inst_4127_, v_matcherName_4130_);
v___x_4144_ = lean_apply_4(v_toBind_4109_, lean_box(0), lean_box(0), v___x_4143_, v___f_4142_);
return v___x_4144_;
}
else
{
lean_object* v___f_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_dec(v_matcherName_4130_);
lean_dec_ref(v_inst_4127_);
lean_dec_ref(v_inst_4113_);
lean_dec_ref(v_inst_4110_);
v___f_4145_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4145_, 0, v___f_4140_);
v___x_4146_ = lean_unsigned_to_nat(0u);
v___x_4147_ = lean_apply_2(v_toPure_4107_, lean_box(0), v___x_4146_);
v___x_4148_ = lean_apply_4(v_toBind_4109_, lean_box(0), lean_box(0), v___x_4147_, v___f_4145_);
return v___x_4148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4149_ = _args[0];
lean_object* v_toPure_4150_ = _args[1];
lean_object* v_inst_4151_ = _args[2];
lean_object* v_toBind_4152_ = _args[3];
lean_object* v_inst_4153_ = _args[4];
lean_object* v___f_4154_ = _args[5];
lean_object* v_onMotive_4155_ = _args[6];
lean_object* v_inst_4156_ = _args[7];
lean_object* v_onRemaining_4157_ = _args[8];
lean_object* v_inst_4158_ = _args[9];
lean_object* v___f_4159_ = _args[10];
lean_object* v_onAlt_4160_ = _args[11];
lean_object* v___f_4161_ = _args[12];
lean_object* v_useSplitter_4162_ = _args[13];
lean_object* v___f_4163_ = _args[14];
lean_object* v___x_4164_ = _args[15];
lean_object* v___x_4165_ = _args[16];
lean_object* v_toMonadExceptOf_4166_ = _args[17];
lean_object* v___f_4167_ = _args[18];
lean_object* v___f_4168_ = _args[19];
lean_object* v_onParams_4169_ = _args[20];
lean_object* v_inst_4170_ = _args[21];
lean_object* v_____do__lift_4171_ = _args[22];
_start:
{
uint8_t v_useSplitter_boxed_4172_; lean_object* v_res_4173_; 
v_useSplitter_boxed_4172_ = lean_unbox(v_useSplitter_4162_);
v_res_4173_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4149_, v_toPure_4150_, v_inst_4151_, v_toBind_4152_, v_inst_4153_, v___f_4154_, v_onMotive_4155_, v_inst_4156_, v_onRemaining_4157_, v_inst_4158_, v___f_4159_, v_onAlt_4160_, v___f_4161_, v_useSplitter_boxed_4172_, v___f_4163_, v___x_4164_, v___x_4165_, v_toMonadExceptOf_4166_, v___f_4167_, v___f_4168_, v_onParams_4169_, v_inst_4170_, v_____do__lift_4171_);
return v_res_4173_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_4174_; 
v___x_4174_ = l_Subarray_empty___redArg();
return v___x_4174_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4175_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
return v___x_4176_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4177_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1);
v___x_4178_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
lean_ctor_set(v___x_4179_, 1, v___x_4177_);
return v___x_4179_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3(void){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Array_instInhabited___redArg();
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2);
v___x_4182_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4181_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5(void){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4);
v___x_4185_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v___x_4184_);
return v___x_4186_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4187_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5);
v___x_4188_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3);
v___x_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
lean_ctor_set(v___x_4189_, 1, v___x_4187_);
return v___x_4189_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6);
v___x_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4192_, lean_object* v_inst_4193_, lean_object* v_inst_4194_, lean_object* v_inst_4195_, lean_object* v_inst_4196_, lean_object* v_matcherApp_4197_, uint8_t v_useSplitter_4198_, uint8_t v_addEqualities_4199_, lean_object* v_onParams_4200_, lean_object* v_onMotive_4201_, lean_object* v_onAlt_4202_, lean_object* v_onRemaining_4203_){
_start:
{
lean_object* v_toApplicative_4204_; lean_object* v_toBind_4205_; lean_object* v_getEnv_4206_; lean_object* v_toPure_4207_; lean_object* v_toMonadExceptOf_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___f_4211_; lean_object* v___f_4212_; lean_object* v___f_4213_; lean_object* v___x_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___f_4217_; lean_object* v___f_4218_; lean_object* v___f_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; 
v_toApplicative_4204_ = lean_ctor_get(v_inst_4194_, 0);
v_toBind_4205_ = lean_ctor_get(v_inst_4194_, 1);
lean_inc_n(v_toBind_4205_, 4);
v_getEnv_4206_ = lean_ctor_get(v_inst_4196_, 0);
lean_inc(v_getEnv_4206_);
v_toPure_4207_ = lean_ctor_get(v_toApplicative_4204_, 1);
lean_inc_n(v_toPure_4207_, 5);
v_toMonadExceptOf_4208_ = lean_ctor_get(v_inst_4195_, 0);
lean_inc_ref(v_toMonadExceptOf_4208_);
v___x_4209_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
lean_inc_ref_n(v_inst_4194_, 4);
v___x_4210_ = l_instInhabitedOfMonad___redArg(v_inst_4194_, v___x_4209_);
lean_inc_ref(v_inst_4195_);
v___f_4211_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4211_, 0, v_inst_4194_);
lean_closure_set(v___f_4211_, 1, v_inst_4195_);
lean_inc_n(v_inst_4192_, 3);
v___f_4212_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4212_, 0, v_inst_4192_);
v___f_4213_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4213_, 0, v_inst_4194_);
lean_closure_set(v___f_4213_, 1, v___f_4212_);
v___x_4214_ = l_Lean_instInhabitedExpr;
v___f_4215_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 6, 3);
lean_closure_set(v___f_4215_, 0, v_toPure_4207_);
lean_closure_set(v___f_4215_, 1, v_inst_4192_);
lean_closure_set(v___f_4215_, 2, v_toBind_4205_);
v___x_4216_ = lean_box(v_addEqualities_4199_);
v___f_4217_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4217_, 0, v_toPure_4207_);
lean_closure_set(v___f_4217_, 1, v___x_4216_);
lean_closure_set(v___f_4217_, 2, v_inst_4192_);
lean_closure_set(v___f_4217_, 3, v_toBind_4205_);
v___f_4218_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11), 2, 1);
lean_closure_set(v___f_4218_, 0, v_toPure_4207_);
v___f_4219_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 2, 1);
lean_closure_set(v___f_4219_, 0, v_toPure_4207_);
v___x_4220_ = l_instInhabitedOfMonad___redArg(v_inst_4194_, v___x_4214_);
v___x_4221_ = lean_box(v_useSplitter_4198_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 23, 22);
lean_closure_set(v___f_4222_, 0, v_matcherApp_4197_);
lean_closure_set(v___f_4222_, 1, v_toPure_4207_);
lean_closure_set(v___f_4222_, 2, v_inst_4192_);
lean_closure_set(v___f_4222_, 3, v_toBind_4205_);
lean_closure_set(v___f_4222_, 4, v_inst_4194_);
lean_closure_set(v___f_4222_, 5, v___f_4217_);
lean_closure_set(v___f_4222_, 6, v_onMotive_4201_);
lean_closure_set(v___f_4222_, 7, v_inst_4195_);
lean_closure_set(v___f_4222_, 8, v_onRemaining_4203_);
lean_closure_set(v___f_4222_, 9, v_inst_4193_);
lean_closure_set(v___f_4222_, 10, v___f_4219_);
lean_closure_set(v___f_4222_, 11, v_onAlt_4202_);
lean_closure_set(v___f_4222_, 12, v___f_4213_);
lean_closure_set(v___f_4222_, 13, v___x_4221_);
lean_closure_set(v___f_4222_, 14, v___f_4218_);
lean_closure_set(v___f_4222_, 15, v___x_4210_);
lean_closure_set(v___f_4222_, 16, v___x_4220_);
lean_closure_set(v___f_4222_, 17, v_toMonadExceptOf_4208_);
lean_closure_set(v___f_4222_, 18, v___f_4211_);
lean_closure_set(v___f_4222_, 19, v___f_4215_);
lean_closure_set(v___f_4222_, 20, v_onParams_4200_);
lean_closure_set(v___f_4222_, 21, v_inst_4196_);
v___x_4223_ = lean_apply_4(v_toBind_4205_, lean_box(0), lean_box(0), v_getEnv_4206_, v___f_4222_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4224_, lean_object* v_inst_4225_, lean_object* v_inst_4226_, lean_object* v_inst_4227_, lean_object* v_inst_4228_, lean_object* v_matcherApp_4229_, lean_object* v_useSplitter_4230_, lean_object* v_addEqualities_4231_, lean_object* v_onParams_4232_, lean_object* v_onMotive_4233_, lean_object* v_onAlt_4234_, lean_object* v_onRemaining_4235_){
_start:
{
uint8_t v_useSplitter_boxed_4236_; uint8_t v_addEqualities_boxed_4237_; lean_object* v_res_4238_; 
v_useSplitter_boxed_4236_ = lean_unbox(v_useSplitter_4230_);
v_addEqualities_boxed_4237_ = lean_unbox(v_addEqualities_4231_);
v_res_4238_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4224_, v_inst_4225_, v_inst_4226_, v_inst_4227_, v_inst_4228_, v_matcherApp_4229_, v_useSplitter_boxed_4236_, v_addEqualities_boxed_4237_, v_onParams_4232_, v_onMotive_4233_, v_onAlt_4234_, v_onRemaining_4235_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4239_, lean_object* v_inst_4240_, lean_object* v_inst_4241_, lean_object* v_inst_4242_, lean_object* v_inst_4243_, lean_object* v_inst_4244_, lean_object* v_inst_4245_, lean_object* v_inst_4246_, lean_object* v_inst_4247_, lean_object* v_matcherApp_4248_, uint8_t v_useSplitter_4249_, uint8_t v_addEqualities_4250_, lean_object* v_onParams_4251_, lean_object* v_onMotive_4252_, lean_object* v_onAlt_4253_, lean_object* v_onRemaining_4254_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4240_, v_inst_4241_, v_inst_4242_, v_inst_4243_, v_inst_4244_, v_matcherApp_4248_, v_useSplitter_4249_, v_addEqualities_4250_, v_onParams_4251_, v_onMotive_4252_, v_onAlt_4253_, v_onRemaining_4254_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4256_, lean_object* v_inst_4257_, lean_object* v_inst_4258_, lean_object* v_inst_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_inst_4263_, lean_object* v_inst_4264_, lean_object* v_matcherApp_4265_, lean_object* v_useSplitter_4266_, lean_object* v_addEqualities_4267_, lean_object* v_onParams_4268_, lean_object* v_onMotive_4269_, lean_object* v_onAlt_4270_, lean_object* v_onRemaining_4271_){
_start:
{
uint8_t v_useSplitter_boxed_4272_; uint8_t v_addEqualities_boxed_4273_; lean_object* v_res_4274_; 
v_useSplitter_boxed_4272_ = lean_unbox(v_useSplitter_4266_);
v_addEqualities_boxed_4273_ = lean_unbox(v_addEqualities_4267_);
v_res_4274_ = l_Lean_Meta_MatcherApp_transform(v_n_4256_, v_inst_4257_, v_inst_4258_, v_inst_4259_, v_inst_4260_, v_inst_4261_, v_inst_4262_, v_inst_4263_, v_inst_4264_, v_matcherApp_4265_, v_useSplitter_boxed_4272_, v_addEqualities_boxed_4273_, v_onParams_4268_, v_onMotive_4269_, v_onAlt_4270_, v_onRemaining_4271_);
lean_dec_ref(v_inst_4264_);
lean_dec(v_inst_4263_);
lean_dec_ref(v_inst_4262_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_){
_start:
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___y_4275_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4283_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v___x_4295_; 
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___y_4289_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4302_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4303_, lean_object* v_opt_4304_){
_start:
{
lean_object* v_name_4305_; lean_object* v_defValue_4306_; lean_object* v_map_4307_; lean_object* v___x_4308_; 
v_name_4305_ = lean_ctor_get(v_opt_4304_, 0);
v_defValue_4306_ = lean_ctor_get(v_opt_4304_, 1);
v_map_4307_ = lean_ctor_get(v_opts_4303_, 0);
v___x_4308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4307_, v_name_4305_);
if (lean_obj_tag(v___x_4308_) == 0)
{
uint8_t v___x_4309_; 
v___x_4309_ = lean_unbox(v_defValue_4306_);
return v___x_4309_;
}
else
{
lean_object* v_val_4310_; 
v_val_4310_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_val_4310_);
lean_dec_ref_known(v___x_4308_, 1);
if (lean_obj_tag(v_val_4310_) == 1)
{
uint8_t v_v_4311_; 
v_v_4311_ = lean_ctor_get_uint8(v_val_4310_, 0);
lean_dec_ref_known(v_val_4310_, 0);
return v_v_4311_;
}
else
{
uint8_t v___x_4312_; 
lean_dec(v_val_4310_);
v___x_4312_ = lean_unbox(v_defValue_4306_);
return v___x_4312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4313_, lean_object* v_opt_4314_){
_start:
{
uint8_t v_res_4315_; lean_object* v_r_4316_; 
v_res_4315_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4313_, v_opt_4314_);
lean_dec_ref(v_opt_4314_);
lean_dec_ref(v_opts_4313_);
v_r_4316_ = lean_box(v_res_4315_);
return v_r_4316_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_4325_, lean_object* v_x_4326_){
_start:
{
if (lean_obj_tag(v_x_4326_) == 1)
{
lean_object* v_pre_4327_; 
v_pre_4327_ = lean_ctor_get(v_x_4326_, 0);
switch(lean_obj_tag(v_pre_4327_))
{
case 1:
{
lean_object* v_pre_4328_; 
v_pre_4328_ = lean_ctor_get(v_pre_4327_, 0);
switch(lean_obj_tag(v_pre_4328_))
{
case 0:
{
lean_object* v_str_4329_; lean_object* v_str_4330_; lean_object* v___x_4331_; uint8_t v___x_4332_; 
v_str_4329_ = lean_ctor_get(v_x_4326_, 1);
v_str_4330_ = lean_ctor_get(v_pre_4327_, 1);
v___x_4331_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4332_ = lean_string_dec_eq(v_str_4330_, v___x_4331_);
if (v___x_4332_ == 0)
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4333_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4334_ = lean_string_dec_eq(v_str_4330_, v___x_4333_);
if (v___x_4334_ == 0)
{
return v___x_4334_;
}
else
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4336_ = lean_string_dec_eq(v_str_4329_, v___x_4335_);
if (v___x_4336_ == 0)
{
return v___x_4336_;
}
else
{
return v_suppressElabErrors_4325_;
}
}
}
else
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4338_ = lean_string_dec_eq(v_str_4329_, v___x_4337_);
if (v___x_4338_ == 0)
{
return v___x_4338_;
}
else
{
return v_suppressElabErrors_4325_;
}
}
}
case 1:
{
lean_object* v_pre_4339_; 
v_pre_4339_ = lean_ctor_get(v_pre_4328_, 0);
if (lean_obj_tag(v_pre_4339_) == 0)
{
lean_object* v_str_4340_; lean_object* v_str_4341_; lean_object* v_str_4342_; lean_object* v___x_4343_; uint8_t v___x_4344_; 
v_str_4340_ = lean_ctor_get(v_x_4326_, 1);
v_str_4341_ = lean_ctor_get(v_pre_4327_, 1);
v_str_4342_ = lean_ctor_get(v_pre_4328_, 1);
v___x_4343_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4344_ = lean_string_dec_eq(v_str_4342_, v___x_4343_);
if (v___x_4344_ == 0)
{
return v___x_4344_;
}
else
{
lean_object* v___x_4345_; uint8_t v___x_4346_; 
v___x_4345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4346_ = lean_string_dec_eq(v_str_4341_, v___x_4345_);
if (v___x_4346_ == 0)
{
return v___x_4346_;
}
else
{
lean_object* v___x_4347_; uint8_t v___x_4348_; 
v___x_4347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4348_ = lean_string_dec_eq(v_str_4340_, v___x_4347_);
if (v___x_4348_ == 0)
{
return v___x_4348_;
}
else
{
return v_suppressElabErrors_4325_;
}
}
}
}
else
{
uint8_t v___x_4349_; 
v___x_4349_ = 0;
return v___x_4349_;
}
}
default: 
{
uint8_t v___x_4350_; 
v___x_4350_ = 0;
return v___x_4350_;
}
}
}
case 0:
{
lean_object* v_str_4351_; lean_object* v___x_4352_; uint8_t v___x_4353_; 
v_str_4351_ = lean_ctor_get(v_x_4326_, 1);
v___x_4352_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4353_ = lean_string_dec_eq(v_str_4351_, v___x_4352_);
if (v___x_4353_ == 0)
{
return v___x_4353_;
}
else
{
return v_suppressElabErrors_4325_;
}
}
default: 
{
uint8_t v___x_4354_; 
v___x_4354_ = 0;
return v___x_4354_;
}
}
}
else
{
uint8_t v___x_4355_; 
v___x_4355_ = 0;
return v___x_4355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_4356_, lean_object* v_x_4357_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4358_; uint8_t v_res_4359_; lean_object* v_r_4360_; 
v_suppressElabErrors_boxed_4358_ = lean_unbox(v_suppressElabErrors_4356_);
v_res_4359_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_4358_, v_x_4357_);
lean_dec(v_x_4357_);
v_r_4360_ = lean_box(v_res_4359_);
return v_r_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4362_, lean_object* v_msgData_4363_, uint8_t v_severity_4364_, uint8_t v_isSilent_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
lean_object* v___y_4372_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; uint8_t v___y_4376_; uint8_t v___y_4377_; lean_object* v___y_4378_; lean_object* v_toCold_4379_; lean_object* v___y_4380_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v___y_4412_; uint8_t v___y_4413_; uint8_t v___y_4414_; uint8_t v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4436_; lean_object* v___y_4437_; uint8_t v___y_4438_; lean_object* v___y_4439_; uint8_t v___y_4440_; uint8_t v___y_4441_; lean_object* v___y_4442_; uint8_t v___y_4446_; uint8_t v___y_4447_; uint8_t v___x_4457_; uint8_t v___y_4459_; uint8_t v___x_4465_; 
v___x_4457_ = 2;
v___x_4465_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4364_, v___x_4457_);
if (v___x_4465_ == 0)
{
v___y_4459_ = v___x_4465_;
goto v___jp_4458_;
}
else
{
uint8_t v___x_4466_; 
lean_inc_ref(v_msgData_4363_);
v___x_4466_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4363_);
if (v___x_4466_ == 0)
{
v___y_4459_ = v___x_4466_;
goto v___jp_4458_;
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
lean_dec_ref(v_msgData_4363_);
v___x_4467_ = lean_box(0);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4467_);
return v___x_4468_;
}
}
v___jp_4371_:
{
lean_object* v_currNamespace_4381_; lean_object* v_openDecls_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v_env_4387_; lean_object* v_nextMacroScope_4388_; lean_object* v_ngen_4389_; lean_object* v_auxDeclNGen_4390_; lean_object* v_traceState_4391_; lean_object* v_cache_4392_; lean_object* v_recordedDeps_4393_; lean_object* v_messages_4394_; lean_object* v_infoState_4395_; lean_object* v_snapshotTasks_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4407_; 
v_currNamespace_4381_ = lean_ctor_get(v_toCold_4379_, 4);
v_openDecls_4382_ = lean_ctor_get(v_toCold_4379_, 5);
lean_inc(v_openDecls_4382_);
lean_inc(v_currNamespace_4381_);
v___x_4383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4383_, 0, v_currNamespace_4381_);
lean_ctor_set(v___x_4383_, 1, v_openDecls_4382_);
v___x_4384_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
lean_ctor_set(v___x_4384_, 1, v___y_4373_);
lean_inc_ref(v___y_4375_);
lean_inc_ref(v___y_4378_);
v___x_4385_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4385_, 0, v___y_4378_);
lean_ctor_set(v___x_4385_, 1, v___y_4374_);
lean_ctor_set(v___x_4385_, 2, v___y_4372_);
lean_ctor_set(v___x_4385_, 3, v___y_4375_);
lean_ctor_set(v___x_4385_, 4, v___x_4384_);
lean_ctor_set_uint8(v___x_4385_, sizeof(void*)*5, v___y_4376_);
lean_ctor_set_uint8(v___x_4385_, sizeof(void*)*5 + 1, v___y_4377_);
lean_ctor_set_uint8(v___x_4385_, sizeof(void*)*5 + 2, v_isSilent_4365_);
v___x_4386_ = lean_st_ref_take(v___y_4380_);
v_env_4387_ = lean_ctor_get(v___x_4386_, 0);
v_nextMacroScope_4388_ = lean_ctor_get(v___x_4386_, 1);
v_ngen_4389_ = lean_ctor_get(v___x_4386_, 2);
v_auxDeclNGen_4390_ = lean_ctor_get(v___x_4386_, 3);
v_traceState_4391_ = lean_ctor_get(v___x_4386_, 4);
v_cache_4392_ = lean_ctor_get(v___x_4386_, 5);
v_recordedDeps_4393_ = lean_ctor_get(v___x_4386_, 6);
v_messages_4394_ = lean_ctor_get(v___x_4386_, 7);
v_infoState_4395_ = lean_ctor_get(v___x_4386_, 8);
v_snapshotTasks_4396_ = lean_ctor_get(v___x_4386_, 9);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4386_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4398_ = v___x_4386_;
v_isShared_4399_ = v_isSharedCheck_4407_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_snapshotTasks_4396_);
lean_inc(v_infoState_4395_);
lean_inc(v_messages_4394_);
lean_inc(v_recordedDeps_4393_);
lean_inc(v_cache_4392_);
lean_inc(v_traceState_4391_);
lean_inc(v_auxDeclNGen_4390_);
lean_inc(v_ngen_4389_);
lean_inc(v_nextMacroScope_4388_);
lean_inc(v_env_4387_);
lean_dec(v___x_4386_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4407_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4403_; 
v___x_4400_ = lean_box(0);
v___x_4401_ = l_Lean_MessageLog_add(v___x_4385_, v_messages_4394_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 7, v___x_4401_);
v___x_4403_ = v___x_4398_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_env_4387_);
lean_ctor_set(v_reuseFailAlloc_4406_, 1, v_nextMacroScope_4388_);
lean_ctor_set(v_reuseFailAlloc_4406_, 2, v_ngen_4389_);
lean_ctor_set(v_reuseFailAlloc_4406_, 3, v_auxDeclNGen_4390_);
lean_ctor_set(v_reuseFailAlloc_4406_, 4, v_traceState_4391_);
lean_ctor_set(v_reuseFailAlloc_4406_, 5, v_cache_4392_);
lean_ctor_set(v_reuseFailAlloc_4406_, 6, v_recordedDeps_4393_);
lean_ctor_set(v_reuseFailAlloc_4406_, 7, v___x_4401_);
lean_ctor_set(v_reuseFailAlloc_4406_, 8, v_infoState_4395_);
lean_ctor_set(v_reuseFailAlloc_4406_, 9, v_snapshotTasks_4396_);
v___x_4403_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = lean_st_ref_put(v___y_4380_, v___x_4403_);
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4400_);
return v___x_4405_;
}
}
}
v___jp_4408_:
{
lean_object* v_fileName_4417_; lean_object* v_fileMap_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4434_; 
v_fileName_4417_ = lean_ctor_get(v___y_4412_, 0);
v_fileMap_4418_ = lean_ctor_get(v___y_4412_, 1);
v___x_4419_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4363_);
v___x_4420_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4419_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4423_ = v___x_4420_;
v_isShared_4424_ = v_isSharedCheck_4434_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4434_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; 
lean_inc_ref_n(v_fileMap_4418_, 2);
v___x_4425_ = l_Lean_FileMap_toPosition(v_fileMap_4418_, v___y_4411_);
lean_dec(v___y_4411_);
v___x_4426_ = l_Lean_FileMap_toPosition(v_fileMap_4418_, v___y_4416_);
lean_dec(v___y_4416_);
v___x_4427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4426_);
v___x_4428_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4415_ == 0)
{
lean_del_object(v___x_4423_);
lean_dec_ref(v___y_4409_);
v___y_4372_ = v___x_4427_;
v___y_4373_ = v_a_4421_;
v___y_4374_ = v___x_4425_;
v___y_4375_ = v___x_4428_;
v___y_4376_ = v___y_4413_;
v___y_4377_ = v___y_4414_;
v___y_4378_ = v_fileName_4417_;
v_toCold_4379_ = v___y_4410_;
v___y_4380_ = v___y_4369_;
goto v___jp_4371_;
}
else
{
uint8_t v___x_4429_; 
lean_inc(v_a_4421_);
v___x_4429_ = l_Lean_MessageData_hasTag(v___y_4409_, v_a_4421_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; lean_object* v___x_4432_; 
lean_dec_ref_known(v___x_4427_, 1);
lean_dec_ref(v___x_4425_);
lean_dec(v_a_4421_);
v___x_4430_ = lean_box(0);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v___x_4430_);
v___x_4432_ = v___x_4423_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4430_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
else
{
lean_del_object(v___x_4423_);
v___y_4372_ = v___x_4427_;
v___y_4373_ = v_a_4421_;
v___y_4374_ = v___x_4425_;
v___y_4375_ = v___x_4428_;
v___y_4376_ = v___y_4413_;
v___y_4377_ = v___y_4414_;
v___y_4378_ = v_fileName_4417_;
v_toCold_4379_ = v___y_4410_;
v___y_4380_ = v___y_4369_;
goto v___jp_4371_;
}
}
}
}
v___jp_4435_:
{
lean_object* v___x_4443_; 
v___x_4443_ = l_Lean_Syntax_getTailPos_x3f(v___y_4439_, v___y_4440_);
lean_dec(v___y_4439_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_inc(v___y_4442_);
v___y_4409_ = v___y_4436_;
v___y_4410_ = v___y_4437_;
v___y_4411_ = v___y_4442_;
v___y_4412_ = v___y_4437_;
v___y_4413_ = v___y_4440_;
v___y_4414_ = v___y_4441_;
v___y_4415_ = v___y_4438_;
v___y_4416_ = v___y_4442_;
goto v___jp_4408_;
}
else
{
lean_object* v_val_4444_; 
v_val_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_val_4444_);
lean_dec_ref_known(v___x_4443_, 1);
v___y_4409_ = v___y_4436_;
v___y_4410_ = v___y_4437_;
v___y_4411_ = v___y_4442_;
v___y_4412_ = v___y_4437_;
v___y_4413_ = v___y_4440_;
v___y_4414_ = v___y_4441_;
v___y_4415_ = v___y_4438_;
v___y_4416_ = v_val_4444_;
goto v___jp_4408_;
}
}
v___jp_4445_:
{
lean_object* v_toCold_4448_; lean_object* v_ref_4449_; uint8_t v_suppressElabErrors_4450_; lean_object* v___x_4451_; lean_object* v___f_4452_; lean_object* v_ref_4453_; lean_object* v___x_4454_; 
v_toCold_4448_ = lean_ctor_get(v___y_4368_, 0);
v_ref_4449_ = lean_ctor_get(v___y_4368_, 2);
v_suppressElabErrors_4450_ = lean_ctor_get_uint8(v___y_4368_, sizeof(void*)*3 + 2);
v___x_4451_ = lean_box(v_suppressElabErrors_4450_);
v___f_4452_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4452_, 0, v___x_4451_);
v_ref_4453_ = l_Lean_replaceRef(v_ref_4362_, v_ref_4449_);
v___x_4454_ = l_Lean_Syntax_getPos_x3f(v_ref_4453_, v___y_4446_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v___x_4455_; 
v___x_4455_ = lean_unsigned_to_nat(0u);
v___y_4436_ = v___f_4452_;
v___y_4437_ = v_toCold_4448_;
v___y_4438_ = v_suppressElabErrors_4450_;
v___y_4439_ = v_ref_4453_;
v___y_4440_ = v___y_4446_;
v___y_4441_ = v___y_4447_;
v___y_4442_ = v___x_4455_;
goto v___jp_4435_;
}
else
{
lean_object* v_val_4456_; 
v_val_4456_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_val_4456_);
lean_dec_ref_known(v___x_4454_, 1);
v___y_4436_ = v___f_4452_;
v___y_4437_ = v_toCold_4448_;
v___y_4438_ = v_suppressElabErrors_4450_;
v___y_4439_ = v_ref_4453_;
v___y_4440_ = v___y_4446_;
v___y_4441_ = v___y_4447_;
v___y_4442_ = v_val_4456_;
goto v___jp_4435_;
}
}
v___jp_4458_:
{
uint8_t v___x_4460_; uint8_t v___x_4461_; 
v___x_4460_ = 1;
v___x_4461_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4364_, v___x_4460_);
if (v___x_4461_ == 0)
{
v___y_4446_ = v___y_4459_;
v___y_4447_ = v_severity_4364_;
goto v___jp_4445_;
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4462_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4368_);
v___x_4463_ = l_Lean_warningAsError;
v___x_4464_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v___x_4462_, v___x_4463_);
lean_dec_ref(v___x_4462_);
if (v___x_4464_ == 0)
{
v___y_4446_ = v___y_4459_;
v___y_4447_ = v_severity_4364_;
goto v___jp_4445_;
}
else
{
v___y_4446_ = v___y_4459_;
v___y_4447_ = v___x_4457_;
goto v___jp_4445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4469_, lean_object* v_msgData_4470_, lean_object* v_severity_4471_, lean_object* v_isSilent_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
uint8_t v_severity_boxed_4478_; uint8_t v_isSilent_boxed_4479_; lean_object* v_res_4480_; 
v_severity_boxed_4478_ = lean_unbox(v_severity_4471_);
v_isSilent_boxed_4479_ = lean_unbox(v_isSilent_4472_);
v_res_4480_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4469_, v_msgData_4470_, v_severity_boxed_4478_, v_isSilent_boxed_4479_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
lean_dec(v___y_4476_);
lean_dec_ref(v___y_4475_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v_ref_4469_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4481_, uint8_t v_severity_4482_, uint8_t v_isSilent_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v_ref_4489_; lean_object* v___x_4490_; 
v_ref_4489_ = lean_ctor_get(v___y_4486_, 2);
v___x_4490_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4489_, v_msgData_4481_, v_severity_4482_, v_isSilent_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
return v___x_4490_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4491_, lean_object* v_severity_4492_, lean_object* v_isSilent_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
uint8_t v_severity_boxed_4499_; uint8_t v_isSilent_boxed_4500_; lean_object* v_res_4501_; 
v_severity_boxed_4499_ = lean_unbox(v_severity_4492_);
v_isSilent_boxed_4500_ = lean_unbox(v_isSilent_4493_);
v_res_4501_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4491_, v_severity_boxed_4499_, v_isSilent_boxed_4500_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec_ref(v___y_4494_);
return v_res_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
uint8_t v___x_4508_; uint8_t v___x_4509_; lean_object* v___x_4510_; 
v___x_4508_ = 0;
v___x_4509_ = 0;
v___x_4510_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4502_, v___x_4508_, v___x_4509_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
return v___x_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_){
_start:
{
lean_object* v_res_4517_; 
v_res_4517_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
return v_res_4517_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4520_ = l_Lean_stringToMessageData(v___x_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4521_, lean_object* v___altIdx_4522_, lean_object* v_expAltType_4523_, lean_object* v___altFVars_4524_, lean_object* v_alt_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___x_4531_; 
lean_inc(v___y_4529_);
lean_inc_ref(v___y_4528_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc_ref(v_alt_4525_);
v___x_4531_ = lean_infer_type(v_alt_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4533_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v___x_4533_ = l_Lean_Meta_mkEq(v_expAltType_4523_, v_a_4532_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4533_) == 0)
{
lean_object* v_a_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v_a_4534_ = lean_ctor_get(v___x_4533_, 0);
lean_inc(v_a_4534_);
lean_dec_ref_known(v___x_4533_, 1);
v___x_4535_ = lean_box(0);
v___x_4536_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4534_, v___x_4535_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4591_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4591_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4591_ == 0)
{
v___x_4539_ = v___x_4536_;
v_isShared_4540_ = v_isSharedCheck_4591_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4536_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4591_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = l_Lean_Expr_mvarId_x21(v_a_4537_);
v___x_4542_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4541_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4544_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc_n(v_a_4543_, 2);
lean_dec_ref_known(v___x_4542_, 1);
v___x_4544_ = l_Lean_MVarId_refl(v_a_4543_, v___x_4521_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v___x_4545_; 
lean_dec_ref_known(v___x_4544_, 1);
lean_dec(v_a_4543_);
lean_del_object(v___x_4539_);
v___x_4545_ = l_Lean_Meta_mkEqMPR(v_a_4537_, v_alt_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
return v___x_4545_;
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4582_; 
v_a_4546_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4548_ = v___x_4544_;
v_isShared_4549_ = v_isSharedCheck_4582_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4544_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4582_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
uint8_t v___x_4550_; 
v___x_4550_ = l_Lean_Exception_isInterrupt(v_a_4546_);
if (v___x_4550_ == 0)
{
uint8_t v___x_4551_; 
lean_inc(v_a_4546_);
v___x_4551_ = l_Lean_Exception_isRuntime(v_a_4546_);
if (v___x_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4554_; 
lean_del_object(v___x_4548_);
lean_dec(v_a_4546_);
v___x_4552_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4543_);
if (v_isShared_4540_ == 0)
{
lean_ctor_set_tag(v___x_4539_, 1);
lean_ctor_set(v___x_4539_, 0, v_a_4543_);
v___x_4554_ = v___x_4539_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4543_);
v___x_4554_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4552_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
v___x_4556_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4555_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v___x_4557_; 
lean_dec_ref_known(v___x_4556_, 1);
v___x_4557_ = l_Lean_MVarId_admit(v_a_4543_, v___x_4521_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v___x_4558_; 
lean_dec_ref_known(v___x_4557_, 1);
v___x_4558_ = l_Lean_Meta_mkEqMPR(v_a_4537_, v_alt_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
return v___x_4558_;
}
else
{
lean_object* v_a_4559_; lean_object* v___x_4561_; uint8_t v_isShared_4562_; uint8_t v_isSharedCheck_4566_; 
lean_dec(v_a_4537_);
lean_dec_ref(v_alt_4525_);
v_a_4559_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4561_ = v___x_4557_;
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
else
{
lean_inc(v_a_4559_);
lean_dec(v___x_4557_);
v___x_4561_ = lean_box(0);
v_isShared_4562_ = v_isSharedCheck_4566_;
goto v_resetjp_4560_;
}
v_resetjp_4560_:
{
lean_object* v___x_4564_; 
if (v_isShared_4562_ == 0)
{
v___x_4564_ = v___x_4561_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4559_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4574_; 
lean_dec(v_a_4543_);
lean_dec(v_a_4537_);
lean_dec_ref(v_alt_4525_);
v_a_4567_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4569_ = v___x_4556_;
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4556_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4572_; 
if (v_isShared_4570_ == 0)
{
v___x_4572_ = v___x_4569_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
}
else
{
lean_object* v___x_4577_; 
lean_dec(v_a_4543_);
lean_del_object(v___x_4539_);
lean_dec(v_a_4537_);
lean_dec_ref(v_alt_4525_);
if (v_isShared_4549_ == 0)
{
v___x_4577_ = v___x_4548_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4546_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
else
{
lean_object* v___x_4580_; 
lean_dec(v_a_4543_);
lean_del_object(v___x_4539_);
lean_dec(v_a_4537_);
lean_dec_ref(v_alt_4525_);
if (v_isShared_4549_ == 0)
{
v___x_4580_ = v___x_4548_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4546_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
}
}
else
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
lean_del_object(v___x_4539_);
lean_dec(v_a_4537_);
lean_dec_ref(v_alt_4525_);
v_a_4583_ = lean_ctor_get(v___x_4542_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v___x_4542_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v___x_4542_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4542_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4525_);
return v___x_4536_;
}
}
else
{
lean_dec_ref(v_alt_4525_);
return v___x_4533_;
}
}
else
{
lean_dec_ref(v_alt_4525_);
lean_dec_ref(v_expAltType_4523_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4592_, lean_object* v___altIdx_4593_, lean_object* v_expAltType_4594_, lean_object* v___altFVars_4595_, lean_object* v_alt_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_){
_start:
{
uint8_t v___x_32551__boxed_4602_; lean_object* v_res_4603_; 
v___x_32551__boxed_4602_ = lean_unbox(v___x_4592_);
v_res_4603_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32551__boxed_4602_, v___altIdx_4593_, v_expAltType_4594_, v___altFVars_4595_, v_alt_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec_ref(v___altFVars_4595_);
lean_dec(v___altIdx_4593_);
return v_res_4603_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4604_, lean_object* v_e_4605_){
_start:
{
uint8_t v___x_4606_; lean_object* v_d_4608_; lean_object* v_b_4609_; 
v___x_4606_ = l_Lean_Expr_hasFVar(v_e_4605_);
if (v___x_4606_ == 0)
{
return v___x_4606_;
}
else
{
switch(lean_obj_tag(v_e_4605_))
{
case 7:
{
lean_object* v_binderType_4612_; lean_object* v_body_4613_; 
v_binderType_4612_ = lean_ctor_get(v_e_4605_, 1);
v_body_4613_ = lean_ctor_get(v_e_4605_, 2);
v_d_4608_ = v_binderType_4612_;
v_b_4609_ = v_body_4613_;
goto v___jp_4607_;
}
case 6:
{
lean_object* v_binderType_4614_; lean_object* v_body_4615_; 
v_binderType_4614_ = lean_ctor_get(v_e_4605_, 1);
v_body_4615_ = lean_ctor_get(v_e_4605_, 2);
v_d_4608_ = v_binderType_4614_;
v_b_4609_ = v_body_4615_;
goto v___jp_4607_;
}
case 10:
{
lean_object* v_expr_4616_; 
v_expr_4616_ = lean_ctor_get(v_e_4605_, 1);
v_e_4605_ = v_expr_4616_;
goto _start;
}
case 8:
{
lean_object* v_type_4618_; lean_object* v_value_4619_; lean_object* v_body_4620_; uint8_t v___x_4621_; 
v_type_4618_ = lean_ctor_get(v_e_4605_, 1);
v_value_4619_ = lean_ctor_get(v_e_4605_, 2);
v_body_4620_ = lean_ctor_get(v_e_4605_, 3);
v___x_4621_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4604_, v_type_4618_);
if (v___x_4621_ == 0)
{
uint8_t v___x_4622_; 
v___x_4622_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4604_, v_value_4619_);
if (v___x_4622_ == 0)
{
v_e_4605_ = v_body_4620_;
goto _start;
}
else
{
return v___x_4606_;
}
}
else
{
return v___x_4606_;
}
}
case 5:
{
lean_object* v_fn_4624_; lean_object* v_arg_4625_; uint8_t v___x_4626_; 
v_fn_4624_ = lean_ctor_get(v_e_4605_, 0);
v_arg_4625_ = lean_ctor_get(v_e_4605_, 1);
v___x_4626_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4604_, v_fn_4624_);
if (v___x_4626_ == 0)
{
v_e_4605_ = v_arg_4625_;
goto _start;
}
else
{
return v___x_4606_;
}
}
case 11:
{
lean_object* v_struct_4628_; 
v_struct_4628_ = lean_ctor_get(v_e_4605_, 2);
v_e_4605_ = v_struct_4628_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4630_; lean_object* v___x_4631_; uint8_t v___x_4632_; 
v_fvarId_4630_ = lean_ctor_get(v_e_4605_, 0);
v___x_4631_ = l_Lean_Expr_fvarId_x21(v___x_4604_);
v___x_4632_ = l_Lean_instBEqFVarId_beq(v_fvarId_4630_, v___x_4631_);
lean_dec(v___x_4631_);
return v___x_4632_;
}
default: 
{
uint8_t v___x_4633_; 
v___x_4633_ = 0;
return v___x_4633_;
}
}
}
v___jp_4607_:
{
uint8_t v___x_4610_; 
v___x_4610_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4604_, v_d_4608_);
if (v___x_4610_ == 0)
{
v_e_4605_ = v_b_4609_;
goto _start;
}
else
{
return v___x_4606_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4634_, lean_object* v_e_4635_){
_start:
{
uint8_t v_res_4636_; lean_object* v_r_4637_; 
v_res_4636_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4634_, v_e_4635_);
lean_dec_ref(v_e_4635_);
lean_dec_ref(v___x_4634_);
v_r_4637_ = lean_box(v_res_4636_);
return v_r_4637_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4640_ = l_Lean_stringToMessageData(v___x_4639_);
return v___x_4640_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4642_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4643_ = l_Lean_stringToMessageData(v___x_4642_);
return v___x_4643_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4646_ = l_Lean_stringToMessageData(v___x_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4647_, lean_object* v_termAlt_4648_, lean_object* v_a_4649_, lean_object* v_b_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_array_4656_; lean_object* v_start_4657_; lean_object* v_stop_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4686_; 
v_array_4656_ = lean_ctor_get(v_a_4649_, 0);
v_start_4657_ = lean_ctor_get(v_a_4649_, 1);
v_stop_4658_ = lean_ctor_get(v_a_4649_, 2);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_a_4649_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4660_ = v_a_4649_;
v_isShared_4661_ = v_isSharedCheck_4686_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_stop_4658_);
lean_inc(v_start_4657_);
lean_inc(v_array_4656_);
lean_dec(v_a_4649_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4686_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
uint8_t v___x_4662_; 
v___x_4662_ = lean_nat_dec_lt(v_start_4657_, v_stop_4658_);
if (v___x_4662_ == 0)
{
lean_object* v___x_4663_; 
lean_del_object(v___x_4660_);
lean_dec(v_stop_4658_);
lean_dec(v_start_4657_);
lean_dec_ref(v_array_4656_);
lean_dec_ref(v_termAlt_4648_);
lean_dec_ref(v_a_4647_);
v___x_4663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4663_, 0, v_b_4650_);
return v___x_4663_;
}
else
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4668_; 
v___x_4664_ = lean_box(0);
v___x_4665_ = lean_unsigned_to_nat(1u);
v___x_4666_ = lean_nat_add(v_start_4657_, v___x_4665_);
lean_inc_ref(v_array_4656_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 1, v___x_4666_);
v___x_4668_ = v___x_4660_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_array_4656_);
lean_ctor_set(v_reuseFailAlloc_4685_, 1, v___x_4666_);
lean_ctor_set(v_reuseFailAlloc_4685_, 2, v_stop_4658_);
v___x_4668_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
lean_object* v___x_4669_; uint8_t v___x_4670_; 
v___x_4669_ = lean_array_fget(v_array_4656_, v_start_4657_);
lean_dec(v_start_4657_);
lean_dec_ref(v_array_4656_);
v___x_4670_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4669_, v_a_4647_);
if (v___x_4670_ == 0)
{
lean_dec(v___x_4669_);
v_a_4649_ = v___x_4668_;
v_b_4650_ = v___x_4664_;
goto _start;
}
else
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4672_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4647_);
v___x_4673_ = l_Lean_MessageData_ofExpr(v_a_4647_);
v___x_4674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4672_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
v___x_4675_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4674_);
lean_ctor_set(v___x_4676_, 1, v___x_4675_);
lean_inc_ref(v_termAlt_4648_);
v___x_4677_ = l_Lean_MessageData_ofExpr(v_termAlt_4648_);
v___x_4678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4676_);
lean_ctor_set(v___x_4678_, 1, v___x_4677_);
v___x_4679_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4678_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
v___x_4681_ = l_Lean_MessageData_ofExpr(v___x_4669_);
v___x_4682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4682_, 0, v___x_4680_);
lean_ctor_set(v___x_4682_, 1, v___x_4681_);
v___x_4683_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4682_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_dec_ref_known(v___x_4683_, 1);
v_a_4649_ = v___x_4668_;
v_b_4650_ = v___x_4664_;
goto _start;
}
else
{
lean_dec_ref(v___x_4668_);
lean_dec_ref(v_termAlt_4648_);
lean_dec_ref(v_a_4647_);
return v___x_4683_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4687_, lean_object* v_termAlt_4688_, lean_object* v_a_4689_, lean_object* v_b_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4687_, v_termAlt_4688_, v_a_4689_, v_b_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4697_, lean_object* v_v_4698_, uint8_t v___x_4699_, uint8_t v___x_4700_, uint8_t v___x_4701_, lean_object* v_xs_4702_, lean_object* v_termAltBody_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_){
_start:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4709_ = lean_array_get_size(v_xs_4702_);
v___x_4710_ = lean_nat_sub(v___x_4709_, v_nExtra_4697_);
v___x_4711_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4710_);
lean_inc_ref(v_xs_4702_);
v___x_4712_ = l_Array_toSubarray___redArg(v_xs_4702_, v___x_4711_, v___x_4710_);
v___x_4713_ = l_Array_toSubarray___redArg(v_xs_4702_, v___x_4710_, v___x_4709_);
lean_inc(v___y_4707_);
lean_inc_ref(v___y_4706_);
lean_inc(v___y_4705_);
lean_inc_ref(v___y_4704_);
v___x_4714_ = lean_infer_type(v_termAltBody_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v_a_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v_a_4715_ = lean_ctor_get(v___x_4714_, 0);
lean_inc_n(v_a_4715_, 2);
lean_dec_ref_known(v___x_4714_, 1);
v___x_4716_ = lean_box(0);
v___x_4717_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4715_, v_v_4698_, v___x_4713_, v___x_4716_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
lean_dec_ref_known(v___x_4717_, 1);
v___x_4718_ = l_Subarray_copy___redArg(v___x_4712_);
v___x_4719_ = l_Lean_Meta_mkLambdaFVars(v___x_4718_, v_a_4715_, v___x_4699_, v___x_4700_, v___x_4699_, v___x_4700_, v___x_4701_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
lean_dec_ref(v___x_4718_);
return v___x_4719_;
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_dec(v_a_4715_);
lean_dec_ref(v___x_4712_);
v_a_4720_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4717_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4717_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
else
{
lean_dec_ref(v___x_4713_);
lean_dec_ref(v___x_4712_);
lean_dec(v_v_4698_);
return v___x_4714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4728_, lean_object* v_v_4729_, lean_object* v___x_4730_, lean_object* v___x_4731_, lean_object* v___x_4732_, lean_object* v_xs_4733_, lean_object* v_termAltBody_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
uint8_t v___x_32867__boxed_4740_; uint8_t v___x_32868__boxed_4741_; uint8_t v___x_32869__boxed_4742_; lean_object* v_res_4743_; 
v___x_32867__boxed_4740_ = lean_unbox(v___x_4730_);
v___x_32868__boxed_4741_ = lean_unbox(v___x_4731_);
v___x_32869__boxed_4742_ = lean_unbox(v___x_4732_);
v_res_4743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4728_, v_v_4729_, v___x_32867__boxed_4740_, v___x_32868__boxed_4741_, v___x_32869__boxed_4742_, v_xs_4733_, v_termAltBody_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v_nExtra_4728_);
return v_res_4743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4744_, size_t v_sz_4745_, size_t v_i_4746_, lean_object* v_bs_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
uint8_t v___x_4753_; 
v___x_4753_ = lean_usize_dec_lt(v_i_4746_, v_sz_4745_);
if (v___x_4753_ == 0)
{
lean_object* v___x_4754_; 
lean_dec(v_nExtra_4744_);
v___x_4754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4754_, 0, v_bs_4747_);
return v___x_4754_;
}
else
{
uint8_t v___x_4755_; uint8_t v___x_4756_; lean_object* v_v_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___f_4761_; lean_object* v___x_4762_; lean_object* v_bs_x27_4763_; lean_object* v___x_4764_; 
v___x_4755_ = 0;
v___x_4756_ = 1;
v_v_4757_ = lean_array_uget(v_bs_4747_, v_i_4746_);
v___x_4758_ = lean_box(v___x_4755_);
v___x_4759_ = lean_box(v___x_4753_);
v___x_4760_ = lean_box(v___x_4756_);
lean_inc(v_v_4757_);
lean_inc(v_nExtra_4744_);
v___f_4761_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4761_, 0, v_nExtra_4744_);
lean_closure_set(v___f_4761_, 1, v_v_4757_);
lean_closure_set(v___f_4761_, 2, v___x_4758_);
lean_closure_set(v___f_4761_, 3, v___x_4759_);
lean_closure_set(v___f_4761_, 4, v___x_4760_);
v___x_4762_ = lean_unsigned_to_nat(0u);
v_bs_x27_4763_ = lean_array_uset(v_bs_4747_, v_i_4746_, v___x_4762_);
v___x_4764_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4757_, v___f_4761_, v___x_4755_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; size_t v___x_4766_; size_t v___x_4767_; lean_object* v___x_4768_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc(v_a_4765_);
lean_dec_ref_known(v___x_4764_, 1);
v___x_4766_ = ((size_t)1ULL);
v___x_4767_ = lean_usize_add(v_i_4746_, v___x_4766_);
v___x_4768_ = lean_array_uset(v_bs_x27_4763_, v_i_4746_, v_a_4765_);
v_i_4746_ = v___x_4767_;
v_bs_4747_ = v___x_4768_;
goto _start;
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
lean_dec_ref(v_bs_x27_4763_);
lean_dec(v_nExtra_4744_);
v_a_4770_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4764_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4764_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4778_, lean_object* v_sz_4779_, lean_object* v_i_4780_, lean_object* v_bs_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
size_t v_sz_boxed_4787_; size_t v_i_boxed_4788_; lean_object* v_res_4789_; 
v_sz_boxed_4787_ = lean_unbox_usize(v_sz_4779_);
lean_dec(v_sz_4779_);
v_i_boxed_4788_ = lean_unbox_usize(v_i_4780_);
lean_dec(v_i_4780_);
v_res_4789_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4778_, v_sz_boxed_4787_, v_i_boxed_4788_, v_bs_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
return v_res_4789_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4790_ = lean_box(0);
v___x_4791_ = l_Lean_Expr_sort___override(v___x_4790_);
return v___x_4791_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; 
v___x_4792_ = lean_box(0);
v___x_4793_ = l_Lean_Level_succ___override(v___x_4792_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4794_, uint8_t v___x_4795_, uint8_t v___x_4796_, lean_object* v_alts_4797_, lean_object* v_toMatcherInfo_4798_, lean_object* v_matcherName_4799_, lean_object* v_params_4800_, lean_object* v_matcherLevels_4801_, lean_object* v_motiveArgs_4802_, lean_object* v_body_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v___x_4809_; 
lean_inc(v_nExtra_4794_);
v___x_4809_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4794_, v_body_4803_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; lean_object* v___x_4813_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc(v_a_4810_);
lean_dec_ref_known(v___x_4809_, 1);
v___x_4811_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4812_ = 1;
v___x_4813_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4802_, v___x_4811_, v___x_4795_, v___x_4796_, v___x_4795_, v___x_4796_, v___x_4812_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; size_t v_sz_4815_; size_t v___x_4816_; lean_object* v___x_4817_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4814_);
lean_dec_ref_known(v___x_4813_, 1);
v_sz_4815_ = lean_array_size(v_alts_4797_);
v___x_4816_ = ((size_t)0ULL);
v___x_4817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4794_, v_sz_4815_, v___x_4816_, v_alts_4797_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; lean_object* v_matcherLevels_4820_; lean_object* v___y_4821_; lean_object* v___y_4822_; lean_object* v_uElimPos_x3f_4827_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_a_4818_);
lean_dec_ref_known(v___x_4817_, 1);
v_uElimPos_x3f_4827_ = lean_ctor_get(v_toMatcherInfo_4798_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4827_) == 0)
{
v_matcherLevels_4820_ = v_matcherLevels_4801_;
v___y_4821_ = v___y_4806_;
v___y_4822_ = v___y_4807_;
goto v___jp_4819_;
}
else
{
lean_object* v_val_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v_val_4828_ = lean_ctor_get(v_uElimPos_x3f_4827_, 0);
v___x_4829_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4830_ = lean_array_set(v_matcherLevels_4801_, v_val_4828_, v___x_4829_);
v_matcherLevels_4820_ = v___x_4830_;
v___y_4821_ = v___y_4806_;
v___y_4822_ = v___y_4807_;
goto v___jp_4819_;
}
v___jp_4819_:
{
lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; 
v___x_4823_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4824_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4824_, 0, v_toMatcherInfo_4798_);
lean_ctor_set(v___x_4824_, 1, v_matcherName_4799_);
lean_ctor_set(v___x_4824_, 2, v_matcherLevels_4820_);
lean_ctor_set(v___x_4824_, 3, v_params_4800_);
lean_ctor_set(v___x_4824_, 4, v_a_4814_);
lean_ctor_set(v___x_4824_, 5, v_motiveArgs_4802_);
lean_ctor_set(v___x_4824_, 6, v_a_4818_);
lean_ctor_set(v___x_4824_, 7, v___x_4823_);
v___x_4825_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4824_);
v___x_4826_ = l_Lean_mkArrowN(v_a_4810_, v___x_4825_, v___y_4821_, v___y_4822_);
lean_dec(v_a_4810_);
return v___x_4826_;
}
}
else
{
lean_object* v_a_4831_; lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4838_; 
lean_dec(v_a_4814_);
lean_dec(v_a_4810_);
lean_dec_ref(v_motiveArgs_4802_);
lean_dec_ref(v_matcherLevels_4801_);
lean_dec_ref(v_params_4800_);
lean_dec(v_matcherName_4799_);
lean_dec_ref(v_toMatcherInfo_4798_);
v_a_4831_ = lean_ctor_get(v___x_4817_, 0);
v_isSharedCheck_4838_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4838_ == 0)
{
v___x_4833_ = v___x_4817_;
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
else
{
lean_inc(v_a_4831_);
lean_dec(v___x_4817_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4838_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v___x_4836_; 
if (v_isShared_4834_ == 0)
{
v___x_4836_ = v___x_4833_;
goto v_reusejp_4835_;
}
else
{
lean_object* v_reuseFailAlloc_4837_; 
v_reuseFailAlloc_4837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_a_4831_);
v___x_4836_ = v_reuseFailAlloc_4837_;
goto v_reusejp_4835_;
}
v_reusejp_4835_:
{
return v___x_4836_;
}
}
}
}
else
{
lean_dec(v_a_4810_);
lean_dec_ref(v_motiveArgs_4802_);
lean_dec_ref(v_matcherLevels_4801_);
lean_dec_ref(v_params_4800_);
lean_dec(v_matcherName_4799_);
lean_dec_ref(v_toMatcherInfo_4798_);
lean_dec_ref(v_alts_4797_);
lean_dec(v_nExtra_4794_);
return v___x_4813_;
}
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec_ref(v_motiveArgs_4802_);
lean_dec_ref(v_matcherLevels_4801_);
lean_dec_ref(v_params_4800_);
lean_dec(v_matcherName_4799_);
lean_dec_ref(v_toMatcherInfo_4798_);
lean_dec_ref(v_alts_4797_);
lean_dec(v_nExtra_4794_);
v_a_4839_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4809_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4809_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4847_, lean_object* v___x_4848_, lean_object* v___x_4849_, lean_object* v_alts_4850_, lean_object* v_toMatcherInfo_4851_, lean_object* v_matcherName_4852_, lean_object* v_params_4853_, lean_object* v_matcherLevels_4854_, lean_object* v_motiveArgs_4855_, lean_object* v_body_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
uint8_t v___x_33002__boxed_4862_; uint8_t v___x_33003__boxed_4863_; lean_object* v_res_4864_; 
v___x_33002__boxed_4862_ = lean_unbox(v___x_4848_);
v___x_33003__boxed_4863_ = lean_unbox(v___x_4849_);
v_res_4864_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4847_, v___x_33002__boxed_4862_, v___x_33003__boxed_4863_, v_alts_4850_, v_toMatcherInfo_4851_, v_matcherName_4852_, v_params_4853_, v_matcherLevels_4854_, v_motiveArgs_4855_, v_body_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4865_, lean_object* v_ys_4866_, lean_object* v_args_4867_, lean_object* v___mask_4868_, lean_object* v___bodyType_4869_, lean_object* v___y_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_){
_start:
{
lean_object* v___x_4875_; 
lean_inc(v___y_4873_);
lean_inc_ref(v___y_4872_);
lean_inc(v___y_4871_);
lean_inc_ref(v___y_4870_);
v___x_4875_ = lean_apply_7(v_k_4865_, v_ys_4866_, v_args_4867_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_, lean_box(0));
return v___x_4875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4876_, lean_object* v_ys_4877_, lean_object* v_args_4878_, lean_object* v___mask_4879_, lean_object* v___bodyType_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4876_, v_ys_4877_, v_args_4878_, v___mask_4879_, v___bodyType_4880_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
lean_dec_ref(v___bodyType_4880_);
lean_dec_ref(v___mask_4879_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4887_, lean_object* v_altInfo_4888_, lean_object* v_k_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v___f_4895_; lean_object* v___x_4896_; 
v___f_4895_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4895_, 0, v_k_4889_);
v___x_4896_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4887_, v_altInfo_4888_, v___f_4895_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4896_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4896_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
v_a_4905_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4896_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4896_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4913_, lean_object* v_altInfo_4914_, lean_object* v_k_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_){
_start:
{
lean_object* v_res_4921_; 
v_res_4921_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4913_, v_altInfo_4914_, v_k_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_);
lean_dec(v___y_4919_);
lean_dec_ref(v___y_4918_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
return v_res_4921_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4922_, lean_object* v___x_4923_, lean_object* v___f_4924_, lean_object* v_fst_4925_, lean_object* v___x_4926_, lean_object* v___x_4927_, lean_object* v___x_4928_, lean_object* v___x_4929_, lean_object* v___x_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_){
_start:
{
lean_object* v___x_4936_; 
v___x_4936_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4922_, v___x_4923_, v___f_4924_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4951_; 
v_a_4937_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4939_ = v___x_4936_;
v_isShared_4940_ = v_isSharedCheck_4951_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4936_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4951_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4941_ = lean_array_push(v_fst_4925_, v_a_4937_);
v___x_4942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4926_);
lean_ctor_set(v___x_4942_, 1, v___x_4927_);
v___x_4943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4928_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
v___x_4944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4944_, 0, v___x_4929_);
lean_ctor_set(v___x_4944_, 1, v___x_4943_);
v___x_4945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4930_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
v___x_4946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4941_);
lean_ctor_set(v___x_4946_, 1, v___x_4945_);
v___x_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 0, v___x_4947_);
v___x_4949_ = v___x_4939_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
lean_dec_ref(v___x_4930_);
lean_dec_ref(v___x_4929_);
lean_dec_ref(v___x_4928_);
lean_dec_ref(v___x_4927_);
lean_dec_ref(v___x_4926_);
lean_dec(v_fst_4925_);
v_a_4952_ = lean_ctor_get(v___x_4936_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4936_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4936_);
v___x_4954_ = lean_box(0);
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
v_resetjp_4953_:
{
lean_object* v___x_4957_; 
if (v_isShared_4955_ == 0)
{
v___x_4957_ = v___x_4954_;
goto v_reusejp_4956_;
}
else
{
lean_object* v_reuseFailAlloc_4958_; 
v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_a_4952_);
v___x_4957_ = v_reuseFailAlloc_4958_;
goto v_reusejp_4956_;
}
v_reusejp_4956_:
{
return v___x_4957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4960_, lean_object* v___x_4961_, lean_object* v___f_4962_, lean_object* v_fst_4963_, lean_object* v___x_4964_, lean_object* v___x_4965_, lean_object* v___x_4966_, lean_object* v___x_4967_, lean_object* v___x_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v_res_4974_; 
v_res_4974_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4960_, v___x_4961_, v___f_4962_, v_fst_4963_, v___x_4964_, v___x_4965_, v___x_4966_, v___x_4967_, v___x_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
lean_dec(v___y_4970_);
lean_dec_ref(v___y_4969_);
return v_res_4974_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_4975_, lean_object* v_ys_4976_, lean_object* v_ys2_4977_, lean_object* v_ys3_4978_, lean_object* v_onAlt_4979_, lean_object* v_a_4980_, uint8_t v___x_4981_, uint8_t v_useSplitter_4982_, lean_object* v___x_4983_, lean_object* v_ys4_4984_, lean_object* v_altType_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v_a_4992_; lean_object* v___x_5001_; lean_object* v___x_5002_; 
lean_inc_ref(v_args_4975_);
v___x_5001_ = l_Array_append___redArg(v_args_4975_, v_ys3_4978_);
v___x_5002_ = l_Lean_Meta_instantiateLambda(v___x_4983_, v___x_5001_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
lean_dec_ref(v___x_5001_);
if (lean_obj_tag(v___x_5002_) == 0)
{
lean_object* v_a_5003_; 
v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
lean_inc(v_a_5003_);
lean_dec_ref_known(v___x_5002_, 1);
v_a_4992_ = v_a_5003_;
goto v___jp_4991_;
}
else
{
lean_object* v_a_5004_; uint8_t v___x_5005_; 
v_a_5004_ = lean_ctor_get(v___x_5002_, 0);
v___x_5005_ = l_Lean_Exception_isInterrupt(v_a_5004_);
if (v___x_5005_ == 0)
{
uint8_t v___x_5006_; 
lean_inc(v_a_5004_);
v___x_5006_ = l_Lean_Exception_isRuntime(v_a_5004_);
if (v___x_5006_ == 0)
{
lean_object* v___x_5007_; lean_object* v___x_5008_; 
lean_dec_ref_known(v___x_5002_, 1);
v___x_5007_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_5008_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5007_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v_a_5009_; 
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
lean_inc(v_a_5009_);
lean_dec_ref_known(v___x_5008_, 1);
v_a_4992_ = v_a_5009_;
goto v___jp_4991_;
}
else
{
lean_dec_ref(v_altType_4985_);
lean_dec_ref(v_ys4_4984_);
lean_dec(v_a_4980_);
lean_dec_ref(v_onAlt_4979_);
lean_dec_ref(v_ys3_4978_);
lean_dec_ref(v_ys2_4977_);
lean_dec_ref(v_ys_4976_);
lean_dec_ref(v_args_4975_);
return v___x_5008_;
}
}
else
{
lean_dec_ref(v_altType_4985_);
lean_dec_ref(v_ys4_4984_);
lean_dec(v_a_4980_);
lean_dec_ref(v_onAlt_4979_);
lean_dec_ref(v_ys3_4978_);
lean_dec_ref(v_ys2_4977_);
lean_dec_ref(v_ys_4976_);
lean_dec_ref(v_args_4975_);
return v___x_5002_;
}
}
else
{
lean_dec_ref(v_altType_4985_);
lean_dec_ref(v_ys4_4984_);
lean_dec(v_a_4980_);
lean_dec_ref(v_onAlt_4979_);
lean_dec_ref(v_ys3_4978_);
lean_dec_ref(v_ys2_4977_);
lean_dec_ref(v_ys_4976_);
lean_dec_ref(v_args_4975_);
return v___x_5002_;
}
}
v___jp_4991_:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
lean_inc_ref(v_ys4_4984_);
lean_inc_ref(v_ys3_4978_);
lean_inc_ref(v_ys2_4977_);
lean_inc_ref(v_ys_4976_);
v___x_4993_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4993_, 0, v_args_4975_);
lean_ctor_set(v___x_4993_, 1, v_ys_4976_);
lean_ctor_set(v___x_4993_, 2, v_ys2_4977_);
lean_ctor_set(v___x_4993_, 3, v_ys3_4978_);
lean_ctor_set(v___x_4993_, 4, v_ys4_4984_);
lean_inc(v___y_4989_);
lean_inc_ref(v___y_4988_);
lean_inc(v___y_4987_);
lean_inc_ref(v___y_4986_);
v___x_4994_ = lean_apply_9(v_onAlt_4979_, v_a_4980_, v_altType_4985_, v___x_4993_, v_a_4992_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, lean_box(0));
if (lean_obj_tag(v___x_4994_) == 0)
{
lean_object* v_a_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; uint8_t v___x_4999_; lean_object* v___x_5000_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
lean_dec_ref_known(v___x_4994_, 1);
v___x_4996_ = l_Array_append___redArg(v_ys_4976_, v_ys2_4977_);
lean_dec_ref(v_ys2_4977_);
v___x_4997_ = l_Array_append___redArg(v___x_4996_, v_ys3_4978_);
lean_dec_ref(v_ys3_4978_);
v___x_4998_ = l_Array_append___redArg(v___x_4997_, v_ys4_4984_);
lean_dec_ref(v_ys4_4984_);
v___x_4999_ = 1;
v___x_5000_ = l_Lean_Meta_mkLambdaFVars(v___x_4998_, v_a_4995_, v___x_4981_, v_useSplitter_4982_, v___x_4981_, v_useSplitter_4982_, v___x_4999_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_);
lean_dec_ref(v___x_4998_);
return v___x_5000_;
}
else
{
lean_dec_ref(v_ys4_4984_);
lean_dec_ref(v_ys3_4978_);
lean_dec_ref(v_ys2_4977_);
lean_dec_ref(v_ys_4976_);
return v___x_4994_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5010_, lean_object* v_ys_5011_, lean_object* v_ys2_5012_, lean_object* v_ys3_5013_, lean_object* v_onAlt_5014_, lean_object* v_a_5015_, lean_object* v___x_5016_, lean_object* v_useSplitter_5017_, lean_object* v___x_5018_, lean_object* v_ys4_5019_, lean_object* v_altType_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
uint8_t v___x_33256__boxed_5026_; uint8_t v_useSplitter_boxed_5027_; lean_object* v_res_5028_; 
v___x_33256__boxed_5026_ = lean_unbox(v___x_5016_);
v_useSplitter_boxed_5027_ = lean_unbox(v_useSplitter_5017_);
v_res_5028_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5010_, v_ys_5011_, v_ys2_5012_, v_ys3_5013_, v_onAlt_5014_, v_a_5015_, v___x_33256__boxed_5026_, v_useSplitter_boxed_5027_, v___x_5018_, v_ys4_5019_, v_altType_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
lean_dec(v___y_5024_);
lean_dec_ref(v___y_5023_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
return v_res_5028_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5029_, lean_object* v_ys_5030_, lean_object* v_ys2_5031_, lean_object* v_onAlt_5032_, lean_object* v_a_5033_, uint8_t v___x_5034_, uint8_t v_useSplitter_5035_, lean_object* v___x_5036_, lean_object* v_extraEqualities_5037_, lean_object* v_ys3_5038_, lean_object* v_altType_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_){
_start:
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___f_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; 
v___x_5045_ = lean_box(v___x_5034_);
v___x_5046_ = lean_box(v_useSplitter_5035_);
v___f_5047_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5047_, 0, v_args_5029_);
lean_closure_set(v___f_5047_, 1, v_ys_5030_);
lean_closure_set(v___f_5047_, 2, v_ys2_5031_);
lean_closure_set(v___f_5047_, 3, v_ys3_5038_);
lean_closure_set(v___f_5047_, 4, v_onAlt_5032_);
lean_closure_set(v___f_5047_, 5, v_a_5033_);
lean_closure_set(v___f_5047_, 6, v___x_5045_);
lean_closure_set(v___f_5047_, 7, v___x_5046_);
lean_closure_set(v___f_5047_, 8, v___x_5036_);
v___x_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5048_, 0, v_extraEqualities_5037_);
v___x_5049_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5039_, v___x_5048_, v___f_5047_, v___x_5034_, v___x_5034_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_);
return v___x_5049_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5050_, lean_object* v_ys_5051_, lean_object* v_ys2_5052_, lean_object* v_onAlt_5053_, lean_object* v_a_5054_, lean_object* v___x_5055_, lean_object* v_useSplitter_5056_, lean_object* v___x_5057_, lean_object* v_extraEqualities_5058_, lean_object* v_ys3_5059_, lean_object* v_altType_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
uint8_t v___x_33318__boxed_5066_; uint8_t v_useSplitter_boxed_5067_; lean_object* v_res_5068_; 
v___x_33318__boxed_5066_ = lean_unbox(v___x_5055_);
v_useSplitter_boxed_5067_ = lean_unbox(v_useSplitter_5056_);
v_res_5068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5050_, v_ys_5051_, v_ys2_5052_, v_onAlt_5053_, v_a_5054_, v___x_33318__boxed_5066_, v_useSplitter_boxed_5067_, v___x_5057_, v_extraEqualities_5058_, v_ys3_5059_, v_altType_5060_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_);
lean_dec(v___y_5064_);
lean_dec_ref(v___y_5063_);
lean_dec(v___y_5062_);
lean_dec_ref(v___y_5061_);
return v_res_5068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5069_, lean_object* v_ys_5070_, lean_object* v_onAlt_5071_, lean_object* v_a_5072_, uint8_t v___x_5073_, uint8_t v_useSplitter_5074_, lean_object* v___x_5075_, lean_object* v_extraEqualities_5076_, lean_object* v_numDiscrEqs_5077_, lean_object* v_ys2_5078_, lean_object* v_altType_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___f_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5085_ = lean_box(v___x_5073_);
v___x_5086_ = lean_box(v_useSplitter_5074_);
v___f_5087_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5087_, 0, v_args_5069_);
lean_closure_set(v___f_5087_, 1, v_ys_5070_);
lean_closure_set(v___f_5087_, 2, v_ys2_5078_);
lean_closure_set(v___f_5087_, 3, v_onAlt_5071_);
lean_closure_set(v___f_5087_, 4, v_a_5072_);
lean_closure_set(v___f_5087_, 5, v___x_5085_);
lean_closure_set(v___f_5087_, 6, v___x_5086_);
lean_closure_set(v___f_5087_, 7, v___x_5075_);
lean_closure_set(v___f_5087_, 8, v_extraEqualities_5076_);
v___x_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5088_, 0, v_numDiscrEqs_5077_);
v___x_5089_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5079_, v___x_5088_, v___f_5087_, v___x_5073_, v___x_5073_, v___y_5080_, v___y_5081_, v___y_5082_, v___y_5083_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5090_, lean_object* v_ys_5091_, lean_object* v_onAlt_5092_, lean_object* v_a_5093_, lean_object* v___x_5094_, lean_object* v_useSplitter_5095_, lean_object* v___x_5096_, lean_object* v_extraEqualities_5097_, lean_object* v_numDiscrEqs_5098_, lean_object* v_ys2_5099_, lean_object* v_altType_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_){
_start:
{
uint8_t v___x_33349__boxed_5106_; uint8_t v_useSplitter_boxed_5107_; lean_object* v_res_5108_; 
v___x_33349__boxed_5106_ = lean_unbox(v___x_5094_);
v_useSplitter_boxed_5107_ = lean_unbox(v_useSplitter_5095_);
v_res_5108_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5090_, v_ys_5091_, v_onAlt_5092_, v_a_5093_, v___x_33349__boxed_5106_, v_useSplitter_boxed_5107_, v___x_5096_, v_extraEqualities_5097_, v_numDiscrEqs_5098_, v_ys2_5099_, v_altType_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
return v_res_5108_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0(void){
_start:
{
lean_object* v___x_5109_; 
v___x_5109_ = l_instMonadEIO___redArg();
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_){
_start:
{
lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v_toApplicative_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5183_; 
v___x_5120_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5121_ = l_StateRefT_x27_instMonad___redArg(v___x_5120_);
v_toApplicative_5122_ = lean_ctor_get(v___x_5121_, 0);
v_isSharedCheck_5183_ = !lean_is_exclusive(v___x_5121_);
if (v_isSharedCheck_5183_ == 0)
{
lean_object* v_unused_5184_; 
v_unused_5184_ = lean_ctor_get(v___x_5121_, 1);
lean_dec(v_unused_5184_);
v___x_5124_ = v___x_5121_;
v_isShared_5125_ = v_isSharedCheck_5183_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_toApplicative_5122_);
lean_dec(v___x_5121_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5183_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v_toFunctor_5126_; lean_object* v_toSeq_5127_; lean_object* v_toSeqLeft_5128_; lean_object* v_toSeqRight_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5181_; 
v_toFunctor_5126_ = lean_ctor_get(v_toApplicative_5122_, 0);
v_toSeq_5127_ = lean_ctor_get(v_toApplicative_5122_, 2);
v_toSeqLeft_5128_ = lean_ctor_get(v_toApplicative_5122_, 3);
v_toSeqRight_5129_ = lean_ctor_get(v_toApplicative_5122_, 4);
v_isSharedCheck_5181_ = !lean_is_exclusive(v_toApplicative_5122_);
if (v_isSharedCheck_5181_ == 0)
{
lean_object* v_unused_5182_; 
v_unused_5182_ = lean_ctor_get(v_toApplicative_5122_, 1);
lean_dec(v_unused_5182_);
v___x_5131_ = v_toApplicative_5122_;
v_isShared_5132_ = v_isSharedCheck_5181_;
goto v_resetjp_5130_;
}
else
{
lean_inc(v_toSeqRight_5129_);
lean_inc(v_toSeqLeft_5128_);
lean_inc(v_toSeq_5127_);
lean_inc(v_toFunctor_5126_);
lean_dec(v_toApplicative_5122_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5181_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
lean_object* v___f_5133_; lean_object* v___f_5134_; lean_object* v___f_5135_; lean_object* v___f_5136_; lean_object* v___x_5137_; lean_object* v___f_5138_; lean_object* v___f_5139_; lean_object* v___f_5140_; lean_object* v___x_5142_; 
v___f_5133_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5134_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5126_);
v___f_5135_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5135_, 0, v_toFunctor_5126_);
v___f_5136_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5136_, 0, v_toFunctor_5126_);
v___x_5137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5137_, 0, v___f_5135_);
lean_ctor_set(v___x_5137_, 1, v___f_5136_);
v___f_5138_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5138_, 0, v_toSeqRight_5129_);
v___f_5139_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5139_, 0, v_toSeqLeft_5128_);
v___f_5140_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5140_, 0, v_toSeq_5127_);
if (v_isShared_5132_ == 0)
{
lean_ctor_set(v___x_5131_, 4, v___f_5138_);
lean_ctor_set(v___x_5131_, 3, v___f_5139_);
lean_ctor_set(v___x_5131_, 2, v___f_5140_);
lean_ctor_set(v___x_5131_, 1, v___f_5133_);
lean_ctor_set(v___x_5131_, 0, v___x_5137_);
v___x_5142_ = v___x_5131_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5137_);
lean_ctor_set(v_reuseFailAlloc_5180_, 1, v___f_5133_);
lean_ctor_set(v_reuseFailAlloc_5180_, 2, v___f_5140_);
lean_ctor_set(v_reuseFailAlloc_5180_, 3, v___f_5139_);
lean_ctor_set(v_reuseFailAlloc_5180_, 4, v___f_5138_);
v___x_5142_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
lean_object* v___x_5144_; 
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 1, v___f_5134_);
lean_ctor_set(v___x_5124_, 0, v___x_5142_);
v___x_5144_ = v___x_5124_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v___x_5142_);
lean_ctor_set(v_reuseFailAlloc_5179_, 1, v___f_5134_);
v___x_5144_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
lean_object* v___x_5145_; lean_object* v_toApplicative_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5177_; 
v___x_5145_ = l_StateRefT_x27_instMonad___redArg(v___x_5144_);
v_toApplicative_5146_ = lean_ctor_get(v___x_5145_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5145_);
if (v_isSharedCheck_5177_ == 0)
{
lean_object* v_unused_5178_; 
v_unused_5178_ = lean_ctor_get(v___x_5145_, 1);
lean_dec(v_unused_5178_);
v___x_5148_ = v___x_5145_;
v_isShared_5149_ = v_isSharedCheck_5177_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_toApplicative_5146_);
lean_dec(v___x_5145_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5177_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v_toFunctor_5150_; lean_object* v_toSeq_5151_; lean_object* v_toSeqLeft_5152_; lean_object* v_toSeqRight_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5175_; 
v_toFunctor_5150_ = lean_ctor_get(v_toApplicative_5146_, 0);
v_toSeq_5151_ = lean_ctor_get(v_toApplicative_5146_, 2);
v_toSeqLeft_5152_ = lean_ctor_get(v_toApplicative_5146_, 3);
v_toSeqRight_5153_ = lean_ctor_get(v_toApplicative_5146_, 4);
v_isSharedCheck_5175_ = !lean_is_exclusive(v_toApplicative_5146_);
if (v_isSharedCheck_5175_ == 0)
{
lean_object* v_unused_5176_; 
v_unused_5176_ = lean_ctor_get(v_toApplicative_5146_, 1);
lean_dec(v_unused_5176_);
v___x_5155_ = v_toApplicative_5146_;
v_isShared_5156_ = v_isSharedCheck_5175_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_toSeqRight_5153_);
lean_inc(v_toSeqLeft_5152_);
lean_inc(v_toSeq_5151_);
lean_inc(v_toFunctor_5150_);
lean_dec(v_toApplicative_5146_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5175_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___f_5157_; lean_object* v___f_5158_; lean_object* v___f_5159_; lean_object* v___f_5160_; lean_object* v___x_5161_; lean_object* v___f_5162_; lean_object* v___f_5163_; lean_object* v___f_5164_; lean_object* v___x_5166_; 
v___f_5157_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5158_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5150_);
v___f_5159_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5159_, 0, v_toFunctor_5150_);
v___f_5160_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5160_, 0, v_toFunctor_5150_);
v___x_5161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___f_5159_);
lean_ctor_set(v___x_5161_, 1, v___f_5160_);
v___f_5162_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5162_, 0, v_toSeqRight_5153_);
v___f_5163_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5163_, 0, v_toSeqLeft_5152_);
v___f_5164_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5164_, 0, v_toSeq_5151_);
if (v_isShared_5156_ == 0)
{
lean_ctor_set(v___x_5155_, 4, v___f_5162_);
lean_ctor_set(v___x_5155_, 3, v___f_5163_);
lean_ctor_set(v___x_5155_, 2, v___f_5164_);
lean_ctor_set(v___x_5155_, 1, v___f_5157_);
lean_ctor_set(v___x_5155_, 0, v___x_5161_);
v___x_5166_ = v___x_5155_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5161_);
lean_ctor_set(v_reuseFailAlloc_5174_, 1, v___f_5157_);
lean_ctor_set(v_reuseFailAlloc_5174_, 2, v___f_5164_);
lean_ctor_set(v_reuseFailAlloc_5174_, 3, v___f_5163_);
lean_ctor_set(v_reuseFailAlloc_5174_, 4, v___f_5162_);
v___x_5166_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
lean_object* v___x_5168_; 
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 1, v___f_5158_);
lean_ctor_set(v___x_5148_, 0, v___x_5166_);
v___x_5168_ = v___x_5148_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5166_);
lean_ctor_set(v_reuseFailAlloc_5173_, 1, v___f_5158_);
v___x_5168_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
lean_object* v___x_5169_; lean_object* v___x_5170_; lean_object* v___x_27303__overap_5171_; lean_object* v___x_5172_; 
v___x_5169_ = l_Lean_instInhabitedExpr;
v___x_5170_ = l_instInhabitedOfMonad___redArg(v___x_5168_, v___x_5169_);
v___x_27303__overap_5171_ = lean_panic_fn_borrowed(v___x_5170_, v_msg_5114_);
lean_dec(v___x_5170_);
lean_inc(v___y_5118_);
lean_inc_ref(v___y_5117_);
lean_inc(v___y_5116_);
lean_inc_ref(v___y_5115_);
v___x_5172_ = lean_apply_5(v___x_27303__overap_5171_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, lean_box(0));
return v___x_5172_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5185_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
lean_dec(v___y_5189_);
lean_dec_ref(v___y_5188_);
lean_dec(v___y_5187_);
lean_dec_ref(v___y_5186_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5192_, lean_object* v_onAlt_5193_, lean_object* v_a_5194_, uint8_t v___x_5195_, uint8_t v_useSplitter_5196_, lean_object* v___x_5197_, lean_object* v_extraEqualities_5198_, lean_object* v_numDiscrEqs_5199_, lean_object* v___x_5200_, lean_object* v___x_5201_, lean_object* v_ys_5202_, lean_object* v_args_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_){
_start:
{
lean_object* v_numFields_5209_; lean_object* v_numOverlaps_5210_; uint8_t v_hasUnitThunk_5211_; lean_object* v___x_5212_; uint8_t v___x_5213_; 
v_numFields_5209_ = lean_ctor_get(v___x_5192_, 0);
v_numOverlaps_5210_ = lean_ctor_get(v___x_5192_, 1);
v_hasUnitThunk_5211_ = lean_ctor_get_uint8(v___x_5192_, sizeof(void*)*2);
v___x_5212_ = lean_array_get_size(v_ys_5202_);
v___x_5213_ = lean_nat_dec_eq(v___x_5212_, v_numFields_5209_);
if (v___x_5213_ == 0)
{
lean_object* v___x_5214_; lean_object* v___x_5215_; 
lean_dec_ref(v_args_5203_);
lean_dec_ref(v_ys_5202_);
lean_dec_ref(v___x_5200_);
lean_dec(v_numDiscrEqs_5199_);
lean_dec(v_extraEqualities_5198_);
lean_dec_ref(v___x_5197_);
lean_dec(v_a_5194_);
lean_dec_ref(v_onAlt_5193_);
v___x_5214_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5215_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v___x_5214_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
return v___x_5215_;
}
else
{
lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___f_5218_; lean_object* v_altType_5220_; lean_object* v___y_5221_; lean_object* v___y_5222_; lean_object* v___y_5223_; lean_object* v___y_5224_; lean_object* v___x_5234_; 
v___x_5216_ = lean_box(v___x_5195_);
v___x_5217_ = lean_box(v_useSplitter_5196_);
lean_inc_ref(v_ys_5202_);
v___f_5218_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5218_, 0, v_args_5203_);
lean_closure_set(v___f_5218_, 1, v_ys_5202_);
lean_closure_set(v___f_5218_, 2, v_onAlt_5193_);
lean_closure_set(v___f_5218_, 3, v_a_5194_);
lean_closure_set(v___f_5218_, 4, v___x_5216_);
lean_closure_set(v___f_5218_, 5, v___x_5217_);
lean_closure_set(v___f_5218_, 6, v___x_5197_);
lean_closure_set(v___f_5218_, 7, v_extraEqualities_5198_);
lean_closure_set(v___f_5218_, 8, v_numDiscrEqs_5199_);
v___x_5234_ = l_Lean_Meta_instantiateForall(v___x_5200_, v_ys_5202_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
lean_dec_ref(v_ys_5202_);
if (lean_obj_tag(v___x_5234_) == 0)
{
if (v_hasUnitThunk_5211_ == 0)
{
lean_object* v_a_5235_; 
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref_known(v___x_5234_, 1);
v_altType_5220_ = v_a_5235_;
v___y_5221_ = v___y_5204_;
v___y_5222_ = v___y_5205_;
v___y_5223_ = v___y_5206_;
v___y_5224_ = v___y_5207_;
goto v___jp_5219_;
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; 
v_a_5236_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5236_);
lean_dec_ref_known(v___x_5234_, 1);
v___x_5237_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5238_ = lean_mk_empty_array_with_capacity(v___x_5201_);
v___x_5239_ = lean_array_push(v___x_5238_, v___x_5237_);
v___x_5240_ = l_Lean_Meta_instantiateForall(v_a_5236_, v___x_5239_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
lean_dec_ref(v___x_5239_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_object* v_a_5241_; 
v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
lean_inc(v_a_5241_);
lean_dec_ref_known(v___x_5240_, 1);
v_altType_5220_ = v_a_5241_;
v___y_5221_ = v___y_5204_;
v___y_5222_ = v___y_5205_;
v___y_5223_ = v___y_5206_;
v___y_5224_ = v___y_5207_;
goto v___jp_5219_;
}
else
{
lean_dec_ref(v___f_5218_);
return v___x_5240_;
}
}
}
else
{
lean_dec_ref(v___f_5218_);
return v___x_5234_;
}
v___jp_5219_:
{
lean_object* v___x_5225_; lean_object* v___x_5226_; 
lean_inc(v_numOverlaps_5210_);
v___x_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5225_, 0, v_numOverlaps_5210_);
v___x_5226_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5220_, v___x_5225_, v___f_5218_, v___x_5195_, v___x_5195_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
if (lean_obj_tag(v___x_5226_) == 0)
{
if (v_hasUnitThunk_5211_ == 0)
{
return v___x_5226_;
}
else
{
lean_object* v_a_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
v_a_5227_ = lean_ctor_get(v___x_5226_, 0);
lean_inc(v_a_5227_);
lean_dec_ref_known(v___x_5226_, 1);
v___x_5228_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5229_ = lean_unsigned_to_nat(2u);
v___x_5230_ = lean_mk_empty_array_with_capacity(v___x_5229_);
lean_dec_ref(v___x_5230_);
v___x_5231_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5232_ = lean_array_push(v___x_5231_, v_a_5227_);
v___x_5233_ = l_Lean_Meta_mkAppM(v___x_5228_, v___x_5232_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_);
return v___x_5233_;
}
}
else
{
return v___x_5226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5242_ = _args[0];
lean_object* v_onAlt_5243_ = _args[1];
lean_object* v_a_5244_ = _args[2];
lean_object* v___x_5245_ = _args[3];
lean_object* v_useSplitter_5246_ = _args[4];
lean_object* v___x_5247_ = _args[5];
lean_object* v_extraEqualities_5248_ = _args[6];
lean_object* v_numDiscrEqs_5249_ = _args[7];
lean_object* v___x_5250_ = _args[8];
lean_object* v___x_5251_ = _args[9];
lean_object* v_ys_5252_ = _args[10];
lean_object* v_args_5253_ = _args[11];
lean_object* v___y_5254_ = _args[12];
lean_object* v___y_5255_ = _args[13];
lean_object* v___y_5256_ = _args[14];
lean_object* v___y_5257_ = _args[15];
lean_object* v___y_5258_ = _args[16];
_start:
{
uint8_t v___x_33551__boxed_5259_; uint8_t v_useSplitter_boxed_5260_; lean_object* v_res_5261_; 
v___x_33551__boxed_5259_ = lean_unbox(v___x_5245_);
v_useSplitter_boxed_5260_ = lean_unbox(v_useSplitter_5246_);
v_res_5261_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5242_, v_onAlt_5243_, v_a_5244_, v___x_33551__boxed_5259_, v_useSplitter_boxed_5260_, v___x_5247_, v_extraEqualities_5248_, v_numDiscrEqs_5249_, v___x_5250_, v___x_5251_, v_ys_5252_, v_args_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
lean_dec(v___y_5257_);
lean_dec_ref(v___y_5256_);
lean_dec(v___y_5255_);
lean_dec_ref(v___y_5254_);
lean_dec(v___x_5251_);
lean_dec_ref(v___x_5242_);
return v_res_5261_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v_toApplicative_5270_; lean_object* v___x_5272_; uint8_t v_isShared_5273_; uint8_t v_isSharedCheck_5331_; 
v___x_5268_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5269_ = l_StateRefT_x27_instMonad___redArg(v___x_5268_);
v_toApplicative_5270_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5331_ == 0)
{
lean_object* v_unused_5332_; 
v_unused_5332_ = lean_ctor_get(v___x_5269_, 1);
lean_dec(v_unused_5332_);
v___x_5272_ = v___x_5269_;
v_isShared_5273_ = v_isSharedCheck_5331_;
goto v_resetjp_5271_;
}
else
{
lean_inc(v_toApplicative_5270_);
lean_dec(v___x_5269_);
v___x_5272_ = lean_box(0);
v_isShared_5273_ = v_isSharedCheck_5331_;
goto v_resetjp_5271_;
}
v_resetjp_5271_:
{
lean_object* v_toFunctor_5274_; lean_object* v_toSeq_5275_; lean_object* v_toSeqLeft_5276_; lean_object* v_toSeqRight_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5329_; 
v_toFunctor_5274_ = lean_ctor_get(v_toApplicative_5270_, 0);
v_toSeq_5275_ = lean_ctor_get(v_toApplicative_5270_, 2);
v_toSeqLeft_5276_ = lean_ctor_get(v_toApplicative_5270_, 3);
v_toSeqRight_5277_ = lean_ctor_get(v_toApplicative_5270_, 4);
v_isSharedCheck_5329_ = !lean_is_exclusive(v_toApplicative_5270_);
if (v_isSharedCheck_5329_ == 0)
{
lean_object* v_unused_5330_; 
v_unused_5330_ = lean_ctor_get(v_toApplicative_5270_, 1);
lean_dec(v_unused_5330_);
v___x_5279_ = v_toApplicative_5270_;
v_isShared_5280_ = v_isSharedCheck_5329_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_toSeqRight_5277_);
lean_inc(v_toSeqLeft_5276_);
lean_inc(v_toSeq_5275_);
lean_inc(v_toFunctor_5274_);
lean_dec(v_toApplicative_5270_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5329_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v___f_5281_; lean_object* v___f_5282_; lean_object* v___f_5283_; lean_object* v___f_5284_; lean_object* v___x_5285_; lean_object* v___f_5286_; lean_object* v___f_5287_; lean_object* v___f_5288_; lean_object* v___x_5290_; 
v___f_5281_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5282_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5274_);
v___f_5283_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5283_, 0, v_toFunctor_5274_);
v___f_5284_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5284_, 0, v_toFunctor_5274_);
v___x_5285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5285_, 0, v___f_5283_);
lean_ctor_set(v___x_5285_, 1, v___f_5284_);
v___f_5286_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5286_, 0, v_toSeqRight_5277_);
v___f_5287_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5287_, 0, v_toSeqLeft_5276_);
v___f_5288_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5288_, 0, v_toSeq_5275_);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 4, v___f_5286_);
lean_ctor_set(v___x_5279_, 3, v___f_5287_);
lean_ctor_set(v___x_5279_, 2, v___f_5288_);
lean_ctor_set(v___x_5279_, 1, v___f_5281_);
lean_ctor_set(v___x_5279_, 0, v___x_5285_);
v___x_5290_ = v___x_5279_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v___x_5285_);
lean_ctor_set(v_reuseFailAlloc_5328_, 1, v___f_5281_);
lean_ctor_set(v_reuseFailAlloc_5328_, 2, v___f_5288_);
lean_ctor_set(v_reuseFailAlloc_5328_, 3, v___f_5287_);
lean_ctor_set(v_reuseFailAlloc_5328_, 4, v___f_5286_);
v___x_5290_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
lean_object* v___x_5292_; 
if (v_isShared_5273_ == 0)
{
lean_ctor_set(v___x_5272_, 1, v___f_5282_);
lean_ctor_set(v___x_5272_, 0, v___x_5290_);
v___x_5292_ = v___x_5272_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5290_);
lean_ctor_set(v_reuseFailAlloc_5327_, 1, v___f_5282_);
v___x_5292_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
lean_object* v___x_5293_; lean_object* v_toApplicative_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5325_; 
v___x_5293_ = l_StateRefT_x27_instMonad___redArg(v___x_5292_);
v_toApplicative_5294_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5325_ == 0)
{
lean_object* v_unused_5326_; 
v_unused_5326_ = lean_ctor_get(v___x_5293_, 1);
lean_dec(v_unused_5326_);
v___x_5296_ = v___x_5293_;
v_isShared_5297_ = v_isSharedCheck_5325_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_toApplicative_5294_);
lean_dec(v___x_5293_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5325_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v_toFunctor_5298_; lean_object* v_toSeq_5299_; lean_object* v_toSeqLeft_5300_; lean_object* v_toSeqRight_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5323_; 
v_toFunctor_5298_ = lean_ctor_get(v_toApplicative_5294_, 0);
v_toSeq_5299_ = lean_ctor_get(v_toApplicative_5294_, 2);
v_toSeqLeft_5300_ = lean_ctor_get(v_toApplicative_5294_, 3);
v_toSeqRight_5301_ = lean_ctor_get(v_toApplicative_5294_, 4);
v_isSharedCheck_5323_ = !lean_is_exclusive(v_toApplicative_5294_);
if (v_isSharedCheck_5323_ == 0)
{
lean_object* v_unused_5324_; 
v_unused_5324_ = lean_ctor_get(v_toApplicative_5294_, 1);
lean_dec(v_unused_5324_);
v___x_5303_ = v_toApplicative_5294_;
v_isShared_5304_ = v_isSharedCheck_5323_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_toSeqRight_5301_);
lean_inc(v_toSeqLeft_5300_);
lean_inc(v_toSeq_5299_);
lean_inc(v_toFunctor_5298_);
lean_dec(v_toApplicative_5294_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5323_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v___f_5305_; lean_object* v___f_5306_; lean_object* v___f_5307_; lean_object* v___f_5308_; lean_object* v___x_5309_; lean_object* v___f_5310_; lean_object* v___f_5311_; lean_object* v___f_5312_; lean_object* v___x_5314_; 
v___f_5305_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5306_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5298_);
v___f_5307_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5307_, 0, v_toFunctor_5298_);
v___f_5308_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5308_, 0, v_toFunctor_5298_);
v___x_5309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5309_, 0, v___f_5307_);
lean_ctor_set(v___x_5309_, 1, v___f_5308_);
v___f_5310_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5310_, 0, v_toSeqRight_5301_);
v___f_5311_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5311_, 0, v_toSeqLeft_5300_);
v___f_5312_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5312_, 0, v_toSeq_5299_);
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 4, v___f_5310_);
lean_ctor_set(v___x_5303_, 3, v___f_5311_);
lean_ctor_set(v___x_5303_, 2, v___f_5312_);
lean_ctor_set(v___x_5303_, 1, v___f_5305_);
lean_ctor_set(v___x_5303_, 0, v___x_5309_);
v___x_5314_ = v___x_5303_;
goto v_reusejp_5313_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5309_);
lean_ctor_set(v_reuseFailAlloc_5322_, 1, v___f_5305_);
lean_ctor_set(v_reuseFailAlloc_5322_, 2, v___f_5312_);
lean_ctor_set(v_reuseFailAlloc_5322_, 3, v___f_5311_);
lean_ctor_set(v_reuseFailAlloc_5322_, 4, v___f_5310_);
v___x_5314_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5313_;
}
v_reusejp_5313_:
{
lean_object* v___x_5316_; 
if (v_isShared_5297_ == 0)
{
lean_ctor_set(v___x_5296_, 1, v___f_5306_);
lean_ctor_set(v___x_5296_, 0, v___x_5314_);
v___x_5316_ = v___x_5296_;
goto v_reusejp_5315_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v___x_5314_);
lean_ctor_set(v_reuseFailAlloc_5321_, 1, v___f_5306_);
v___x_5316_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5315_;
}
v_reusejp_5315_:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; lean_object* v___x_27323__overap_5319_; lean_object* v___x_5320_; 
v___x_5317_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
v___x_5318_ = l_instInhabitedOfMonad___redArg(v___x_5316_, v___x_5317_);
v___x_27323__overap_5319_ = lean_panic_fn_borrowed(v___x_5318_, v_msg_5262_);
lean_dec(v___x_5318_);
lean_inc(v___y_5266_);
lean_inc_ref(v___y_5265_);
lean_inc(v___y_5264_);
lean_inc_ref(v___y_5263_);
v___x_5320_ = lean_apply_5(v___x_27323__overap_5319_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, lean_box(0));
return v___x_5320_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
lean_object* v_res_5339_; 
v_res_5339_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5333_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
lean_dec(v___y_5337_);
lean_dec_ref(v___y_5336_);
lean_dec(v___y_5335_);
lean_dec_ref(v___y_5334_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v___x_5346_; 
v___x_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5346_, 0, v___x_5340_);
return v___x_5346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
lean_object* v_res_5353_; 
v_res_5353_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5347_, v___y_5348_, v___y_5349_, v___y_5350_, v___y_5351_);
lean_dec(v___y_5351_);
lean_dec_ref(v___y_5350_);
lean_dec(v___y_5349_);
lean_dec_ref(v___y_5348_);
return v_res_5353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5354_, lean_object* v_onAlt_5355_, uint8_t v_useSplitter_5356_, lean_object* v_extraEqualities_5357_, lean_object* v_numDiscrEqs_5358_, lean_object* v_a_5359_, lean_object* v_b_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_){
_start:
{
lean_object* v___y_5367_; uint8_t v___x_5390_; 
v___x_5390_ = lean_nat_dec_lt(v_a_5359_, v_upperBound_5354_);
if (v___x_5390_ == 0)
{
lean_object* v___x_5391_; 
lean_dec(v_a_5359_);
lean_dec(v_numDiscrEqs_5358_);
lean_dec(v_extraEqualities_5357_);
lean_dec_ref(v_onAlt_5355_);
v___x_5391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5391_, 0, v_b_5360_);
return v___x_5391_;
}
else
{
lean_object* v_snd_5392_; lean_object* v_snd_5393_; lean_object* v_snd_5394_; lean_object* v_snd_5395_; lean_object* v_snd_5396_; lean_object* v_fst_5397_; lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5601_; 
v_snd_5392_ = lean_ctor_get(v_b_5360_, 1);
lean_inc(v_snd_5392_);
v_snd_5393_ = lean_ctor_get(v_snd_5392_, 1);
lean_inc(v_snd_5393_);
v_snd_5394_ = lean_ctor_get(v_snd_5393_, 1);
lean_inc(v_snd_5394_);
v_snd_5395_ = lean_ctor_get(v_snd_5394_, 1);
lean_inc(v_snd_5395_);
v_snd_5396_ = lean_ctor_get(v_snd_5395_, 1);
lean_inc(v_snd_5396_);
v_fst_5397_ = lean_ctor_get(v_b_5360_, 0);
v_isSharedCheck_5601_ = !lean_is_exclusive(v_b_5360_);
if (v_isSharedCheck_5601_ == 0)
{
lean_object* v_unused_5602_; 
v_unused_5602_ = lean_ctor_get(v_b_5360_, 1);
lean_dec(v_unused_5602_);
v___x_5399_ = v_b_5360_;
v_isShared_5400_ = v_isSharedCheck_5601_;
goto v_resetjp_5398_;
}
else
{
lean_inc(v_fst_5397_);
lean_dec(v_b_5360_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5601_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v_fst_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5599_; 
v_fst_5401_ = lean_ctor_get(v_snd_5392_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v_snd_5392_);
if (v_isSharedCheck_5599_ == 0)
{
lean_object* v_unused_5600_; 
v_unused_5600_ = lean_ctor_get(v_snd_5392_, 1);
lean_dec(v_unused_5600_);
v___x_5403_ = v_snd_5392_;
v_isShared_5404_ = v_isSharedCheck_5599_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_fst_5401_);
lean_dec(v_snd_5392_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5599_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v_fst_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5597_; 
v_fst_5405_ = lean_ctor_get(v_snd_5393_, 0);
v_isSharedCheck_5597_ = !lean_is_exclusive(v_snd_5393_);
if (v_isSharedCheck_5597_ == 0)
{
lean_object* v_unused_5598_; 
v_unused_5598_ = lean_ctor_get(v_snd_5393_, 1);
lean_dec(v_unused_5598_);
v___x_5407_ = v_snd_5393_;
v_isShared_5408_ = v_isSharedCheck_5597_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_fst_5405_);
lean_dec(v_snd_5393_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5597_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v_fst_5409_; lean_object* v___x_5411_; uint8_t v_isShared_5412_; uint8_t v_isSharedCheck_5595_; 
v_fst_5409_ = lean_ctor_get(v_snd_5394_, 0);
v_isSharedCheck_5595_ = !lean_is_exclusive(v_snd_5394_);
if (v_isSharedCheck_5595_ == 0)
{
lean_object* v_unused_5596_; 
v_unused_5596_ = lean_ctor_get(v_snd_5394_, 1);
lean_dec(v_unused_5596_);
v___x_5411_ = v_snd_5394_;
v_isShared_5412_ = v_isSharedCheck_5595_;
goto v_resetjp_5410_;
}
else
{
lean_inc(v_fst_5409_);
lean_dec(v_snd_5394_);
v___x_5411_ = lean_box(0);
v_isShared_5412_ = v_isSharedCheck_5595_;
goto v_resetjp_5410_;
}
v_resetjp_5410_:
{
lean_object* v_fst_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5593_; 
v_fst_5413_ = lean_ctor_get(v_snd_5395_, 0);
v_isSharedCheck_5593_ = !lean_is_exclusive(v_snd_5395_);
if (v_isSharedCheck_5593_ == 0)
{
lean_object* v_unused_5594_; 
v_unused_5594_ = lean_ctor_get(v_snd_5395_, 1);
lean_dec(v_unused_5594_);
v___x_5415_ = v_snd_5395_;
v_isShared_5416_ = v_isSharedCheck_5593_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_fst_5413_);
lean_dec(v_snd_5395_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5593_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v_array_5417_; lean_object* v_start_5418_; lean_object* v_stop_5419_; uint8_t v___x_5420_; 
v_array_5417_ = lean_ctor_get(v_snd_5396_, 0);
v_start_5418_ = lean_ctor_get(v_snd_5396_, 1);
v_stop_5419_ = lean_ctor_get(v_snd_5396_, 2);
v___x_5420_ = lean_nat_dec_lt(v_start_5418_, v_stop_5419_);
if (v___x_5420_ == 0)
{
lean_object* v___x_5422_; 
if (v_isShared_5416_ == 0)
{
v___x_5422_ = v___x_5415_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_fst_5413_);
lean_ctor_set(v_reuseFailAlloc_5437_, 1, v_snd_5396_);
v___x_5422_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
lean_object* v___x_5424_; 
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 1, v___x_5422_);
v___x_5424_ = v___x_5411_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_fst_5409_);
lean_ctor_set(v_reuseFailAlloc_5436_, 1, v___x_5422_);
v___x_5424_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
lean_object* v___x_5426_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 1, v___x_5424_);
v___x_5426_ = v___x_5407_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_fst_5405_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v___x_5424_);
v___x_5426_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
lean_object* v___x_5428_; 
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 1, v___x_5426_);
v___x_5428_ = v___x_5403_;
goto v_reusejp_5427_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_fst_5401_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v___x_5426_);
v___x_5428_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5427_;
}
v_reusejp_5427_:
{
lean_object* v___x_5430_; 
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 1, v___x_5428_);
v___x_5430_ = v___x_5399_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_fst_5397_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v___x_5428_);
v___x_5430_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
lean_object* v___x_5431_; lean_object* v___f_5432_; 
v___x_5431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5431_, 0, v___x_5430_);
v___f_5432_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5432_, 0, v___x_5431_);
v___y_5367_ = v___f_5432_;
goto v___jp_5366_;
}
}
}
}
}
}
else
{
lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5589_; 
lean_inc(v_stop_5419_);
lean_inc(v_start_5418_);
lean_inc_ref(v_array_5417_);
v_isSharedCheck_5589_ = !lean_is_exclusive(v_snd_5396_);
if (v_isSharedCheck_5589_ == 0)
{
lean_object* v_unused_5590_; lean_object* v_unused_5591_; lean_object* v_unused_5592_; 
v_unused_5590_ = lean_ctor_get(v_snd_5396_, 2);
lean_dec(v_unused_5590_);
v_unused_5591_ = lean_ctor_get(v_snd_5396_, 1);
lean_dec(v_unused_5591_);
v_unused_5592_ = lean_ctor_get(v_snd_5396_, 0);
lean_dec(v_unused_5592_);
v___x_5439_ = v_snd_5396_;
v_isShared_5440_ = v_isSharedCheck_5589_;
goto v_resetjp_5438_;
}
else
{
lean_dec(v_snd_5396_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5589_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v_array_5441_; lean_object* v_start_5442_; lean_object* v_stop_5443_; lean_object* v___x_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; lean_object* v___x_5448_; 
v_array_5441_ = lean_ctor_get(v_fst_5413_, 0);
v_start_5442_ = lean_ctor_get(v_fst_5413_, 1);
v_stop_5443_ = lean_ctor_get(v_fst_5413_, 2);
v___x_5444_ = lean_array_fget(v_array_5417_, v_start_5418_);
v___x_5445_ = lean_unsigned_to_nat(1u);
v___x_5446_ = lean_nat_add(v_start_5418_, v___x_5445_);
lean_dec(v_start_5418_);
if (v_isShared_5440_ == 0)
{
lean_ctor_set(v___x_5439_, 1, v___x_5446_);
v___x_5448_ = v___x_5439_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v_array_5417_);
lean_ctor_set(v_reuseFailAlloc_5588_, 1, v___x_5446_);
lean_ctor_set(v_reuseFailAlloc_5588_, 2, v_stop_5419_);
v___x_5448_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
uint8_t v___x_5449_; 
v___x_5449_ = lean_nat_dec_lt(v_start_5442_, v_stop_5443_);
if (v___x_5449_ == 0)
{
lean_object* v___x_5451_; 
lean_dec(v___x_5444_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 1, v___x_5448_);
v___x_5451_ = v___x_5415_;
goto v_reusejp_5450_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_fst_5413_);
lean_ctor_set(v_reuseFailAlloc_5466_, 1, v___x_5448_);
v___x_5451_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5450_;
}
v_reusejp_5450_:
{
lean_object* v___x_5453_; 
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 1, v___x_5451_);
v___x_5453_ = v___x_5411_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_fst_5409_);
lean_ctor_set(v_reuseFailAlloc_5465_, 1, v___x_5451_);
v___x_5453_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
lean_object* v___x_5455_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 1, v___x_5453_);
v___x_5455_ = v___x_5407_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v_fst_5405_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v___x_5453_);
v___x_5455_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5457_; 
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 1, v___x_5455_);
v___x_5457_ = v___x_5403_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_fst_5401_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v___x_5455_);
v___x_5457_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
lean_object* v___x_5459_; 
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 1, v___x_5457_);
v___x_5459_ = v___x_5399_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_fst_5397_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v___x_5457_);
v___x_5459_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
lean_object* v___x_5460_; lean_object* v___f_5461_; 
v___x_5460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5460_, 0, v___x_5459_);
v___f_5461_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5461_, 0, v___x_5460_);
v___y_5367_ = v___f_5461_;
goto v___jp_5366_;
}
}
}
}
}
}
else
{
lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5584_; 
lean_inc(v_stop_5443_);
lean_inc(v_start_5442_);
lean_inc_ref(v_array_5441_);
v_isSharedCheck_5584_ = !lean_is_exclusive(v_fst_5413_);
if (v_isSharedCheck_5584_ == 0)
{
lean_object* v_unused_5585_; lean_object* v_unused_5586_; lean_object* v_unused_5587_; 
v_unused_5585_ = lean_ctor_get(v_fst_5413_, 2);
lean_dec(v_unused_5585_);
v_unused_5586_ = lean_ctor_get(v_fst_5413_, 1);
lean_dec(v_unused_5586_);
v_unused_5587_ = lean_ctor_get(v_fst_5413_, 0);
lean_dec(v_unused_5587_);
v___x_5468_ = v_fst_5413_;
v_isShared_5469_ = v_isSharedCheck_5584_;
goto v_resetjp_5467_;
}
else
{
lean_dec(v_fst_5413_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5584_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v_array_5470_; lean_object* v_start_5471_; lean_object* v_stop_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5476_; 
v_array_5470_ = lean_ctor_get(v_fst_5409_, 0);
v_start_5471_ = lean_ctor_get(v_fst_5409_, 1);
v_stop_5472_ = lean_ctor_get(v_fst_5409_, 2);
v___x_5473_ = lean_array_fget(v_array_5441_, v_start_5442_);
v___x_5474_ = lean_nat_add(v_start_5442_, v___x_5445_);
lean_dec(v_start_5442_);
if (v_isShared_5469_ == 0)
{
lean_ctor_set(v___x_5468_, 1, v___x_5474_);
v___x_5476_ = v___x_5468_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_array_5441_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v___x_5474_);
lean_ctor_set(v_reuseFailAlloc_5583_, 2, v_stop_5443_);
v___x_5476_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
uint8_t v___x_5477_; 
v___x_5477_ = lean_nat_dec_lt(v_start_5471_, v_stop_5472_);
if (v___x_5477_ == 0)
{
lean_object* v___x_5479_; 
lean_dec(v___x_5473_);
lean_dec(v___x_5444_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 1, v___x_5448_);
lean_ctor_set(v___x_5415_, 0, v___x_5476_);
v___x_5479_ = v___x_5415_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5494_, 1, v___x_5448_);
v___x_5479_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
lean_object* v___x_5481_; 
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 1, v___x_5479_);
v___x_5481_ = v___x_5411_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_fst_5409_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v___x_5479_);
v___x_5481_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
lean_object* v___x_5483_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 1, v___x_5481_);
v___x_5483_ = v___x_5407_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v_fst_5405_);
lean_ctor_set(v_reuseFailAlloc_5492_, 1, v___x_5481_);
v___x_5483_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
lean_object* v___x_5485_; 
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 1, v___x_5483_);
v___x_5485_ = v___x_5403_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_fst_5401_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v___x_5483_);
v___x_5485_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
lean_object* v___x_5487_; 
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 1, v___x_5485_);
v___x_5487_ = v___x_5399_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_fst_5397_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v___x_5485_);
v___x_5487_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
lean_object* v___x_5488_; lean_object* v___f_5489_; 
v___x_5488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5488_, 0, v___x_5487_);
v___f_5489_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5489_, 0, v___x_5488_);
v___y_5367_ = v___f_5489_;
goto v___jp_5366_;
}
}
}
}
}
}
else
{
lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5579_; 
lean_inc(v_stop_5472_);
lean_inc(v_start_5471_);
lean_inc_ref(v_array_5470_);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_fst_5409_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; lean_object* v_unused_5581_; lean_object* v_unused_5582_; 
v_unused_5580_ = lean_ctor_get(v_fst_5409_, 2);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_fst_5409_, 1);
lean_dec(v_unused_5581_);
v_unused_5582_ = lean_ctor_get(v_fst_5409_, 0);
lean_dec(v_unused_5582_);
v___x_5496_ = v_fst_5409_;
v_isShared_5497_ = v_isSharedCheck_5579_;
goto v_resetjp_5495_;
}
else
{
lean_dec(v_fst_5409_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5579_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v_array_5498_; lean_object* v_start_5499_; lean_object* v_stop_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5504_; 
v_array_5498_ = lean_ctor_get(v_fst_5405_, 0);
v_start_5499_ = lean_ctor_get(v_fst_5405_, 1);
v_stop_5500_ = lean_ctor_get(v_fst_5405_, 2);
v___x_5501_ = lean_array_fget(v_array_5470_, v_start_5471_);
v___x_5502_ = lean_nat_add(v_start_5471_, v___x_5445_);
lean_dec(v_start_5471_);
if (v_isShared_5497_ == 0)
{
lean_ctor_set(v___x_5496_, 1, v___x_5502_);
v___x_5504_ = v___x_5496_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_array_5470_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v___x_5502_);
lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_stop_5472_);
v___x_5504_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
uint8_t v___x_5505_; 
v___x_5505_ = lean_nat_dec_lt(v_start_5499_, v_stop_5500_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5507_; 
lean_dec(v___x_5501_);
lean_dec(v___x_5473_);
lean_dec(v___x_5444_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 1, v___x_5448_);
lean_ctor_set(v___x_5415_, 0, v___x_5476_);
v___x_5507_ = v___x_5415_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v___x_5448_);
v___x_5507_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5509_; 
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 1, v___x_5507_);
lean_ctor_set(v___x_5411_, 0, v___x_5504_);
v___x_5509_ = v___x_5411_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v___x_5507_);
v___x_5509_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
lean_object* v___x_5511_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 1, v___x_5509_);
v___x_5511_ = v___x_5407_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_fst_5405_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v___x_5509_);
v___x_5511_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
lean_object* v___x_5513_; 
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 1, v___x_5511_);
v___x_5513_ = v___x_5403_;
goto v_reusejp_5512_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_fst_5401_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5511_);
v___x_5513_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5512_;
}
v_reusejp_5512_:
{
lean_object* v___x_5515_; 
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 1, v___x_5513_);
v___x_5515_ = v___x_5399_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_fst_5397_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5513_);
v___x_5515_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
lean_object* v___x_5516_; lean_object* v___f_5517_; 
v___x_5516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5516_, 0, v___x_5515_);
v___f_5517_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5517_, 0, v___x_5516_);
v___y_5367_ = v___f_5517_;
goto v___jp_5366_;
}
}
}
}
}
}
else
{
lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5574_; 
lean_inc(v_stop_5500_);
lean_inc(v_start_5499_);
lean_inc_ref(v_array_5498_);
v_isSharedCheck_5574_ = !lean_is_exclusive(v_fst_5405_);
if (v_isSharedCheck_5574_ == 0)
{
lean_object* v_unused_5575_; lean_object* v_unused_5576_; lean_object* v_unused_5577_; 
v_unused_5575_ = lean_ctor_get(v_fst_5405_, 2);
lean_dec(v_unused_5575_);
v_unused_5576_ = lean_ctor_get(v_fst_5405_, 1);
lean_dec(v_unused_5576_);
v_unused_5577_ = lean_ctor_get(v_fst_5405_, 0);
lean_dec(v_unused_5577_);
v___x_5524_ = v_fst_5405_;
v_isShared_5525_ = v_isSharedCheck_5574_;
goto v_resetjp_5523_;
}
else
{
lean_dec(v_fst_5405_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5574_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v_array_5526_; lean_object* v_start_5527_; lean_object* v_stop_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5532_; 
v_array_5526_ = lean_ctor_get(v_fst_5401_, 0);
v_start_5527_ = lean_ctor_get(v_fst_5401_, 1);
v_stop_5528_ = lean_ctor_get(v_fst_5401_, 2);
v___x_5529_ = lean_array_fget(v_array_5498_, v_start_5499_);
v___x_5530_ = lean_nat_add(v_start_5499_, v___x_5445_);
lean_dec(v_start_5499_);
if (v_isShared_5525_ == 0)
{
lean_ctor_set(v___x_5524_, 1, v___x_5530_);
v___x_5532_ = v___x_5524_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_array_5498_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v___x_5530_);
lean_ctor_set(v_reuseFailAlloc_5573_, 2, v_stop_5500_);
v___x_5532_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
uint8_t v___x_5533_; 
v___x_5533_ = lean_nat_dec_lt(v_start_5527_, v_stop_5528_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5535_; 
lean_dec(v___x_5529_);
lean_dec(v___x_5501_);
lean_dec(v___x_5473_);
lean_dec(v___x_5444_);
if (v_isShared_5416_ == 0)
{
lean_ctor_set(v___x_5415_, 1, v___x_5448_);
lean_ctor_set(v___x_5415_, 0, v___x_5476_);
v___x_5535_ = v___x_5415_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5476_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v___x_5448_);
v___x_5535_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
lean_object* v___x_5537_; 
if (v_isShared_5412_ == 0)
{
lean_ctor_set(v___x_5411_, 1, v___x_5535_);
lean_ctor_set(v___x_5411_, 0, v___x_5504_);
v___x_5537_ = v___x_5411_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v___x_5535_);
v___x_5537_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___x_5539_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 1, v___x_5537_);
lean_ctor_set(v___x_5407_, 0, v___x_5532_);
v___x_5539_ = v___x_5407_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v___x_5537_);
v___x_5539_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5541_; 
if (v_isShared_5404_ == 0)
{
lean_ctor_set(v___x_5403_, 1, v___x_5539_);
v___x_5541_ = v___x_5403_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_fst_5401_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v___x_5539_);
v___x_5541_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5543_; 
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 1, v___x_5541_);
v___x_5543_ = v___x_5399_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_fst_5397_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v___x_5541_);
v___x_5543_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5544_; lean_object* v___f_5545_; 
v___x_5544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5543_);
v___f_5545_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5545_, 0, v___x_5544_);
v___y_5367_ = v___f_5545_;
goto v___jp_5366_;
}
}
}
}
}
}
else
{
lean_object* v___x_5552_; uint8_t v_isShared_5553_; uint8_t v_isSharedCheck_5569_; 
lean_inc(v_stop_5528_);
lean_inc(v_start_5527_);
lean_inc_ref(v_array_5526_);
lean_del_object(v___x_5415_);
lean_del_object(v___x_5411_);
lean_del_object(v___x_5407_);
lean_del_object(v___x_5403_);
lean_del_object(v___x_5399_);
v_isSharedCheck_5569_ = !lean_is_exclusive(v_fst_5401_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; lean_object* v_unused_5571_; lean_object* v_unused_5572_; 
v_unused_5570_ = lean_ctor_get(v_fst_5401_, 2);
lean_dec(v_unused_5570_);
v_unused_5571_ = lean_ctor_get(v_fst_5401_, 1);
lean_dec(v_unused_5571_);
v_unused_5572_ = lean_ctor_get(v_fst_5401_, 0);
lean_dec(v_unused_5572_);
v___x_5552_ = v_fst_5401_;
v_isShared_5553_ = v_isSharedCheck_5569_;
goto v_resetjp_5551_;
}
else
{
lean_dec(v_fst_5401_);
v___x_5552_ = lean_box(0);
v_isShared_5553_ = v_isSharedCheck_5569_;
goto v_resetjp_5551_;
}
v_resetjp_5551_:
{
lean_object* v_numOverlaps_5554_; lean_object* v___x_5555_; uint8_t v___x_5556_; 
v_numOverlaps_5554_ = lean_ctor_get(v___x_5529_, 1);
v___x_5555_ = lean_unsigned_to_nat(0u);
v___x_5556_ = lean_nat_dec_eq(v_numOverlaps_5554_, v___x_5555_);
if (v___x_5556_ == 0)
{
lean_object* v___x_5557_; lean_object* v___x_5558_; 
lean_del_object(v___x_5552_);
lean_dec_ref(v___x_5532_);
lean_dec(v___x_5529_);
lean_dec(v_stop_5528_);
lean_dec(v_start_5527_);
lean_dec_ref(v_array_5526_);
lean_dec_ref(v___x_5504_);
lean_dec(v___x_5501_);
lean_dec_ref(v___x_5476_);
lean_dec(v___x_5473_);
lean_dec_ref(v___x_5448_);
lean_dec(v___x_5444_);
lean_dec(v_fst_5397_);
v___x_5557_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_5558_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed), 6, 1);
lean_closure_set(v___x_5558_, 0, v___x_5557_);
v___y_5367_ = v___x_5558_;
goto v___jp_5366_;
}
else
{
uint8_t v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5561_; lean_object* v___x_5562_; lean_object* v___f_5563_; lean_object* v___x_5564_; lean_object* v___x_5566_; 
v___x_5559_ = 0;
v___x_5560_ = lean_array_fget_borrowed(v_array_5526_, v_start_5527_);
v___x_5561_ = lean_box(v___x_5559_);
v___x_5562_ = lean_box(v_useSplitter_5356_);
lean_inc(v_numDiscrEqs_5358_);
lean_inc(v_extraEqualities_5357_);
lean_inc(v___x_5560_);
lean_inc(v_a_5359_);
lean_inc_ref(v_onAlt_5355_);
v___f_5563_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 17, 10);
lean_closure_set(v___f_5563_, 0, v___x_5501_);
lean_closure_set(v___f_5563_, 1, v_onAlt_5355_);
lean_closure_set(v___f_5563_, 2, v_a_5359_);
lean_closure_set(v___f_5563_, 3, v___x_5561_);
lean_closure_set(v___f_5563_, 4, v___x_5562_);
lean_closure_set(v___f_5563_, 5, v___x_5560_);
lean_closure_set(v___f_5563_, 6, v_extraEqualities_5357_);
lean_closure_set(v___f_5563_, 7, v_numDiscrEqs_5358_);
lean_closure_set(v___f_5563_, 8, v___x_5444_);
lean_closure_set(v___f_5563_, 9, v___x_5445_);
v___x_5564_ = lean_nat_add(v_start_5527_, v___x_5445_);
lean_dec(v_start_5527_);
if (v_isShared_5553_ == 0)
{
lean_ctor_set(v___x_5552_, 1, v___x_5564_);
v___x_5566_ = v___x_5552_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_array_5526_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5568_, 2, v_stop_5528_);
v___x_5566_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___f_5567_; 
v___f_5567_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5567_, 0, v___x_5473_);
lean_closure_set(v___f_5567_, 1, v___x_5529_);
lean_closure_set(v___f_5567_, 2, v___f_5563_);
lean_closure_set(v___f_5567_, 3, v_fst_5397_);
lean_closure_set(v___f_5567_, 4, v___x_5476_);
lean_closure_set(v___f_5567_, 5, v___x_5448_);
lean_closure_set(v___f_5567_, 6, v___x_5504_);
lean_closure_set(v___f_5567_, 7, v___x_5532_);
lean_closure_set(v___f_5567_, 8, v___x_5566_);
v___y_5367_ = v___f_5567_;
goto v___jp_5366_;
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
v___jp_5366_:
{
lean_object* v___x_5368_; 
lean_inc(v___y_5364_);
lean_inc_ref(v___y_5363_);
lean_inc(v___y_5362_);
lean_inc_ref(v___y_5361_);
v___x_5368_ = lean_apply_5(v___y_5367_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_, lean_box(0));
if (lean_obj_tag(v___x_5368_) == 0)
{
lean_object* v_a_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5381_; 
v_a_5369_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5371_ = v___x_5368_;
v_isShared_5372_ = v_isSharedCheck_5381_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_a_5369_);
lean_dec(v___x_5368_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5381_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
if (lean_obj_tag(v_a_5369_) == 0)
{
lean_object* v_a_5373_; lean_object* v___x_5375_; 
lean_dec(v_a_5359_);
lean_dec(v_numDiscrEqs_5358_);
lean_dec(v_extraEqualities_5357_);
lean_dec_ref(v_onAlt_5355_);
v_a_5373_ = lean_ctor_get(v_a_5369_, 0);
lean_inc(v_a_5373_);
lean_dec_ref_known(v_a_5369_, 1);
if (v_isShared_5372_ == 0)
{
lean_ctor_set(v___x_5371_, 0, v_a_5373_);
v___x_5375_ = v___x_5371_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_a_5373_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
else
{
lean_object* v_a_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; 
lean_del_object(v___x_5371_);
v_a_5377_ = lean_ctor_get(v_a_5369_, 0);
lean_inc(v_a_5377_);
lean_dec_ref_known(v_a_5369_, 1);
v___x_5378_ = lean_unsigned_to_nat(1u);
v___x_5379_ = lean_nat_add(v_a_5359_, v___x_5378_);
lean_dec(v_a_5359_);
v_a_5359_ = v___x_5379_;
v_b_5360_ = v_a_5377_;
goto _start;
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_dec(v_a_5359_);
lean_dec(v_numDiscrEqs_5358_);
lean_dec(v_extraEqualities_5357_);
lean_dec_ref(v_onAlt_5355_);
v_a_5382_ = lean_ctor_get(v___x_5368_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5368_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5368_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5368_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5603_, lean_object* v_onAlt_5604_, lean_object* v_useSplitter_5605_, lean_object* v_extraEqualities_5606_, lean_object* v_numDiscrEqs_5607_, lean_object* v_a_5608_, lean_object* v_b_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_){
_start:
{
uint8_t v_useSplitter_boxed_5615_; lean_object* v_res_5616_; 
v_useSplitter_boxed_5615_ = lean_unbox(v_useSplitter_5605_);
v_res_5616_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5603_, v_onAlt_5604_, v_useSplitter_boxed_5615_, v_extraEqualities_5606_, v_numDiscrEqs_5607_, v_a_5608_, v_b_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v___y_5611_);
lean_dec_ref(v___y_5610_);
lean_dec(v_upperBound_5603_);
return v_res_5616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5617_, lean_object* v_as_5618_, size_t v_sz_5619_, size_t v_i_5620_, lean_object* v_b_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_, lean_object* v___y_5625_){
_start:
{
lean_object* v_a_5628_; uint8_t v___x_5632_; 
v___x_5632_ = lean_usize_dec_lt(v_i_5620_, v_sz_5619_);
if (v___x_5632_ == 0)
{
lean_object* v___x_5633_; 
v___x_5633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5633_, 0, v_b_5621_);
return v___x_5633_;
}
else
{
lean_object* v_snd_5634_; lean_object* v_snd_5635_; lean_object* v_snd_5636_; lean_object* v_snd_5637_; lean_object* v_fst_5638_; lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5784_; 
v_snd_5634_ = lean_ctor_get(v_b_5621_, 1);
lean_inc(v_snd_5634_);
v_snd_5635_ = lean_ctor_get(v_snd_5634_, 1);
lean_inc(v_snd_5635_);
v_snd_5636_ = lean_ctor_get(v_snd_5635_, 1);
lean_inc(v_snd_5636_);
v_snd_5637_ = lean_ctor_get(v_snd_5636_, 1);
lean_inc(v_snd_5637_);
v_fst_5638_ = lean_ctor_get(v_b_5621_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v_b_5621_);
if (v_isSharedCheck_5784_ == 0)
{
lean_object* v_unused_5785_; 
v_unused_5785_ = lean_ctor_get(v_b_5621_, 1);
lean_dec(v_unused_5785_);
v___x_5640_ = v_b_5621_;
v_isShared_5641_ = v_isSharedCheck_5784_;
goto v_resetjp_5639_;
}
else
{
lean_inc(v_fst_5638_);
lean_dec(v_b_5621_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5784_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
lean_object* v_fst_5642_; lean_object* v___x_5644_; uint8_t v_isShared_5645_; uint8_t v_isSharedCheck_5782_; 
v_fst_5642_ = lean_ctor_get(v_snd_5634_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v_snd_5634_);
if (v_isSharedCheck_5782_ == 0)
{
lean_object* v_unused_5783_; 
v_unused_5783_ = lean_ctor_get(v_snd_5634_, 1);
lean_dec(v_unused_5783_);
v___x_5644_ = v_snd_5634_;
v_isShared_5645_ = v_isSharedCheck_5782_;
goto v_resetjp_5643_;
}
else
{
lean_inc(v_fst_5642_);
lean_dec(v_snd_5634_);
v___x_5644_ = lean_box(0);
v_isShared_5645_ = v_isSharedCheck_5782_;
goto v_resetjp_5643_;
}
v_resetjp_5643_:
{
lean_object* v_fst_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5780_; 
v_fst_5646_ = lean_ctor_get(v_snd_5635_, 0);
v_isSharedCheck_5780_ = !lean_is_exclusive(v_snd_5635_);
if (v_isSharedCheck_5780_ == 0)
{
lean_object* v_unused_5781_; 
v_unused_5781_ = lean_ctor_get(v_snd_5635_, 1);
lean_dec(v_unused_5781_);
v___x_5648_ = v_snd_5635_;
v_isShared_5649_ = v_isSharedCheck_5780_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_fst_5646_);
lean_dec(v_snd_5635_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5780_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v_fst_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5778_; 
v_fst_5650_ = lean_ctor_get(v_snd_5636_, 0);
v_isSharedCheck_5778_ = !lean_is_exclusive(v_snd_5636_);
if (v_isSharedCheck_5778_ == 0)
{
lean_object* v_unused_5779_; 
v_unused_5779_ = lean_ctor_get(v_snd_5636_, 1);
lean_dec(v_unused_5779_);
v___x_5652_ = v_snd_5636_;
v_isShared_5653_ = v_isSharedCheck_5778_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_fst_5650_);
lean_dec(v_snd_5636_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5778_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v_array_5654_; lean_object* v_start_5655_; lean_object* v_stop_5656_; uint8_t v___x_5657_; 
v_array_5654_ = lean_ctor_get(v_snd_5637_, 0);
v_start_5655_ = lean_ctor_get(v_snd_5637_, 1);
v_stop_5656_ = lean_ctor_get(v_snd_5637_, 2);
v___x_5657_ = lean_nat_dec_lt(v_start_5655_, v_stop_5656_);
if (v___x_5657_ == 0)
{
lean_object* v___x_5659_; 
if (v_isShared_5653_ == 0)
{
v___x_5659_ = v___x_5652_;
goto v_reusejp_5658_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_fst_5650_);
lean_ctor_set(v_reuseFailAlloc_5670_, 1, v_snd_5637_);
v___x_5659_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5658_;
}
v_reusejp_5658_:
{
lean_object* v___x_5661_; 
if (v_isShared_5649_ == 0)
{
lean_ctor_set(v___x_5648_, 1, v___x_5659_);
v___x_5661_ = v___x_5648_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5669_; 
v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_fst_5646_);
lean_ctor_set(v_reuseFailAlloc_5669_, 1, v___x_5659_);
v___x_5661_ = v_reuseFailAlloc_5669_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
lean_object* v___x_5663_; 
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 1, v___x_5661_);
v___x_5663_ = v___x_5644_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_fst_5642_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v___x_5661_);
v___x_5663_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
lean_object* v___x_5665_; 
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 1, v___x_5663_);
v___x_5665_ = v___x_5640_;
goto v_reusejp_5664_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_fst_5638_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v___x_5663_);
v___x_5665_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5664_;
}
v_reusejp_5664_:
{
lean_object* v___x_5666_; 
v___x_5666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5666_, 0, v___x_5665_);
return v___x_5666_;
}
}
}
}
}
else
{
lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5774_; 
lean_inc(v_stop_5656_);
lean_inc(v_start_5655_);
lean_inc_ref(v_array_5654_);
v_isSharedCheck_5774_ = !lean_is_exclusive(v_snd_5637_);
if (v_isSharedCheck_5774_ == 0)
{
lean_object* v_unused_5775_; lean_object* v_unused_5776_; lean_object* v_unused_5777_; 
v_unused_5775_ = lean_ctor_get(v_snd_5637_, 2);
lean_dec(v_unused_5775_);
v_unused_5776_ = lean_ctor_get(v_snd_5637_, 1);
lean_dec(v_unused_5776_);
v_unused_5777_ = lean_ctor_get(v_snd_5637_, 0);
lean_dec(v_unused_5777_);
v___x_5672_ = v_snd_5637_;
v_isShared_5673_ = v_isSharedCheck_5774_;
goto v_resetjp_5671_;
}
else
{
lean_dec(v_snd_5637_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5774_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v_array_5674_; lean_object* v_start_5675_; lean_object* v_stop_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5681_; 
v_array_5674_ = lean_ctor_get(v_fst_5650_, 0);
v_start_5675_ = lean_ctor_get(v_fst_5650_, 1);
v_stop_5676_ = lean_ctor_get(v_fst_5650_, 2);
v___x_5677_ = lean_array_fget(v_array_5654_, v_start_5655_);
v___x_5678_ = lean_unsigned_to_nat(1u);
v___x_5679_ = lean_nat_add(v_start_5655_, v___x_5678_);
lean_dec(v_start_5655_);
if (v_isShared_5673_ == 0)
{
lean_ctor_set(v___x_5672_, 1, v___x_5679_);
v___x_5681_ = v___x_5672_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v_array_5654_);
lean_ctor_set(v_reuseFailAlloc_5773_, 1, v___x_5679_);
lean_ctor_set(v_reuseFailAlloc_5773_, 2, v_stop_5656_);
v___x_5681_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
uint8_t v___x_5682_; 
v___x_5682_ = lean_nat_dec_lt(v_start_5675_, v_stop_5676_);
if (v___x_5682_ == 0)
{
lean_object* v___x_5684_; 
lean_dec(v___x_5677_);
if (v_isShared_5653_ == 0)
{
lean_ctor_set(v___x_5652_, 1, v___x_5681_);
v___x_5684_ = v___x_5652_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_fst_5650_);
lean_ctor_set(v_reuseFailAlloc_5695_, 1, v___x_5681_);
v___x_5684_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
lean_object* v___x_5686_; 
if (v_isShared_5649_ == 0)
{
lean_ctor_set(v___x_5648_, 1, v___x_5684_);
v___x_5686_ = v___x_5648_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_fst_5646_);
lean_ctor_set(v_reuseFailAlloc_5694_, 1, v___x_5684_);
v___x_5686_ = v_reuseFailAlloc_5694_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
lean_object* v___x_5688_; 
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 1, v___x_5686_);
v___x_5688_ = v___x_5644_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5693_; 
v_reuseFailAlloc_5693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5693_, 0, v_fst_5642_);
lean_ctor_set(v_reuseFailAlloc_5693_, 1, v___x_5686_);
v___x_5688_ = v_reuseFailAlloc_5693_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
lean_object* v___x_5690_; 
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 1, v___x_5688_);
v___x_5690_ = v___x_5640_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_fst_5638_);
lean_ctor_set(v_reuseFailAlloc_5692_, 1, v___x_5688_);
v___x_5690_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
lean_object* v___x_5691_; 
v___x_5691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
return v___x_5691_;
}
}
}
}
}
else
{
lean_object* v___x_5697_; uint8_t v_isShared_5698_; uint8_t v_isSharedCheck_5769_; 
lean_inc(v_stop_5676_);
lean_inc(v_start_5675_);
lean_inc_ref(v_array_5674_);
v_isSharedCheck_5769_ = !lean_is_exclusive(v_fst_5650_);
if (v_isSharedCheck_5769_ == 0)
{
lean_object* v_unused_5770_; lean_object* v_unused_5771_; lean_object* v_unused_5772_; 
v_unused_5770_ = lean_ctor_get(v_fst_5650_, 2);
lean_dec(v_unused_5770_);
v_unused_5771_ = lean_ctor_get(v_fst_5650_, 1);
lean_dec(v_unused_5771_);
v_unused_5772_ = lean_ctor_get(v_fst_5650_, 0);
lean_dec(v_unused_5772_);
v___x_5697_ = v_fst_5650_;
v_isShared_5698_ = v_isSharedCheck_5769_;
goto v_resetjp_5696_;
}
else
{
lean_dec(v_fst_5650_);
v___x_5697_ = lean_box(0);
v_isShared_5698_ = v_isSharedCheck_5769_;
goto v_resetjp_5696_;
}
v_resetjp_5696_:
{
lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5702_; 
v___x_5699_ = lean_array_fget(v_array_5674_, v_start_5675_);
v___x_5700_ = lean_nat_add(v_start_5675_, v___x_5678_);
lean_dec(v_start_5675_);
if (v_isShared_5698_ == 0)
{
lean_ctor_set(v___x_5697_, 1, v___x_5700_);
v___x_5702_ = v___x_5697_;
goto v_reusejp_5701_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_array_5674_);
lean_ctor_set(v_reuseFailAlloc_5768_, 1, v___x_5700_);
lean_ctor_set(v_reuseFailAlloc_5768_, 2, v_stop_5676_);
v___x_5702_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5701_;
}
v_reusejp_5701_:
{
if (v_addEqualities_5617_ == 0)
{
lean_dec(v___x_5699_);
goto v___jp_5703_;
}
else
{
if (lean_obj_tag(v___x_5677_) == 0)
{
lean_object* v_a_5719_; lean_object* v___x_5720_; 
lean_del_object(v___x_5652_);
lean_del_object(v___x_5648_);
lean_del_object(v___x_5644_);
lean_del_object(v___x_5640_);
v_a_5719_ = lean_array_uget_borrowed(v_as_5618_, v_i_5620_);
lean_inc(v_a_5719_);
v___x_5720_ = l_Lean_Meta_isProof(v_a_5719_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_object* v_a_5721_; uint8_t v___x_5722_; 
v_a_5721_ = lean_ctor_get(v___x_5720_, 0);
lean_inc(v_a_5721_);
lean_dec_ref_known(v___x_5720_, 1);
v___x_5722_ = lean_unbox(v_a_5721_);
lean_dec(v_a_5721_);
if (v___x_5722_ == 0)
{
lean_object* v___x_5723_; 
lean_inc(v_a_5719_);
v___x_5723_ = l_Lean_Meta_mkEqHEq(v___x_5699_, v_a_5719_, v___y_5622_, v___y_5623_, v___y_5624_, v___y_5625_);
if (lean_obj_tag(v___x_5723_) == 0)
{
lean_object* v_a_5724_; lean_object* v___x_5725_; 
v_a_5724_ = lean_ctor_get(v___x_5723_, 0);
lean_inc_n(v_a_5724_, 2);
lean_dec_ref_known(v___x_5723_, 1);
v___x_5725_ = l_Lean_mkArrow(v_a_5724_, v_fst_5638_, v___y_5624_, v___y_5625_);
if (lean_obj_tag(v___x_5725_) == 0)
{
lean_object* v_a_5726_; uint8_t v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; lean_object* v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; 
v_a_5726_ = lean_ctor_get(v___x_5725_, 0);
lean_inc(v_a_5726_);
lean_dec_ref_known(v___x_5725_, 1);
v___x_5727_ = l_Lean_Expr_isHEq(v_a_5724_);
lean_dec(v_a_5724_);
v___x_5728_ = lean_box(v___x_5727_);
v___x_5729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5728_);
v___x_5730_ = lean_array_push(v_fst_5642_, v___x_5729_);
v___x_5731_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_5732_ = lean_array_push(v_fst_5646_, v___x_5731_);
v___x_5733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5733_, 0, v___x_5702_);
lean_ctor_set(v___x_5733_, 1, v___x_5681_);
v___x_5734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5734_, 0, v___x_5732_);
lean_ctor_set(v___x_5734_, 1, v___x_5733_);
v___x_5735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5735_, 0, v___x_5730_);
lean_ctor_set(v___x_5735_, 1, v___x_5734_);
v___x_5736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5736_, 0, v_a_5726_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
v_a_5628_ = v___x_5736_;
goto v___jp_5627_;
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5744_; 
lean_dec(v_a_5724_);
lean_dec_ref(v___x_5702_);
lean_dec_ref(v___x_5681_);
lean_dec(v_fst_5646_);
lean_dec(v_fst_5642_);
v_a_5737_ = lean_ctor_get(v___x_5725_, 0);
v_isSharedCheck_5744_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5744_ == 0)
{
v___x_5739_ = v___x_5725_;
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5725_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5744_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v___x_5742_; 
if (v_isShared_5740_ == 0)
{
v___x_5742_ = v___x_5739_;
goto v_reusejp_5741_;
}
else
{
lean_object* v_reuseFailAlloc_5743_; 
v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
v___x_5742_ = v_reuseFailAlloc_5743_;
goto v_reusejp_5741_;
}
v_reusejp_5741_:
{
return v___x_5742_;
}
}
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec_ref(v___x_5702_);
lean_dec_ref(v___x_5681_);
lean_dec(v_fst_5646_);
lean_dec(v_fst_5642_);
lean_dec(v_fst_5638_);
v_a_5745_ = lean_ctor_get(v___x_5723_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5723_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5723_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5723_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5748_ == 0)
{
v___x_5750_ = v___x_5747_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
}
else
{
lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; 
lean_dec(v___x_5699_);
v___x_5753_ = lean_box(0);
v___x_5754_ = lean_array_push(v_fst_5642_, v___x_5753_);
v___x_5755_ = lean_array_push(v_fst_5646_, v___x_5677_);
v___x_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5702_);
lean_ctor_set(v___x_5756_, 1, v___x_5681_);
v___x_5757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5755_);
lean_ctor_set(v___x_5757_, 1, v___x_5756_);
v___x_5758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5758_, 0, v___x_5754_);
lean_ctor_set(v___x_5758_, 1, v___x_5757_);
v___x_5759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5759_, 0, v_fst_5638_);
lean_ctor_set(v___x_5759_, 1, v___x_5758_);
v_a_5628_ = v___x_5759_;
goto v___jp_5627_;
}
}
else
{
lean_object* v_a_5760_; lean_object* v___x_5762_; uint8_t v_isShared_5763_; uint8_t v_isSharedCheck_5767_; 
lean_dec_ref(v___x_5702_);
lean_dec(v___x_5699_);
lean_dec_ref(v___x_5681_);
lean_dec(v_fst_5646_);
lean_dec(v_fst_5642_);
lean_dec(v_fst_5638_);
v_a_5760_ = lean_ctor_get(v___x_5720_, 0);
v_isSharedCheck_5767_ = !lean_is_exclusive(v___x_5720_);
if (v_isSharedCheck_5767_ == 0)
{
v___x_5762_ = v___x_5720_;
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
else
{
lean_inc(v_a_5760_);
lean_dec(v___x_5720_);
v___x_5762_ = lean_box(0);
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
v_resetjp_5761_:
{
lean_object* v___x_5765_; 
if (v_isShared_5763_ == 0)
{
v___x_5765_ = v___x_5762_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_a_5760_);
v___x_5765_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
return v___x_5765_;
}
}
}
}
else
{
lean_dec(v___x_5699_);
goto v___jp_5703_;
}
}
v___jp_5703_:
{
lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5708_; 
v___x_5704_ = lean_box(0);
v___x_5705_ = lean_array_push(v_fst_5642_, v___x_5704_);
v___x_5706_ = lean_array_push(v_fst_5646_, v___x_5677_);
if (v_isShared_5653_ == 0)
{
lean_ctor_set(v___x_5652_, 1, v___x_5681_);
lean_ctor_set(v___x_5652_, 0, v___x_5702_);
v___x_5708_ = v___x_5652_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v___x_5702_);
lean_ctor_set(v_reuseFailAlloc_5718_, 1, v___x_5681_);
v___x_5708_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
lean_object* v___x_5710_; 
if (v_isShared_5649_ == 0)
{
lean_ctor_set(v___x_5648_, 1, v___x_5708_);
lean_ctor_set(v___x_5648_, 0, v___x_5706_);
v___x_5710_ = v___x_5648_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v___x_5706_);
lean_ctor_set(v_reuseFailAlloc_5717_, 1, v___x_5708_);
v___x_5710_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
lean_object* v___x_5712_; 
if (v_isShared_5645_ == 0)
{
lean_ctor_set(v___x_5644_, 1, v___x_5710_);
lean_ctor_set(v___x_5644_, 0, v___x_5705_);
v___x_5712_ = v___x_5644_;
goto v_reusejp_5711_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5705_);
lean_ctor_set(v_reuseFailAlloc_5716_, 1, v___x_5710_);
v___x_5712_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5711_;
}
v_reusejp_5711_:
{
lean_object* v___x_5714_; 
if (v_isShared_5641_ == 0)
{
lean_ctor_set(v___x_5640_, 1, v___x_5712_);
v___x_5714_ = v___x_5640_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_fst_5638_);
lean_ctor_set(v_reuseFailAlloc_5715_, 1, v___x_5712_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
v_a_5628_ = v___x_5714_;
goto v___jp_5627_;
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
v___jp_5627_:
{
size_t v___x_5629_; size_t v___x_5630_; 
v___x_5629_ = ((size_t)1ULL);
v___x_5630_ = lean_usize_add(v_i_5620_, v___x_5629_);
v_i_5620_ = v___x_5630_;
v_b_5621_ = v_a_5628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5786_, lean_object* v_as_5787_, lean_object* v_sz_5788_, lean_object* v_i_5789_, lean_object* v_b_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_){
_start:
{
uint8_t v_addEqualities_boxed_5796_; size_t v_sz_boxed_5797_; size_t v_i_boxed_5798_; lean_object* v_res_5799_; 
v_addEqualities_boxed_5796_ = lean_unbox(v_addEqualities_5786_);
v_sz_boxed_5797_ = lean_unbox_usize(v_sz_5788_);
lean_dec(v_sz_5788_);
v_i_boxed_5798_ = lean_unbox_usize(v_i_5789_);
lean_dec(v_i_5789_);
v_res_5799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5796_, v_as_5787_, v_sz_boxed_5797_, v_i_boxed_5798_, v_b_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_);
lean_dec(v___y_5794_);
lean_dec_ref(v___y_5793_);
lean_dec(v___y_5792_);
lean_dec_ref(v___y_5791_);
lean_dec_ref(v_as_5787_);
return v_res_5799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5800_, lean_object* v_toMatcherInfo_5801_, lean_object* v_a_5802_, uint8_t v_addEqualities_5803_, size_t v___x_5804_, lean_object* v_discrs_5805_, lean_object* v_motiveArgs_5806_, lean_object* v_motiveBody_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; uint8_t v___x_5907_; 
v___x_5905_ = lean_array_get_size(v_motiveArgs_5806_);
v___x_5906_ = lean_array_get_size(v_discrs_5805_);
v___x_5907_ = lean_nat_dec_eq(v___x_5905_, v___x_5906_);
if (v___x_5907_ == 0)
{
lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5923_; 
lean_dec_ref(v_motiveBody_5807_);
lean_dec_ref(v_motiveArgs_5806_);
lean_dec_ref(v_a_5802_);
lean_dec_ref(v_toMatcherInfo_5801_);
lean_dec_ref(v_onMotive_5800_);
v___x_5908_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5909_ = l_Nat_reprFast(v___x_5906_);
v___x_5910_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5909_);
v___x_5911_ = l_Lean_MessageData_ofFormat(v___x_5910_);
v___x_5912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5908_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5914_, 0, v___x_5912_);
lean_ctor_set(v___x_5914_, 1, v___x_5913_);
v___x_5915_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5914_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
v_a_5916_ = lean_ctor_get(v___x_5915_, 0);
v_isSharedCheck_5923_ = !lean_is_exclusive(v___x_5915_);
if (v_isSharedCheck_5923_ == 0)
{
v___x_5918_ = v___x_5915_;
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5915_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5921_; 
if (v_isShared_5919_ == 0)
{
v___x_5921_ = v___x_5918_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
else
{
goto v___jp_5813_;
}
v___jp_5813_:
{
lean_object* v___x_5814_; 
lean_inc(v___y_5811_);
lean_inc_ref(v___y_5810_);
lean_inc(v___y_5809_);
lean_inc_ref(v___y_5808_);
lean_inc_ref(v_motiveArgs_5806_);
v___x_5814_ = lean_apply_7(v_onMotive_5800_, v_motiveArgs_5806_, v_motiveBody_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, lean_box(0));
if (lean_obj_tag(v___x_5814_) == 0)
{
lean_object* v_a_5815_; lean_object* v_discrInfos_5816_; lean_object* v___x_5817_; lean_object* v_addHEqualities_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5825_; lean_object* v___x_5826_; size_t v_sz_5827_; lean_object* v___x_5828_; 
v_a_5815_ = lean_ctor_get(v___x_5814_, 0);
lean_inc(v_a_5815_);
lean_dec_ref_known(v___x_5814_, 1);
v_discrInfos_5816_ = lean_ctor_get(v_toMatcherInfo_5801_, 4);
lean_inc_ref(v_discrInfos_5816_);
lean_dec_ref(v_toMatcherInfo_5801_);
v___x_5817_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5818_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5819_ = lean_array_get_size(v_a_5802_);
v___x_5820_ = l_Array_toSubarray___redArg(v_a_5802_, v___x_5817_, v___x_5819_);
v___x_5821_ = lean_array_get_size(v_discrInfos_5816_);
v___x_5822_ = l_Array_toSubarray___redArg(v_discrInfos_5816_, v___x_5817_, v___x_5821_);
v___x_5823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5823_, 0, v___x_5820_);
lean_ctor_set(v___x_5823_, 1, v___x_5822_);
v___x_5824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5824_, 0, v_addHEqualities_5818_);
lean_ctor_set(v___x_5824_, 1, v___x_5823_);
v___x_5825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5825_, 0, v_addHEqualities_5818_);
lean_ctor_set(v___x_5825_, 1, v___x_5824_);
v___x_5826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5826_, 0, v_a_5815_);
lean_ctor_set(v___x_5826_, 1, v___x_5825_);
v_sz_5827_ = lean_array_size(v_motiveArgs_5806_);
v___x_5828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5803_, v_motiveArgs_5806_, v_sz_5827_, v___x_5804_, v___x_5826_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
if (lean_obj_tag(v___x_5828_) == 0)
{
lean_object* v_a_5829_; lean_object* v_snd_5830_; lean_object* v_snd_5831_; lean_object* v_fst_5832_; lean_object* v___x_5834_; uint8_t v_isShared_5835_; uint8_t v_isSharedCheck_5887_; 
v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5829_);
lean_dec_ref_known(v___x_5828_, 1);
v_snd_5830_ = lean_ctor_get(v_a_5829_, 1);
lean_inc(v_snd_5830_);
v_snd_5831_ = lean_ctor_get(v_snd_5830_, 1);
lean_inc(v_snd_5831_);
v_fst_5832_ = lean_ctor_get(v_a_5829_, 0);
v_isSharedCheck_5887_ = !lean_is_exclusive(v_a_5829_);
if (v_isSharedCheck_5887_ == 0)
{
lean_object* v_unused_5888_; 
v_unused_5888_ = lean_ctor_get(v_a_5829_, 1);
lean_dec(v_unused_5888_);
v___x_5834_ = v_a_5829_;
v_isShared_5835_ = v_isSharedCheck_5887_;
goto v_resetjp_5833_;
}
else
{
lean_inc(v_fst_5832_);
lean_dec(v_a_5829_);
v___x_5834_ = lean_box(0);
v_isShared_5835_ = v_isSharedCheck_5887_;
goto v_resetjp_5833_;
}
v_resetjp_5833_:
{
lean_object* v_fst_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5885_; 
v_fst_5836_ = lean_ctor_get(v_snd_5830_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v_snd_5830_);
if (v_isSharedCheck_5885_ == 0)
{
lean_object* v_unused_5886_; 
v_unused_5886_ = lean_ctor_get(v_snd_5830_, 1);
lean_dec(v_unused_5886_);
v___x_5838_ = v_snd_5830_;
v_isShared_5839_ = v_isSharedCheck_5885_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_fst_5836_);
lean_dec(v_snd_5830_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5885_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v_fst_5840_; lean_object* v___x_5842_; uint8_t v_isShared_5843_; uint8_t v_isSharedCheck_5883_; 
v_fst_5840_ = lean_ctor_get(v_snd_5831_, 0);
v_isSharedCheck_5883_ = !lean_is_exclusive(v_snd_5831_);
if (v_isSharedCheck_5883_ == 0)
{
lean_object* v_unused_5884_; 
v_unused_5884_ = lean_ctor_get(v_snd_5831_, 1);
lean_dec(v_unused_5884_);
v___x_5842_ = v_snd_5831_;
v_isShared_5843_ = v_isSharedCheck_5883_;
goto v_resetjp_5841_;
}
else
{
lean_inc(v_fst_5840_);
lean_dec(v_snd_5831_);
v___x_5842_ = lean_box(0);
v_isShared_5843_ = v_isSharedCheck_5883_;
goto v_resetjp_5841_;
}
v_resetjp_5841_:
{
uint8_t v___x_5844_; uint8_t v___x_5845_; uint8_t v___x_5846_; lean_object* v___x_5847_; 
v___x_5844_ = 0;
v___x_5845_ = 1;
v___x_5846_ = 1;
lean_inc(v_fst_5832_);
v___x_5847_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5806_, v_fst_5832_, v___x_5844_, v___x_5845_, v___x_5844_, v___x_5845_, v___x_5846_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
lean_dec_ref(v_motiveArgs_5806_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; lean_object* v___x_5849_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5847_, 1);
v___x_5849_ = l_Lean_Meta_getLevel(v_fst_5832_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5866_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5852_ = v___x_5849_;
v_isShared_5853_ = v_isSharedCheck_5866_;
goto v_resetjp_5851_;
}
else
{
lean_inc(v_a_5850_);
lean_dec(v___x_5849_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5866_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v___x_5855_; 
if (v_isShared_5843_ == 0)
{
lean_ctor_set(v___x_5842_, 1, v_fst_5840_);
lean_ctor_set(v___x_5842_, 0, v_fst_5836_);
v___x_5855_ = v___x_5842_;
goto v_reusejp_5854_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_fst_5836_);
lean_ctor_set(v_reuseFailAlloc_5865_, 1, v_fst_5840_);
v___x_5855_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5854_;
}
v_reusejp_5854_:
{
lean_object* v___x_5857_; 
if (v_isShared_5839_ == 0)
{
lean_ctor_set(v___x_5838_, 1, v___x_5855_);
lean_ctor_set(v___x_5838_, 0, v_a_5850_);
v___x_5857_ = v___x_5838_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5864_; 
v_reuseFailAlloc_5864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5864_, 0, v_a_5850_);
lean_ctor_set(v_reuseFailAlloc_5864_, 1, v___x_5855_);
v___x_5857_ = v_reuseFailAlloc_5864_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
lean_object* v___x_5859_; 
if (v_isShared_5835_ == 0)
{
lean_ctor_set(v___x_5834_, 1, v___x_5857_);
lean_ctor_set(v___x_5834_, 0, v_a_5848_);
v___x_5859_ = v___x_5834_;
goto v_reusejp_5858_;
}
else
{
lean_object* v_reuseFailAlloc_5863_; 
v_reuseFailAlloc_5863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5863_, 0, v_a_5848_);
lean_ctor_set(v_reuseFailAlloc_5863_, 1, v___x_5857_);
v___x_5859_ = v_reuseFailAlloc_5863_;
goto v_reusejp_5858_;
}
v_reusejp_5858_:
{
lean_object* v___x_5861_; 
if (v_isShared_5853_ == 0)
{
lean_ctor_set(v___x_5852_, 0, v___x_5859_);
v___x_5861_ = v___x_5852_;
goto v_reusejp_5860_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v___x_5859_);
v___x_5861_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5860_;
}
v_reusejp_5860_:
{
return v___x_5861_;
}
}
}
}
}
}
else
{
lean_object* v_a_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5874_; 
lean_dec(v_a_5848_);
lean_del_object(v___x_5842_);
lean_dec(v_fst_5840_);
lean_del_object(v___x_5838_);
lean_dec(v_fst_5836_);
lean_del_object(v___x_5834_);
v_a_5867_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5869_ = v___x_5849_;
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_a_5867_);
lean_dec(v___x_5849_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v___x_5872_; 
if (v_isShared_5870_ == 0)
{
v___x_5872_ = v___x_5869_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
v___x_5872_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
return v___x_5872_;
}
}
}
}
else
{
lean_object* v_a_5875_; lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5882_; 
lean_del_object(v___x_5842_);
lean_dec(v_fst_5840_);
lean_del_object(v___x_5838_);
lean_dec(v_fst_5836_);
lean_del_object(v___x_5834_);
lean_dec(v_fst_5832_);
v_a_5875_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5877_ = v___x_5847_;
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
else
{
lean_inc(v_a_5875_);
lean_dec(v___x_5847_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v___x_5880_; 
if (v_isShared_5878_ == 0)
{
v___x_5880_ = v___x_5877_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5875_);
v___x_5880_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
return v___x_5880_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5889_; lean_object* v___x_5891_; uint8_t v_isShared_5892_; uint8_t v_isSharedCheck_5896_; 
lean_dec_ref(v_motiveArgs_5806_);
v_a_5889_ = lean_ctor_get(v___x_5828_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v___x_5828_);
if (v_isSharedCheck_5896_ == 0)
{
v___x_5891_ = v___x_5828_;
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
else
{
lean_inc(v_a_5889_);
lean_dec(v___x_5828_);
v___x_5891_ = lean_box(0);
v_isShared_5892_ = v_isSharedCheck_5896_;
goto v_resetjp_5890_;
}
v_resetjp_5890_:
{
lean_object* v___x_5894_; 
if (v_isShared_5892_ == 0)
{
v___x_5894_ = v___x_5891_;
goto v_reusejp_5893_;
}
else
{
lean_object* v_reuseFailAlloc_5895_; 
v_reuseFailAlloc_5895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_a_5889_);
v___x_5894_ = v_reuseFailAlloc_5895_;
goto v_reusejp_5893_;
}
v_reusejp_5893_:
{
return v___x_5894_;
}
}
}
}
else
{
lean_object* v_a_5897_; lean_object* v___x_5899_; uint8_t v_isShared_5900_; uint8_t v_isSharedCheck_5904_; 
lean_dec_ref(v_motiveArgs_5806_);
lean_dec_ref(v_a_5802_);
lean_dec_ref(v_toMatcherInfo_5801_);
v_a_5897_ = lean_ctor_get(v___x_5814_, 0);
v_isSharedCheck_5904_ = !lean_is_exclusive(v___x_5814_);
if (v_isSharedCheck_5904_ == 0)
{
v___x_5899_ = v___x_5814_;
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
else
{
lean_inc(v_a_5897_);
lean_dec(v___x_5814_);
v___x_5899_ = lean_box(0);
v_isShared_5900_ = v_isSharedCheck_5904_;
goto v_resetjp_5898_;
}
v_resetjp_5898_:
{
lean_object* v___x_5902_; 
if (v_isShared_5900_ == 0)
{
v___x_5902_ = v___x_5899_;
goto v_reusejp_5901_;
}
else
{
lean_object* v_reuseFailAlloc_5903_; 
v_reuseFailAlloc_5903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
v___x_5902_ = v_reuseFailAlloc_5903_;
goto v_reusejp_5901_;
}
v_reusejp_5901_:
{
return v___x_5902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5924_, lean_object* v_toMatcherInfo_5925_, lean_object* v_a_5926_, lean_object* v_addEqualities_5927_, lean_object* v___x_5928_, lean_object* v_discrs_5929_, lean_object* v_motiveArgs_5930_, lean_object* v_motiveBody_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_){
_start:
{
uint8_t v_addEqualities_boxed_5937_; size_t v___x_34599__boxed_5938_; lean_object* v_res_5939_; 
v_addEqualities_boxed_5937_ = lean_unbox(v_addEqualities_5927_);
v___x_34599__boxed_5938_ = lean_unbox_usize(v___x_5928_);
lean_dec(v___x_5928_);
v_res_5939_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5924_, v_toMatcherInfo_5925_, v_a_5926_, v_addEqualities_boxed_5937_, v___x_34599__boxed_5938_, v_discrs_5929_, v_motiveArgs_5930_, v_motiveBody_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_);
lean_dec(v___y_5935_);
lean_dec_ref(v___y_5934_);
lean_dec(v___y_5933_);
lean_dec_ref(v___y_5932_);
lean_dec_ref(v_discrs_5929_);
return v_res_5939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5940_, size_t v_sz_5941_, size_t v_i_5942_, lean_object* v_b_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_, lean_object* v___y_5946_, lean_object* v___y_5947_){
_start:
{
lean_object* v_a_5950_; uint8_t v___x_5954_; 
v___x_5954_ = lean_usize_dec_lt(v_i_5942_, v_sz_5941_);
if (v___x_5954_ == 0)
{
lean_object* v___x_5955_; 
v___x_5955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5955_, 0, v_b_5943_);
return v___x_5955_;
}
else
{
lean_object* v_snd_5956_; lean_object* v_snd_5957_; lean_object* v_fst_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_6018_; 
v_snd_5956_ = lean_ctor_get(v_b_5943_, 1);
lean_inc(v_snd_5956_);
v_snd_5957_ = lean_ctor_get(v_snd_5956_, 1);
lean_inc(v_snd_5957_);
v_fst_5958_ = lean_ctor_get(v_b_5943_, 0);
v_isSharedCheck_6018_ = !lean_is_exclusive(v_b_5943_);
if (v_isSharedCheck_6018_ == 0)
{
lean_object* v_unused_6019_; 
v_unused_6019_ = lean_ctor_get(v_b_5943_, 1);
lean_dec(v_unused_6019_);
v___x_5960_ = v_b_5943_;
v_isShared_5961_ = v_isSharedCheck_6018_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_fst_5958_);
lean_dec(v_b_5943_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_6018_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v_fst_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_6016_; 
v_fst_5962_ = lean_ctor_get(v_snd_5956_, 0);
v_isSharedCheck_6016_ = !lean_is_exclusive(v_snd_5956_);
if (v_isSharedCheck_6016_ == 0)
{
lean_object* v_unused_6017_; 
v_unused_6017_ = lean_ctor_get(v_snd_5956_, 1);
lean_dec(v_unused_6017_);
v___x_5964_ = v_snd_5956_;
v_isShared_5965_ = v_isSharedCheck_6016_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_fst_5962_);
lean_dec(v_snd_5956_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_6016_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
lean_object* v_array_5966_; lean_object* v_start_5967_; lean_object* v_stop_5968_; uint8_t v___x_5969_; 
v_array_5966_ = lean_ctor_get(v_snd_5957_, 0);
v_start_5967_ = lean_ctor_get(v_snd_5957_, 1);
v_stop_5968_ = lean_ctor_get(v_snd_5957_, 2);
v___x_5969_ = lean_nat_dec_lt(v_start_5967_, v_stop_5968_);
if (v___x_5969_ == 0)
{
lean_object* v___x_5971_; 
if (v_isShared_5965_ == 0)
{
v___x_5971_ = v___x_5964_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v_fst_5962_);
lean_ctor_set(v_reuseFailAlloc_5976_, 1, v_snd_5957_);
v___x_5971_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
lean_object* v___x_5973_; 
if (v_isShared_5961_ == 0)
{
lean_ctor_set(v___x_5960_, 1, v___x_5971_);
v___x_5973_ = v___x_5960_;
goto v_reusejp_5972_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v_fst_5958_);
lean_ctor_set(v_reuseFailAlloc_5975_, 1, v___x_5971_);
v___x_5973_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5972_;
}
v_reusejp_5972_:
{
lean_object* v___x_5974_; 
v___x_5974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5973_);
return v___x_5974_;
}
}
}
else
{
lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_6012_; 
lean_inc(v_stop_5968_);
lean_inc(v_start_5967_);
lean_inc_ref(v_array_5966_);
v_isSharedCheck_6012_ = !lean_is_exclusive(v_snd_5957_);
if (v_isSharedCheck_6012_ == 0)
{
lean_object* v_unused_6013_; lean_object* v_unused_6014_; lean_object* v_unused_6015_; 
v_unused_6013_ = lean_ctor_get(v_snd_5957_, 2);
lean_dec(v_unused_6013_);
v_unused_6014_ = lean_ctor_get(v_snd_5957_, 1);
lean_dec(v_unused_6014_);
v_unused_6015_ = lean_ctor_get(v_snd_5957_, 0);
lean_dec(v_unused_6015_);
v___x_5978_ = v_snd_5957_;
v_isShared_5979_ = v_isSharedCheck_6012_;
goto v_resetjp_5977_;
}
else
{
lean_dec(v_snd_5957_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_6012_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5984_; 
v___x_5980_ = lean_array_fget(v_array_5966_, v_start_5967_);
v___x_5981_ = lean_unsigned_to_nat(1u);
v___x_5982_ = lean_nat_add(v_start_5967_, v___x_5981_);
lean_dec(v_start_5967_);
if (v_isShared_5979_ == 0)
{
lean_ctor_set(v___x_5978_, 1, v___x_5982_);
v___x_5984_ = v___x_5978_;
goto v_reusejp_5983_;
}
else
{
lean_object* v_reuseFailAlloc_6011_; 
v_reuseFailAlloc_6011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6011_, 0, v_array_5966_);
lean_ctor_set(v_reuseFailAlloc_6011_, 1, v___x_5982_);
lean_ctor_set(v_reuseFailAlloc_6011_, 2, v_stop_5968_);
v___x_5984_ = v_reuseFailAlloc_6011_;
goto v_reusejp_5983_;
}
v_reusejp_5983_:
{
lean_object* v___y_5986_; 
if (lean_obj_tag(v___x_5980_) == 0)
{
lean_object* v___x_6004_; lean_object* v___x_6005_; 
lean_del_object(v___x_5964_);
lean_del_object(v___x_5960_);
v___x_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6004_, 0, v_fst_5962_);
lean_ctor_set(v___x_6004_, 1, v___x_5984_);
v___x_6005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6005_, 0, v_fst_5958_);
lean_ctor_set(v___x_6005_, 1, v___x_6004_);
v_a_5950_ = v___x_6005_;
goto v___jp_5949_;
}
else
{
lean_object* v_val_6006_; lean_object* v_a_6007_; uint8_t v___x_6008_; 
v_val_6006_ = lean_ctor_get(v___x_5980_, 0);
lean_inc(v_val_6006_);
lean_dec_ref_known(v___x_5980_, 1);
v_a_6007_ = lean_array_uget_borrowed(v_as_5940_, v_i_5942_);
v___x_6008_ = lean_unbox(v_val_6006_);
lean_dec(v_val_6006_);
if (v___x_6008_ == 0)
{
lean_object* v___x_6009_; 
lean_inc(v_a_6007_);
v___x_6009_ = l_Lean_Meta_mkEqRefl(v_a_6007_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_);
v___y_5986_ = v___x_6009_;
goto v___jp_5985_;
}
else
{
lean_object* v___x_6010_; 
lean_inc(v_a_6007_);
v___x_6010_ = l_Lean_Meta_mkHEqRefl(v_a_6007_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_);
v___y_5986_ = v___x_6010_;
goto v___jp_5985_;
}
}
v___jp_5985_:
{
if (lean_obj_tag(v___y_5986_) == 0)
{
lean_object* v_a_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5991_; 
v_a_5987_ = lean_ctor_get(v___y_5986_, 0);
lean_inc(v_a_5987_);
lean_dec_ref_known(v___y_5986_, 1);
v___x_5988_ = lean_array_push(v_fst_5958_, v_a_5987_);
v___x_5989_ = lean_nat_add(v_fst_5962_, v___x_5981_);
lean_dec(v_fst_5962_);
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 1, v___x_5984_);
lean_ctor_set(v___x_5964_, 0, v___x_5989_);
v___x_5991_ = v___x_5964_;
goto v_reusejp_5990_;
}
else
{
lean_object* v_reuseFailAlloc_5995_; 
v_reuseFailAlloc_5995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5995_, 0, v___x_5989_);
lean_ctor_set(v_reuseFailAlloc_5995_, 1, v___x_5984_);
v___x_5991_ = v_reuseFailAlloc_5995_;
goto v_reusejp_5990_;
}
v_reusejp_5990_:
{
lean_object* v___x_5993_; 
if (v_isShared_5961_ == 0)
{
lean_ctor_set(v___x_5960_, 1, v___x_5991_);
lean_ctor_set(v___x_5960_, 0, v___x_5988_);
v___x_5993_ = v___x_5960_;
goto v_reusejp_5992_;
}
else
{
lean_object* v_reuseFailAlloc_5994_; 
v_reuseFailAlloc_5994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5994_, 0, v___x_5988_);
lean_ctor_set(v_reuseFailAlloc_5994_, 1, v___x_5991_);
v___x_5993_ = v_reuseFailAlloc_5994_;
goto v_reusejp_5992_;
}
v_reusejp_5992_:
{
v_a_5950_ = v___x_5993_;
goto v___jp_5949_;
}
}
}
else
{
lean_object* v_a_5996_; lean_object* v___x_5998_; uint8_t v_isShared_5999_; uint8_t v_isSharedCheck_6003_; 
lean_dec_ref(v___x_5984_);
lean_del_object(v___x_5964_);
lean_dec(v_fst_5962_);
lean_del_object(v___x_5960_);
lean_dec(v_fst_5958_);
v_a_5996_ = lean_ctor_get(v___y_5986_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v___y_5986_);
if (v_isSharedCheck_6003_ == 0)
{
v___x_5998_ = v___y_5986_;
v_isShared_5999_ = v_isSharedCheck_6003_;
goto v_resetjp_5997_;
}
else
{
lean_inc(v_a_5996_);
lean_dec(v___y_5986_);
v___x_5998_ = lean_box(0);
v_isShared_5999_ = v_isSharedCheck_6003_;
goto v_resetjp_5997_;
}
v_resetjp_5997_:
{
lean_object* v___x_6001_; 
if (v_isShared_5999_ == 0)
{
v___x_6001_ = v___x_5998_;
goto v_reusejp_6000_;
}
else
{
lean_object* v_reuseFailAlloc_6002_; 
v_reuseFailAlloc_6002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6002_, 0, v_a_5996_);
v___x_6001_ = v_reuseFailAlloc_6002_;
goto v_reusejp_6000_;
}
v_reusejp_6000_:
{
return v___x_6001_;
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
v___jp_5949_:
{
size_t v___x_5951_; size_t v___x_5952_; 
v___x_5951_ = ((size_t)1ULL);
v___x_5952_ = lean_usize_add(v_i_5942_, v___x_5951_);
v_i_5942_ = v___x_5952_;
v_b_5943_ = v_a_5950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6020_, lean_object* v_sz_6021_, lean_object* v_i_6022_, lean_object* v_b_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_){
_start:
{
size_t v_sz_boxed_6029_; size_t v_i_boxed_6030_; lean_object* v_res_6031_; 
v_sz_boxed_6029_ = lean_unbox_usize(v_sz_6021_);
lean_dec(v_sz_6021_);
v_i_boxed_6030_ = lean_unbox_usize(v_i_6022_);
lean_dec(v_i_6022_);
v_res_6031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6020_, v_sz_boxed_6029_, v_i_boxed_6030_, v_b_6023_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_);
lean_dec(v___y_6027_);
lean_dec_ref(v___y_6026_);
lean_dec(v___y_6025_);
lean_dec_ref(v___y_6024_);
lean_dec_ref(v_as_6020_);
return v_res_6031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_){
_start:
{
lean_object* v___x_6038_; 
v___x_6038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6032_);
return v___x_6038_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_){
_start:
{
lean_object* v_res_6045_; 
v_res_6045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_);
lean_dec(v___y_6043_);
lean_dec_ref(v___y_6042_);
lean_dec(v___y_6041_);
lean_dec_ref(v___y_6040_);
return v_res_6045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6046_, size_t v_i_6047_, lean_object* v_bs_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_){
_start:
{
uint8_t v___x_6053_; 
v___x_6053_ = lean_usize_dec_lt(v_i_6047_, v_sz_6046_);
if (v___x_6053_ == 0)
{
lean_object* v___x_6054_; 
v___x_6054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6054_, 0, v_bs_6048_);
return v___x_6054_;
}
else
{
lean_object* v_v_6055_; lean_object* v___x_6056_; lean_object* v_bs_x27_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; 
v_v_6055_ = lean_array_uget(v_bs_6048_, v_i_6047_);
v___x_6056_ = lean_unsigned_to_nat(0u);
v_bs_x27_6057_ = lean_array_uset(v_bs_6048_, v_i_6047_, v___x_6056_);
v___x_6058_ = l_Lean_Expr_fvarId_x21(v_v_6055_);
lean_dec(v_v_6055_);
v___x_6059_ = l_Lean_FVarId_getUserName___redArg(v___x_6058_, v___y_6049_, v___y_6050_, v___y_6051_);
if (lean_obj_tag(v___x_6059_) == 0)
{
lean_object* v_a_6060_; size_t v___x_6061_; size_t v___x_6062_; lean_object* v___x_6063_; 
v_a_6060_ = lean_ctor_get(v___x_6059_, 0);
lean_inc(v_a_6060_);
lean_dec_ref_known(v___x_6059_, 1);
v___x_6061_ = ((size_t)1ULL);
v___x_6062_ = lean_usize_add(v_i_6047_, v___x_6061_);
v___x_6063_ = lean_array_uset(v_bs_x27_6057_, v_i_6047_, v_a_6060_);
v_i_6047_ = v___x_6062_;
v_bs_6048_ = v___x_6063_;
goto _start;
}
else
{
lean_object* v_a_6065_; lean_object* v___x_6067_; uint8_t v_isShared_6068_; uint8_t v_isSharedCheck_6072_; 
lean_dec_ref(v_bs_x27_6057_);
v_a_6065_ = lean_ctor_get(v___x_6059_, 0);
v_isSharedCheck_6072_ = !lean_is_exclusive(v___x_6059_);
if (v_isSharedCheck_6072_ == 0)
{
v___x_6067_ = v___x_6059_;
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
else
{
lean_inc(v_a_6065_);
lean_dec(v___x_6059_);
v___x_6067_ = lean_box(0);
v_isShared_6068_ = v_isSharedCheck_6072_;
goto v_resetjp_6066_;
}
v_resetjp_6066_:
{
lean_object* v___x_6070_; 
if (v_isShared_6068_ == 0)
{
v___x_6070_ = v___x_6067_;
goto v_reusejp_6069_;
}
else
{
lean_object* v_reuseFailAlloc_6071_; 
v_reuseFailAlloc_6071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6071_, 0, v_a_6065_);
v___x_6070_ = v_reuseFailAlloc_6071_;
goto v_reusejp_6069_;
}
v_reusejp_6069_:
{
return v___x_6070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6073_, lean_object* v_i_6074_, lean_object* v_bs_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_){
_start:
{
size_t v_sz_boxed_6080_; size_t v_i_boxed_6081_; lean_object* v_res_6082_; 
v_sz_boxed_6080_ = lean_unbox_usize(v_sz_6073_);
lean_dec(v_sz_6073_);
v_i_boxed_6081_ = lean_unbox_usize(v_i_6074_);
lean_dec(v_i_6074_);
v_res_6082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6080_, v_i_boxed_6081_, v_bs_6075_, v___y_6076_, v___y_6077_, v___y_6078_);
lean_dec(v___y_6078_);
lean_dec_ref(v___y_6077_);
lean_dec_ref(v___y_6076_);
return v_res_6082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6083_, lean_object* v_x_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_){
_start:
{
size_t v_sz_6090_; size_t v___x_6091_; lean_object* v___x_6092_; 
v_sz_6090_ = lean_array_size(v_xs_6083_);
v___x_6091_ = ((size_t)0ULL);
v___x_6092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6090_, v___x_6091_, v_xs_6083_, v___y_6085_, v___y_6087_, v___y_6088_);
return v___x_6092_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6093_, lean_object* v_x_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_){
_start:
{
lean_object* v_res_6100_; 
v_res_6100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6093_, v_x_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
lean_dec(v___y_6098_);
lean_dec_ref(v___y_6097_);
lean_dec(v___y_6096_);
lean_dec_ref(v___y_6095_);
lean_dec_ref(v_x_6094_);
return v_res_6100_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6101_, lean_object* v___x_6102_, lean_object* v___f_6103_, uint8_t v___x_6104_, lean_object* v_fst_6105_, lean_object* v___x_6106_, lean_object* v___x_6107_, lean_object* v___x_6108_, lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_){
_start:
{
lean_object* v___x_6114_; 
v___x_6114_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v___x_6101_, v___x_6102_, v___f_6103_, v___x_6104_, v___x_6104_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_);
if (lean_obj_tag(v___x_6114_) == 0)
{
lean_object* v_a_6115_; lean_object* v___x_6117_; uint8_t v_isShared_6118_; uint8_t v_isSharedCheck_6127_; 
v_a_6115_ = lean_ctor_get(v___x_6114_, 0);
v_isSharedCheck_6127_ = !lean_is_exclusive(v___x_6114_);
if (v_isSharedCheck_6127_ == 0)
{
v___x_6117_ = v___x_6114_;
v_isShared_6118_ = v_isSharedCheck_6127_;
goto v_resetjp_6116_;
}
else
{
lean_inc(v_a_6115_);
lean_dec(v___x_6114_);
v___x_6117_ = lean_box(0);
v_isShared_6118_ = v_isSharedCheck_6127_;
goto v_resetjp_6116_;
}
v_resetjp_6116_:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6125_; 
v___x_6119_ = lean_array_push(v_fst_6105_, v_a_6115_);
v___x_6120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6106_);
lean_ctor_set(v___x_6120_, 1, v___x_6107_);
v___x_6121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6121_, 0, v___x_6108_);
lean_ctor_set(v___x_6121_, 1, v___x_6120_);
v___x_6122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6122_, 0, v___x_6119_);
lean_ctor_set(v___x_6122_, 1, v___x_6121_);
v___x_6123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6123_, 0, v___x_6122_);
if (v_isShared_6118_ == 0)
{
lean_ctor_set(v___x_6117_, 0, v___x_6123_);
v___x_6125_ = v___x_6117_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6126_; 
v_reuseFailAlloc_6126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6126_, 0, v___x_6123_);
v___x_6125_ = v_reuseFailAlloc_6126_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
return v___x_6125_;
}
}
}
else
{
lean_object* v_a_6128_; lean_object* v___x_6130_; uint8_t v_isShared_6131_; uint8_t v_isSharedCheck_6135_; 
lean_dec_ref(v___x_6108_);
lean_dec_ref(v___x_6107_);
lean_dec_ref(v___x_6106_);
lean_dec(v_fst_6105_);
v_a_6128_ = lean_ctor_get(v___x_6114_, 0);
v_isSharedCheck_6135_ = !lean_is_exclusive(v___x_6114_);
if (v_isSharedCheck_6135_ == 0)
{
v___x_6130_ = v___x_6114_;
v_isShared_6131_ = v_isSharedCheck_6135_;
goto v_resetjp_6129_;
}
else
{
lean_inc(v_a_6128_);
lean_dec(v___x_6114_);
v___x_6130_ = lean_box(0);
v_isShared_6131_ = v_isSharedCheck_6135_;
goto v_resetjp_6129_;
}
v_resetjp_6129_:
{
lean_object* v___x_6133_; 
if (v_isShared_6131_ == 0)
{
v___x_6133_ = v___x_6130_;
goto v_reusejp_6132_;
}
else
{
lean_object* v_reuseFailAlloc_6134_; 
v_reuseFailAlloc_6134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6134_, 0, v_a_6128_);
v___x_6133_ = v_reuseFailAlloc_6134_;
goto v_reusejp_6132_;
}
v_reusejp_6132_:
{
return v___x_6133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6136_, lean_object* v___x_6137_, lean_object* v___f_6138_, lean_object* v___x_6139_, lean_object* v_fst_6140_, lean_object* v___x_6141_, lean_object* v___x_6142_, lean_object* v___x_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_){
_start:
{
uint8_t v___x_35062__boxed_6149_; lean_object* v_res_6150_; 
v___x_35062__boxed_6149_ = lean_unbox(v___x_6139_);
v_res_6150_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6136_, v___x_6137_, v___f_6138_, v___x_35062__boxed_6149_, v_fst_6140_, v___x_6141_, v___x_6142_, v___x_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
return v_res_6150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6151_, lean_object* v_names_6152_, lean_object* v_k_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
lean_object* v___x_6159_; 
v___x_6159_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6151_, v_names_6152_, v_k_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
if (lean_obj_tag(v___x_6159_) == 0)
{
lean_object* v_a_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6167_; 
v_a_6160_ = lean_ctor_get(v___x_6159_, 0);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_6159_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6162_ = v___x_6159_;
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
else
{
lean_inc(v_a_6160_);
lean_dec(v___x_6159_);
v___x_6162_ = lean_box(0);
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
v_resetjp_6161_:
{
lean_object* v___x_6165_; 
if (v_isShared_6163_ == 0)
{
v___x_6165_ = v___x_6162_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
else
{
lean_object* v_a_6168_; lean_object* v___x_6170_; uint8_t v_isShared_6171_; uint8_t v_isSharedCheck_6175_; 
v_a_6168_ = lean_ctor_get(v___x_6159_, 0);
v_isSharedCheck_6175_ = !lean_is_exclusive(v___x_6159_);
if (v_isSharedCheck_6175_ == 0)
{
v___x_6170_ = v___x_6159_;
v_isShared_6171_ = v_isSharedCheck_6175_;
goto v_resetjp_6169_;
}
else
{
lean_inc(v_a_6168_);
lean_dec(v___x_6159_);
v___x_6170_ = lean_box(0);
v_isShared_6171_ = v_isSharedCheck_6175_;
goto v_resetjp_6169_;
}
v_resetjp_6169_:
{
lean_object* v___x_6173_; 
if (v_isShared_6171_ == 0)
{
v___x_6173_ = v___x_6170_;
goto v_reusejp_6172_;
}
else
{
lean_object* v_reuseFailAlloc_6174_; 
v_reuseFailAlloc_6174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6174_, 0, v_a_6168_);
v___x_6173_ = v_reuseFailAlloc_6174_;
goto v_reusejp_6172_;
}
v_reusejp_6172_:
{
return v___x_6173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6176_, lean_object* v_names_6177_, lean_object* v_k_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_){
_start:
{
lean_object* v_res_6184_; 
v_res_6184_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6176_, v_names_6177_, v_k_6178_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
lean_dec(v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec_ref(v_names_6177_);
lean_dec_ref(v_fvars_6176_);
return v_res_6184_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6185_, lean_object* v_xs_6186_, lean_object* v_remaining_x27_6187_, lean_object* v_ys4_6188_, lean_object* v_onAlt_6189_, lean_object* v_a_6190_, lean_object* v_altType_6191_, uint8_t v___x_6192_, uint8_t v___x_6193_, lean_object* v___y_6194_, lean_object* v___y_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_){
_start:
{
lean_object* v___x_6199_; 
v___x_6199_ = l_Lean_Meta_instantiateLambda(v___x_6185_, v_xs_6186_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_);
if (lean_obj_tag(v___x_6199_) == 0)
{
lean_object* v_a_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
v_a_6200_ = lean_ctor_get(v___x_6199_, 0);
lean_inc(v_a_6200_);
lean_dec_ref_known(v___x_6199_, 1);
lean_inc_ref(v_ys4_6188_);
lean_inc_ref(v_remaining_x27_6187_);
lean_inc_ref_n(v_xs_6186_, 2);
v___x_6201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6201_, 0, v_xs_6186_);
lean_ctor_set(v___x_6201_, 1, v_xs_6186_);
lean_ctor_set(v___x_6201_, 2, v_remaining_x27_6187_);
lean_ctor_set(v___x_6201_, 3, v_remaining_x27_6187_);
lean_ctor_set(v___x_6201_, 4, v_ys4_6188_);
lean_inc(v___y_6197_);
lean_inc_ref(v___y_6196_);
lean_inc(v___y_6195_);
lean_inc_ref(v___y_6194_);
v___x_6202_ = lean_apply_9(v_onAlt_6189_, v_a_6190_, v_altType_6191_, v___x_6201_, v_a_6200_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_, lean_box(0));
if (lean_obj_tag(v___x_6202_) == 0)
{
lean_object* v_a_6203_; lean_object* v___x_6204_; uint8_t v___x_6205_; lean_object* v___x_6206_; 
v_a_6203_ = lean_ctor_get(v___x_6202_, 0);
lean_inc(v_a_6203_);
lean_dec_ref_known(v___x_6202_, 1);
v___x_6204_ = l_Array_append___redArg(v_xs_6186_, v_ys4_6188_);
lean_dec_ref(v_ys4_6188_);
v___x_6205_ = 1;
v___x_6206_ = l_Lean_Meta_mkLambdaFVars(v___x_6204_, v_a_6203_, v___x_6192_, v___x_6193_, v___x_6192_, v___x_6193_, v___x_6205_, v___y_6194_, v___y_6195_, v___y_6196_, v___y_6197_);
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec_ref(v___x_6204_);
return v___x_6206_;
}
else
{
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec_ref(v_ys4_6188_);
lean_dec_ref(v_xs_6186_);
return v___x_6202_;
}
}
else
{
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec(v___y_6195_);
lean_dec_ref(v___y_6194_);
lean_dec_ref(v_altType_6191_);
lean_dec(v_a_6190_);
lean_dec_ref(v_onAlt_6189_);
lean_dec_ref(v_ys4_6188_);
lean_dec_ref(v_remaining_x27_6187_);
lean_dec_ref(v_xs_6186_);
return v___x_6199_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6207_, lean_object* v_xs_6208_, lean_object* v_remaining_x27_6209_, lean_object* v_ys4_6210_, lean_object* v_onAlt_6211_, lean_object* v_a_6212_, lean_object* v_altType_6213_, lean_object* v___x_6214_, lean_object* v___x_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_){
_start:
{
uint8_t v___x_35189__boxed_6221_; uint8_t v___x_35190__boxed_6222_; lean_object* v_res_6223_; 
v___x_35189__boxed_6221_ = lean_unbox(v___x_6214_);
v___x_35190__boxed_6222_ = lean_unbox(v___x_6215_);
v_res_6223_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6207_, v_xs_6208_, v_remaining_x27_6209_, v_ys4_6210_, v_onAlt_6211_, v_a_6212_, v_altType_6213_, v___x_35189__boxed_6221_, v___x_35190__boxed_6222_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_);
return v_res_6223_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6224_, lean_object* v_xs_6225_, lean_object* v_remaining_x27_6226_, lean_object* v_onAlt_6227_, lean_object* v_a_6228_, uint8_t v___x_6229_, uint8_t v___x_6230_, lean_object* v___f_6231_, lean_object* v_ys4_6232_, lean_object* v_altType_6233_, lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_){
_start:
{
lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___f_6241_; lean_object* v___x_6242_; 
v___x_6239_ = lean_box(v___x_6229_);
v___x_6240_ = lean_box(v___x_6230_);
lean_inc_ref(v_xs_6225_);
lean_inc_ref(v___x_6224_);
v___f_6241_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6241_, 0, v___x_6224_);
lean_closure_set(v___f_6241_, 1, v_xs_6225_);
lean_closure_set(v___f_6241_, 2, v_remaining_x27_6226_);
lean_closure_set(v___f_6241_, 3, v_ys4_6232_);
lean_closure_set(v___f_6241_, 4, v_onAlt_6227_);
lean_closure_set(v___f_6241_, 5, v_a_6228_);
lean_closure_set(v___f_6241_, 6, v_altType_6233_);
lean_closure_set(v___f_6241_, 7, v___x_6239_);
lean_closure_set(v___f_6241_, 8, v___x_6240_);
v___x_6242_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6224_, v___f_6231_, v___x_6229_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
if (lean_obj_tag(v___x_6242_) == 0)
{
lean_object* v_a_6243_; lean_object* v___x_6244_; 
v_a_6243_ = lean_ctor_get(v___x_6242_, 0);
lean_inc(v_a_6243_);
lean_dec_ref_known(v___x_6242_, 1);
v___x_6244_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6225_, v_a_6243_, v___f_6241_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_);
lean_dec(v_a_6243_);
lean_dec_ref(v_xs_6225_);
return v___x_6244_;
}
else
{
lean_object* v_a_6245_; lean_object* v___x_6247_; uint8_t v_isShared_6248_; uint8_t v_isSharedCheck_6252_; 
lean_dec_ref(v___f_6241_);
lean_dec_ref(v_xs_6225_);
v_a_6245_ = lean_ctor_get(v___x_6242_, 0);
v_isSharedCheck_6252_ = !lean_is_exclusive(v___x_6242_);
if (v_isSharedCheck_6252_ == 0)
{
v___x_6247_ = v___x_6242_;
v_isShared_6248_ = v_isSharedCheck_6252_;
goto v_resetjp_6246_;
}
else
{
lean_inc(v_a_6245_);
lean_dec(v___x_6242_);
v___x_6247_ = lean_box(0);
v_isShared_6248_ = v_isSharedCheck_6252_;
goto v_resetjp_6246_;
}
v_resetjp_6246_:
{
lean_object* v___x_6250_; 
if (v_isShared_6248_ == 0)
{
v___x_6250_ = v___x_6247_;
goto v_reusejp_6249_;
}
else
{
lean_object* v_reuseFailAlloc_6251_; 
v_reuseFailAlloc_6251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6251_, 0, v_a_6245_);
v___x_6250_ = v_reuseFailAlloc_6251_;
goto v_reusejp_6249_;
}
v_reusejp_6249_:
{
return v___x_6250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6253_, lean_object* v_xs_6254_, lean_object* v_remaining_x27_6255_, lean_object* v_onAlt_6256_, lean_object* v_a_6257_, lean_object* v___x_6258_, lean_object* v___x_6259_, lean_object* v___f_6260_, lean_object* v_ys4_6261_, lean_object* v_altType_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_){
_start:
{
uint8_t v___x_35231__boxed_6268_; uint8_t v___x_35232__boxed_6269_; lean_object* v_res_6270_; 
v___x_35231__boxed_6268_ = lean_unbox(v___x_6258_);
v___x_35232__boxed_6269_ = lean_unbox(v___x_6259_);
v_res_6270_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6253_, v_xs_6254_, v_remaining_x27_6255_, v_onAlt_6256_, v_a_6257_, v___x_35231__boxed_6268_, v___x_35232__boxed_6269_, v___f_6260_, v_ys4_6261_, v_altType_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
lean_dec(v___y_6264_);
lean_dec_ref(v___y_6263_);
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6271_, lean_object* v_remaining_x27_6272_, lean_object* v_onAlt_6273_, lean_object* v_a_6274_, uint8_t v___x_6275_, uint8_t v___x_6276_, lean_object* v___f_6277_, lean_object* v_extraEqualities_6278_, lean_object* v_xs_6279_, lean_object* v_altType_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_, lean_object* v___y_6284_){
_start:
{
lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___f_6288_; lean_object* v___x_6289_; lean_object* v___x_6290_; 
v___x_6286_ = lean_box(v___x_6275_);
v___x_6287_ = lean_box(v___x_6276_);
v___f_6288_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6288_, 0, v___x_6271_);
lean_closure_set(v___f_6288_, 1, v_xs_6279_);
lean_closure_set(v___f_6288_, 2, v_remaining_x27_6272_);
lean_closure_set(v___f_6288_, 3, v_onAlt_6273_);
lean_closure_set(v___f_6288_, 4, v_a_6274_);
lean_closure_set(v___f_6288_, 5, v___x_6286_);
lean_closure_set(v___f_6288_, 6, v___x_6287_);
lean_closure_set(v___f_6288_, 7, v___f_6277_);
v___x_6289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6289_, 0, v_extraEqualities_6278_);
v___x_6290_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_6280_, v___x_6289_, v___f_6288_, v___x_6275_, v___x_6275_, v___y_6281_, v___y_6282_, v___y_6283_, v___y_6284_);
return v___x_6290_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6291_, lean_object* v_remaining_x27_6292_, lean_object* v_onAlt_6293_, lean_object* v_a_6294_, lean_object* v___x_6295_, lean_object* v___x_6296_, lean_object* v___f_6297_, lean_object* v_extraEqualities_6298_, lean_object* v_xs_6299_, lean_object* v_altType_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_){
_start:
{
uint8_t v___x_35286__boxed_6306_; uint8_t v___x_35287__boxed_6307_; lean_object* v_res_6308_; 
v___x_35286__boxed_6306_ = lean_unbox(v___x_6295_);
v___x_35287__boxed_6307_ = lean_unbox(v___x_6296_);
v_res_6308_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6291_, v_remaining_x27_6292_, v_onAlt_6293_, v_a_6294_, v___x_35286__boxed_6306_, v___x_35287__boxed_6307_, v___f_6297_, v_extraEqualities_6298_, v_xs_6299_, v_altType_6300_, v___y_6301_, v___y_6302_, v___y_6303_, v___y_6304_);
lean_dec(v___y_6304_);
lean_dec_ref(v___y_6303_);
lean_dec(v___y_6302_);
lean_dec_ref(v___y_6301_);
return v_res_6308_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6310_, lean_object* v_onAlt_6311_, lean_object* v_extraEqualities_6312_, lean_object* v_a_6313_, lean_object* v_b_6314_, lean_object* v___y_6315_, lean_object* v___y_6316_, lean_object* v___y_6317_, lean_object* v___y_6318_){
_start:
{
lean_object* v___y_6321_; uint8_t v___x_6344_; 
v___x_6344_ = lean_nat_dec_lt(v_a_6313_, v_upperBound_6310_);
if (v___x_6344_ == 0)
{
lean_object* v___x_6345_; 
lean_dec(v_a_6313_);
lean_dec(v_extraEqualities_6312_);
lean_dec_ref(v_onAlt_6311_);
v___x_6345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6345_, 0, v_b_6314_);
return v___x_6345_;
}
else
{
lean_object* v_snd_6346_; lean_object* v_snd_6347_; lean_object* v_snd_6348_; lean_object* v_fst_6349_; lean_object* v___x_6351_; uint8_t v_isShared_6352_; uint8_t v_isSharedCheck_6456_; 
v_snd_6346_ = lean_ctor_get(v_b_6314_, 1);
lean_inc(v_snd_6346_);
v_snd_6347_ = lean_ctor_get(v_snd_6346_, 1);
lean_inc(v_snd_6347_);
v_snd_6348_ = lean_ctor_get(v_snd_6347_, 1);
lean_inc(v_snd_6348_);
v_fst_6349_ = lean_ctor_get(v_b_6314_, 0);
v_isSharedCheck_6456_ = !lean_is_exclusive(v_b_6314_);
if (v_isSharedCheck_6456_ == 0)
{
lean_object* v_unused_6457_; 
v_unused_6457_ = lean_ctor_get(v_b_6314_, 1);
lean_dec(v_unused_6457_);
v___x_6351_ = v_b_6314_;
v_isShared_6352_ = v_isSharedCheck_6456_;
goto v_resetjp_6350_;
}
else
{
lean_inc(v_fst_6349_);
lean_dec(v_b_6314_);
v___x_6351_ = lean_box(0);
v_isShared_6352_ = v_isSharedCheck_6456_;
goto v_resetjp_6350_;
}
v_resetjp_6350_:
{
lean_object* v_fst_6353_; lean_object* v___x_6355_; uint8_t v_isShared_6356_; uint8_t v_isSharedCheck_6454_; 
v_fst_6353_ = lean_ctor_get(v_snd_6346_, 0);
v_isSharedCheck_6454_ = !lean_is_exclusive(v_snd_6346_);
if (v_isSharedCheck_6454_ == 0)
{
lean_object* v_unused_6455_; 
v_unused_6455_ = lean_ctor_get(v_snd_6346_, 1);
lean_dec(v_unused_6455_);
v___x_6355_ = v_snd_6346_;
v_isShared_6356_ = v_isSharedCheck_6454_;
goto v_resetjp_6354_;
}
else
{
lean_inc(v_fst_6353_);
lean_dec(v_snd_6346_);
v___x_6355_ = lean_box(0);
v_isShared_6356_ = v_isSharedCheck_6454_;
goto v_resetjp_6354_;
}
v_resetjp_6354_:
{
lean_object* v_fst_6357_; lean_object* v___x_6359_; uint8_t v_isShared_6360_; uint8_t v_isSharedCheck_6452_; 
v_fst_6357_ = lean_ctor_get(v_snd_6347_, 0);
v_isSharedCheck_6452_ = !lean_is_exclusive(v_snd_6347_);
if (v_isSharedCheck_6452_ == 0)
{
lean_object* v_unused_6453_; 
v_unused_6453_ = lean_ctor_get(v_snd_6347_, 1);
lean_dec(v_unused_6453_);
v___x_6359_ = v_snd_6347_;
v_isShared_6360_ = v_isSharedCheck_6452_;
goto v_resetjp_6358_;
}
else
{
lean_inc(v_fst_6357_);
lean_dec(v_snd_6347_);
v___x_6359_ = lean_box(0);
v_isShared_6360_ = v_isSharedCheck_6452_;
goto v_resetjp_6358_;
}
v_resetjp_6358_:
{
lean_object* v_array_6361_; lean_object* v_start_6362_; lean_object* v_stop_6363_; uint8_t v___x_6364_; 
v_array_6361_ = lean_ctor_get(v_snd_6348_, 0);
v_start_6362_ = lean_ctor_get(v_snd_6348_, 1);
v_stop_6363_ = lean_ctor_get(v_snd_6348_, 2);
v___x_6364_ = lean_nat_dec_lt(v_start_6362_, v_stop_6363_);
if (v___x_6364_ == 0)
{
lean_object* v___x_6366_; 
if (v_isShared_6360_ == 0)
{
v___x_6366_ = v___x_6359_;
goto v_reusejp_6365_;
}
else
{
lean_object* v_reuseFailAlloc_6375_; 
v_reuseFailAlloc_6375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6375_, 0, v_fst_6357_);
lean_ctor_set(v_reuseFailAlloc_6375_, 1, v_snd_6348_);
v___x_6366_ = v_reuseFailAlloc_6375_;
goto v_reusejp_6365_;
}
v_reusejp_6365_:
{
lean_object* v___x_6368_; 
if (v_isShared_6356_ == 0)
{
lean_ctor_set(v___x_6355_, 1, v___x_6366_);
v___x_6368_ = v___x_6355_;
goto v_reusejp_6367_;
}
else
{
lean_object* v_reuseFailAlloc_6374_; 
v_reuseFailAlloc_6374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6374_, 0, v_fst_6353_);
lean_ctor_set(v_reuseFailAlloc_6374_, 1, v___x_6366_);
v___x_6368_ = v_reuseFailAlloc_6374_;
goto v_reusejp_6367_;
}
v_reusejp_6367_:
{
lean_object* v___x_6370_; 
if (v_isShared_6352_ == 0)
{
lean_ctor_set(v___x_6351_, 1, v___x_6368_);
v___x_6370_ = v___x_6351_;
goto v_reusejp_6369_;
}
else
{
lean_object* v_reuseFailAlloc_6373_; 
v_reuseFailAlloc_6373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6373_, 0, v_fst_6349_);
lean_ctor_set(v_reuseFailAlloc_6373_, 1, v___x_6368_);
v___x_6370_ = v_reuseFailAlloc_6373_;
goto v_reusejp_6369_;
}
v_reusejp_6369_:
{
lean_object* v___x_6371_; lean_object* v___f_6372_; 
v___x_6371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6371_, 0, v___x_6370_);
v___f_6372_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6372_, 0, v___x_6371_);
v___y_6321_ = v___f_6372_;
goto v___jp_6320_;
}
}
}
}
else
{
lean_object* v___x_6377_; uint8_t v_isShared_6378_; uint8_t v_isSharedCheck_6448_; 
lean_inc(v_stop_6363_);
lean_inc(v_start_6362_);
lean_inc_ref(v_array_6361_);
v_isSharedCheck_6448_ = !lean_is_exclusive(v_snd_6348_);
if (v_isSharedCheck_6448_ == 0)
{
lean_object* v_unused_6449_; lean_object* v_unused_6450_; lean_object* v_unused_6451_; 
v_unused_6449_ = lean_ctor_get(v_snd_6348_, 2);
lean_dec(v_unused_6449_);
v_unused_6450_ = lean_ctor_get(v_snd_6348_, 1);
lean_dec(v_unused_6450_);
v_unused_6451_ = lean_ctor_get(v_snd_6348_, 0);
lean_dec(v_unused_6451_);
v___x_6377_ = v_snd_6348_;
v_isShared_6378_ = v_isSharedCheck_6448_;
goto v_resetjp_6376_;
}
else
{
lean_dec(v_snd_6348_);
v___x_6377_ = lean_box(0);
v_isShared_6378_ = v_isSharedCheck_6448_;
goto v_resetjp_6376_;
}
v_resetjp_6376_:
{
lean_object* v_array_6379_; lean_object* v_start_6380_; lean_object* v_stop_6381_; lean_object* v___x_6382_; lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6386_; 
v_array_6379_ = lean_ctor_get(v_fst_6357_, 0);
v_start_6380_ = lean_ctor_get(v_fst_6357_, 1);
v_stop_6381_ = lean_ctor_get(v_fst_6357_, 2);
v___x_6382_ = lean_array_fget(v_array_6361_, v_start_6362_);
v___x_6383_ = lean_unsigned_to_nat(1u);
v___x_6384_ = lean_nat_add(v_start_6362_, v___x_6383_);
lean_dec(v_start_6362_);
if (v_isShared_6378_ == 0)
{
lean_ctor_set(v___x_6377_, 1, v___x_6384_);
v___x_6386_ = v___x_6377_;
goto v_reusejp_6385_;
}
else
{
lean_object* v_reuseFailAlloc_6447_; 
v_reuseFailAlloc_6447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_array_6361_);
lean_ctor_set(v_reuseFailAlloc_6447_, 1, v___x_6384_);
lean_ctor_set(v_reuseFailAlloc_6447_, 2, v_stop_6363_);
v___x_6386_ = v_reuseFailAlloc_6447_;
goto v_reusejp_6385_;
}
v_reusejp_6385_:
{
uint8_t v___x_6387_; 
v___x_6387_ = lean_nat_dec_lt(v_start_6380_, v_stop_6381_);
if (v___x_6387_ == 0)
{
lean_object* v___x_6389_; 
lean_dec(v___x_6382_);
if (v_isShared_6360_ == 0)
{
lean_ctor_set(v___x_6359_, 1, v___x_6386_);
v___x_6389_ = v___x_6359_;
goto v_reusejp_6388_;
}
else
{
lean_object* v_reuseFailAlloc_6398_; 
v_reuseFailAlloc_6398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6398_, 0, v_fst_6357_);
lean_ctor_set(v_reuseFailAlloc_6398_, 1, v___x_6386_);
v___x_6389_ = v_reuseFailAlloc_6398_;
goto v_reusejp_6388_;
}
v_reusejp_6388_:
{
lean_object* v___x_6391_; 
if (v_isShared_6356_ == 0)
{
lean_ctor_set(v___x_6355_, 1, v___x_6389_);
v___x_6391_ = v___x_6355_;
goto v_reusejp_6390_;
}
else
{
lean_object* v_reuseFailAlloc_6397_; 
v_reuseFailAlloc_6397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_fst_6353_);
lean_ctor_set(v_reuseFailAlloc_6397_, 1, v___x_6389_);
v___x_6391_ = v_reuseFailAlloc_6397_;
goto v_reusejp_6390_;
}
v_reusejp_6390_:
{
lean_object* v___x_6393_; 
if (v_isShared_6352_ == 0)
{
lean_ctor_set(v___x_6351_, 1, v___x_6391_);
v___x_6393_ = v___x_6351_;
goto v_reusejp_6392_;
}
else
{
lean_object* v_reuseFailAlloc_6396_; 
v_reuseFailAlloc_6396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6396_, 0, v_fst_6349_);
lean_ctor_set(v_reuseFailAlloc_6396_, 1, v___x_6391_);
v___x_6393_ = v_reuseFailAlloc_6396_;
goto v_reusejp_6392_;
}
v_reusejp_6392_:
{
lean_object* v___x_6394_; lean_object* v___f_6395_; 
v___x_6394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6394_, 0, v___x_6393_);
v___f_6395_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6395_, 0, v___x_6394_);
v___y_6321_ = v___f_6395_;
goto v___jp_6320_;
}
}
}
}
else
{
lean_object* v___x_6400_; uint8_t v_isShared_6401_; uint8_t v_isSharedCheck_6443_; 
lean_inc(v_stop_6381_);
lean_inc(v_start_6380_);
lean_inc_ref(v_array_6379_);
v_isSharedCheck_6443_ = !lean_is_exclusive(v_fst_6357_);
if (v_isSharedCheck_6443_ == 0)
{
lean_object* v_unused_6444_; lean_object* v_unused_6445_; lean_object* v_unused_6446_; 
v_unused_6444_ = lean_ctor_get(v_fst_6357_, 2);
lean_dec(v_unused_6444_);
v_unused_6445_ = lean_ctor_get(v_fst_6357_, 1);
lean_dec(v_unused_6445_);
v_unused_6446_ = lean_ctor_get(v_fst_6357_, 0);
lean_dec(v_unused_6446_);
v___x_6400_ = v_fst_6357_;
v_isShared_6401_ = v_isSharedCheck_6443_;
goto v_resetjp_6399_;
}
else
{
lean_dec(v_fst_6357_);
v___x_6400_ = lean_box(0);
v_isShared_6401_ = v_isSharedCheck_6443_;
goto v_resetjp_6399_;
}
v_resetjp_6399_:
{
lean_object* v_array_6402_; lean_object* v_start_6403_; lean_object* v_stop_6404_; lean_object* v___x_6405_; lean_object* v___x_6406_; lean_object* v___x_6408_; 
v_array_6402_ = lean_ctor_get(v_fst_6353_, 0);
v_start_6403_ = lean_ctor_get(v_fst_6353_, 1);
v_stop_6404_ = lean_ctor_get(v_fst_6353_, 2);
v___x_6405_ = lean_array_fget(v_array_6379_, v_start_6380_);
v___x_6406_ = lean_nat_add(v_start_6380_, v___x_6383_);
lean_dec(v_start_6380_);
if (v_isShared_6401_ == 0)
{
lean_ctor_set(v___x_6400_, 1, v___x_6406_);
v___x_6408_ = v___x_6400_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6442_; 
v_reuseFailAlloc_6442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6442_, 0, v_array_6379_);
lean_ctor_set(v_reuseFailAlloc_6442_, 1, v___x_6406_);
lean_ctor_set(v_reuseFailAlloc_6442_, 2, v_stop_6381_);
v___x_6408_ = v_reuseFailAlloc_6442_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
uint8_t v___x_6409_; 
v___x_6409_ = lean_nat_dec_lt(v_start_6403_, v_stop_6404_);
if (v___x_6409_ == 0)
{
lean_object* v___x_6411_; 
lean_dec(v___x_6405_);
lean_dec(v___x_6382_);
if (v_isShared_6360_ == 0)
{
lean_ctor_set(v___x_6359_, 1, v___x_6386_);
lean_ctor_set(v___x_6359_, 0, v___x_6408_);
v___x_6411_ = v___x_6359_;
goto v_reusejp_6410_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v___x_6408_);
lean_ctor_set(v_reuseFailAlloc_6420_, 1, v___x_6386_);
v___x_6411_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6410_;
}
v_reusejp_6410_:
{
lean_object* v___x_6413_; 
if (v_isShared_6356_ == 0)
{
lean_ctor_set(v___x_6355_, 1, v___x_6411_);
v___x_6413_ = v___x_6355_;
goto v_reusejp_6412_;
}
else
{
lean_object* v_reuseFailAlloc_6419_; 
v_reuseFailAlloc_6419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6419_, 0, v_fst_6353_);
lean_ctor_set(v_reuseFailAlloc_6419_, 1, v___x_6411_);
v___x_6413_ = v_reuseFailAlloc_6419_;
goto v_reusejp_6412_;
}
v_reusejp_6412_:
{
lean_object* v___x_6415_; 
if (v_isShared_6352_ == 0)
{
lean_ctor_set(v___x_6351_, 1, v___x_6413_);
v___x_6415_ = v___x_6351_;
goto v_reusejp_6414_;
}
else
{
lean_object* v_reuseFailAlloc_6418_; 
v_reuseFailAlloc_6418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6418_, 0, v_fst_6349_);
lean_ctor_set(v_reuseFailAlloc_6418_, 1, v___x_6413_);
v___x_6415_ = v_reuseFailAlloc_6418_;
goto v_reusejp_6414_;
}
v_reusejp_6414_:
{
lean_object* v___x_6416_; lean_object* v___f_6417_; 
v___x_6416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6416_, 0, v___x_6415_);
v___f_6417_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6417_, 0, v___x_6416_);
v___y_6321_ = v___f_6417_;
goto v___jp_6320_;
}
}
}
}
else
{
lean_object* v___x_6422_; uint8_t v_isShared_6423_; uint8_t v_isSharedCheck_6438_; 
lean_inc(v_stop_6404_);
lean_inc(v_start_6403_);
lean_inc_ref(v_array_6402_);
lean_del_object(v___x_6359_);
lean_del_object(v___x_6355_);
lean_del_object(v___x_6351_);
v_isSharedCheck_6438_ = !lean_is_exclusive(v_fst_6353_);
if (v_isSharedCheck_6438_ == 0)
{
lean_object* v_unused_6439_; lean_object* v_unused_6440_; lean_object* v_unused_6441_; 
v_unused_6439_ = lean_ctor_get(v_fst_6353_, 2);
lean_dec(v_unused_6439_);
v_unused_6440_ = lean_ctor_get(v_fst_6353_, 1);
lean_dec(v_unused_6440_);
v_unused_6441_ = lean_ctor_get(v_fst_6353_, 0);
lean_dec(v_unused_6441_);
v___x_6422_ = v_fst_6353_;
v_isShared_6423_ = v_isSharedCheck_6438_;
goto v_resetjp_6421_;
}
else
{
lean_dec(v_fst_6353_);
v___x_6422_ = lean_box(0);
v_isShared_6423_ = v_isSharedCheck_6438_;
goto v_resetjp_6421_;
}
v_resetjp_6421_:
{
lean_object* v___f_6424_; uint8_t v___x_6425_; lean_object* v_remaining_x27_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; lean_object* v___f_6430_; lean_object* v___x_6431_; lean_object* v___x_6433_; 
v___f_6424_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6425_ = 0;
v_remaining_x27_6426_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6427_ = lean_array_fget_borrowed(v_array_6402_, v_start_6403_);
v___x_6428_ = lean_box(v___x_6425_);
v___x_6429_ = lean_box(v___x_6409_);
lean_inc(v_extraEqualities_6312_);
lean_inc(v_a_6313_);
lean_inc_ref(v_onAlt_6311_);
lean_inc(v___x_6427_);
v___f_6430_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6430_, 0, v___x_6427_);
lean_closure_set(v___f_6430_, 1, v_remaining_x27_6426_);
lean_closure_set(v___f_6430_, 2, v_onAlt_6311_);
lean_closure_set(v___f_6430_, 3, v_a_6313_);
lean_closure_set(v___f_6430_, 4, v___x_6428_);
lean_closure_set(v___f_6430_, 5, v___x_6429_);
lean_closure_set(v___f_6430_, 6, v___f_6424_);
lean_closure_set(v___f_6430_, 7, v_extraEqualities_6312_);
v___x_6431_ = lean_nat_add(v_start_6403_, v___x_6383_);
lean_dec(v_start_6403_);
if (v_isShared_6423_ == 0)
{
lean_ctor_set(v___x_6422_, 1, v___x_6431_);
v___x_6433_ = v___x_6422_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6437_; 
v_reuseFailAlloc_6437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6437_, 0, v_array_6402_);
lean_ctor_set(v_reuseFailAlloc_6437_, 1, v___x_6431_);
lean_ctor_set(v_reuseFailAlloc_6437_, 2, v_stop_6404_);
v___x_6433_ = v_reuseFailAlloc_6437_;
goto v_reusejp_6432_;
}
v_reusejp_6432_:
{
lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___f_6436_; 
v___x_6434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6434_, 0, v___x_6405_);
v___x_6435_ = lean_box(v___x_6425_);
v___f_6436_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6436_, 0, v___x_6382_);
lean_closure_set(v___f_6436_, 1, v___x_6434_);
lean_closure_set(v___f_6436_, 2, v___f_6430_);
lean_closure_set(v___f_6436_, 3, v___x_6435_);
lean_closure_set(v___f_6436_, 4, v_fst_6349_);
lean_closure_set(v___f_6436_, 5, v___x_6408_);
lean_closure_set(v___f_6436_, 6, v___x_6386_);
lean_closure_set(v___f_6436_, 7, v___x_6433_);
v___y_6321_ = v___f_6436_;
goto v___jp_6320_;
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
v___jp_6320_:
{
lean_object* v___x_6322_; 
lean_inc(v___y_6318_);
lean_inc_ref(v___y_6317_);
lean_inc(v___y_6316_);
lean_inc_ref(v___y_6315_);
v___x_6322_ = lean_apply_5(v___y_6321_, v___y_6315_, v___y_6316_, v___y_6317_, v___y_6318_, lean_box(0));
if (lean_obj_tag(v___x_6322_) == 0)
{
lean_object* v_a_6323_; lean_object* v___x_6325_; uint8_t v_isShared_6326_; uint8_t v_isSharedCheck_6335_; 
v_a_6323_ = lean_ctor_get(v___x_6322_, 0);
v_isSharedCheck_6335_ = !lean_is_exclusive(v___x_6322_);
if (v_isSharedCheck_6335_ == 0)
{
v___x_6325_ = v___x_6322_;
v_isShared_6326_ = v_isSharedCheck_6335_;
goto v_resetjp_6324_;
}
else
{
lean_inc(v_a_6323_);
lean_dec(v___x_6322_);
v___x_6325_ = lean_box(0);
v_isShared_6326_ = v_isSharedCheck_6335_;
goto v_resetjp_6324_;
}
v_resetjp_6324_:
{
if (lean_obj_tag(v_a_6323_) == 0)
{
lean_object* v_a_6327_; lean_object* v___x_6329_; 
lean_dec(v_a_6313_);
lean_dec(v_extraEqualities_6312_);
lean_dec_ref(v_onAlt_6311_);
v_a_6327_ = lean_ctor_get(v_a_6323_, 0);
lean_inc(v_a_6327_);
lean_dec_ref_known(v_a_6323_, 1);
if (v_isShared_6326_ == 0)
{
lean_ctor_set(v___x_6325_, 0, v_a_6327_);
v___x_6329_ = v___x_6325_;
goto v_reusejp_6328_;
}
else
{
lean_object* v_reuseFailAlloc_6330_; 
v_reuseFailAlloc_6330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6330_, 0, v_a_6327_);
v___x_6329_ = v_reuseFailAlloc_6330_;
goto v_reusejp_6328_;
}
v_reusejp_6328_:
{
return v___x_6329_;
}
}
else
{
lean_object* v_a_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; 
lean_del_object(v___x_6325_);
v_a_6331_ = lean_ctor_get(v_a_6323_, 0);
lean_inc(v_a_6331_);
lean_dec_ref_known(v_a_6323_, 1);
v___x_6332_ = lean_unsigned_to_nat(1u);
v___x_6333_ = lean_nat_add(v_a_6313_, v___x_6332_);
lean_dec(v_a_6313_);
v_a_6313_ = v___x_6333_;
v_b_6314_ = v_a_6331_;
goto _start;
}
}
}
else
{
lean_object* v_a_6336_; lean_object* v___x_6338_; uint8_t v_isShared_6339_; uint8_t v_isSharedCheck_6343_; 
lean_dec(v_a_6313_);
lean_dec(v_extraEqualities_6312_);
lean_dec_ref(v_onAlt_6311_);
v_a_6336_ = lean_ctor_get(v___x_6322_, 0);
v_isSharedCheck_6343_ = !lean_is_exclusive(v___x_6322_);
if (v_isSharedCheck_6343_ == 0)
{
v___x_6338_ = v___x_6322_;
v_isShared_6339_ = v_isSharedCheck_6343_;
goto v_resetjp_6337_;
}
else
{
lean_inc(v_a_6336_);
lean_dec(v___x_6322_);
v___x_6338_ = lean_box(0);
v_isShared_6339_ = v_isSharedCheck_6343_;
goto v_resetjp_6337_;
}
v_resetjp_6337_:
{
lean_object* v___x_6341_; 
if (v_isShared_6339_ == 0)
{
v___x_6341_ = v___x_6338_;
goto v_reusejp_6340_;
}
else
{
lean_object* v_reuseFailAlloc_6342_; 
v_reuseFailAlloc_6342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6342_, 0, v_a_6336_);
v___x_6341_ = v_reuseFailAlloc_6342_;
goto v_reusejp_6340_;
}
v_reusejp_6340_:
{
return v___x_6341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6458_, lean_object* v_onAlt_6459_, lean_object* v_extraEqualities_6460_, lean_object* v_a_6461_, lean_object* v_b_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_, lean_object* v___y_6465_, lean_object* v___y_6466_, lean_object* v___y_6467_){
_start:
{
lean_object* v_res_6468_; 
v_res_6468_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6458_, v_onAlt_6459_, v_extraEqualities_6460_, v_a_6461_, v_b_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
lean_dec(v___y_6466_);
lean_dec_ref(v___y_6465_);
lean_dec(v___y_6464_);
lean_dec_ref(v___y_6463_);
lean_dec(v_upperBound_6458_);
return v_res_6468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6469_, size_t v_sz_6470_, size_t v_i_6471_, lean_object* v_bs_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_){
_start:
{
uint8_t v___x_6478_; 
v___x_6478_ = lean_usize_dec_lt(v_i_6471_, v_sz_6470_);
if (v___x_6478_ == 0)
{
lean_object* v___x_6479_; 
lean_dec_ref(v_onParams_6469_);
v___x_6479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6479_, 0, v_bs_6472_);
return v___x_6479_;
}
else
{
lean_object* v_v_6480_; lean_object* v___x_6481_; lean_object* v_bs_x27_6482_; lean_object* v___x_6483_; 
v_v_6480_ = lean_array_uget(v_bs_6472_, v_i_6471_);
v___x_6481_ = lean_unsigned_to_nat(0u);
v_bs_x27_6482_ = lean_array_uset(v_bs_6472_, v_i_6471_, v___x_6481_);
lean_inc_ref(v_onParams_6469_);
lean_inc(v___y_6476_);
lean_inc_ref(v___y_6475_);
lean_inc(v___y_6474_);
lean_inc_ref(v___y_6473_);
v___x_6483_ = lean_apply_6(v_onParams_6469_, v_v_6480_, v___y_6473_, v___y_6474_, v___y_6475_, v___y_6476_, lean_box(0));
if (lean_obj_tag(v___x_6483_) == 0)
{
lean_object* v_a_6484_; size_t v___x_6485_; size_t v___x_6486_; lean_object* v___x_6487_; 
v_a_6484_ = lean_ctor_get(v___x_6483_, 0);
lean_inc(v_a_6484_);
lean_dec_ref_known(v___x_6483_, 1);
v___x_6485_ = ((size_t)1ULL);
v___x_6486_ = lean_usize_add(v_i_6471_, v___x_6485_);
v___x_6487_ = lean_array_uset(v_bs_x27_6482_, v_i_6471_, v_a_6484_);
v_i_6471_ = v___x_6486_;
v_bs_6472_ = v___x_6487_;
goto _start;
}
else
{
lean_object* v_a_6489_; lean_object* v___x_6491_; uint8_t v_isShared_6492_; uint8_t v_isSharedCheck_6496_; 
lean_dec_ref(v_bs_x27_6482_);
lean_dec_ref(v_onParams_6469_);
v_a_6489_ = lean_ctor_get(v___x_6483_, 0);
v_isSharedCheck_6496_ = !lean_is_exclusive(v___x_6483_);
if (v_isSharedCheck_6496_ == 0)
{
v___x_6491_ = v___x_6483_;
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
else
{
lean_inc(v_a_6489_);
lean_dec(v___x_6483_);
v___x_6491_ = lean_box(0);
v_isShared_6492_ = v_isSharedCheck_6496_;
goto v_resetjp_6490_;
}
v_resetjp_6490_:
{
lean_object* v___x_6494_; 
if (v_isShared_6492_ == 0)
{
v___x_6494_ = v___x_6491_;
goto v_reusejp_6493_;
}
else
{
lean_object* v_reuseFailAlloc_6495_; 
v_reuseFailAlloc_6495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_a_6489_);
v___x_6494_ = v_reuseFailAlloc_6495_;
goto v_reusejp_6493_;
}
v_reusejp_6493_:
{
return v___x_6494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6497_, lean_object* v_sz_6498_, lean_object* v_i_6499_, lean_object* v_bs_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_){
_start:
{
size_t v_sz_boxed_6506_; size_t v_i_boxed_6507_; lean_object* v_res_6508_; 
v_sz_boxed_6506_ = lean_unbox_usize(v_sz_6498_);
lean_dec(v_sz_6498_);
v_i_boxed_6507_ = lean_unbox_usize(v_i_6499_);
lean_dec(v_i_6499_);
v_res_6508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6497_, v_sz_boxed_6506_, v_i_boxed_6507_, v_bs_6500_, v___y_6501_, v___y_6502_, v___y_6503_, v___y_6504_);
lean_dec(v___y_6504_);
lean_dec_ref(v___y_6503_);
lean_dec(v___y_6502_);
lean_dec_ref(v___y_6501_);
return v_res_6508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6509_, lean_object* v___y_6510_){
_start:
{
lean_object* v___x_6512_; lean_object* v_env_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; 
v___x_6512_ = lean_st_ref_get(v___y_6510_);
v_env_6513_ = lean_ctor_get(v___x_6512_, 0);
lean_inc_ref(v_env_6513_);
lean_dec(v___x_6512_);
v___x_6514_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6513_, v_declName_6509_);
v___x_6515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6515_, 0, v___x_6514_);
return v___x_6515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_){
_start:
{
lean_object* v_res_6519_; 
v_res_6519_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6516_, v___y_6517_);
lean_dec(v___y_6517_);
return v_res_6519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6522_, uint8_t v_useSplitter_6523_, uint8_t v_addEqualities_6524_, lean_object* v_onParams_6525_, lean_object* v_onMotive_6526_, lean_object* v_onAlt_6527_, lean_object* v_onRemaining_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_, lean_object* v___y_6532_){
_start:
{
lean_object* v___x_6534_; lean_object* v_env_6535_; lean_object* v_toMatcherInfo_6536_; lean_object* v_matcherName_6537_; lean_object* v_matcherLevels_6538_; lean_object* v_params_6539_; lean_object* v_motive_6540_; lean_object* v_discrs_6541_; lean_object* v_alts_6542_; lean_object* v_remaining_6543_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; lean_object* v___y_6548_; lean_object* v___y_6549_; lean_object* v___y_6550_; lean_object* v___y_6551_; lean_object* v___y_6552_; lean_object* v___y_6553_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; uint8_t v_isCasesOn_6642_; lean_object* v___y_6644_; lean_object* v___y_6645_; size_t v___y_6646_; lean_object* v___y_6647_; lean_object* v___y_6648_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v_matcherLevels_6651_; lean_object* v___y_6652_; lean_object* v___y_6653_; lean_object* v___y_6654_; lean_object* v___y_6655_; lean_object* v_numDiscrEqs_6849_; lean_object* v___y_6850_; lean_object* v___y_6851_; lean_object* v___y_6852_; lean_object* v___y_6853_; 
v___x_6534_ = lean_st_ref_get(v___y_6532_);
v_env_6535_ = lean_ctor_get(v___x_6534_, 0);
lean_inc_ref(v_env_6535_);
lean_dec(v___x_6534_);
v_toMatcherInfo_6536_ = lean_ctor_get(v_matcherApp_6522_, 0);
lean_inc_ref(v_toMatcherInfo_6536_);
v_matcherName_6537_ = lean_ctor_get(v_matcherApp_6522_, 1);
lean_inc_n(v_matcherName_6537_, 2);
v_matcherLevels_6538_ = lean_ctor_get(v_matcherApp_6522_, 2);
v_params_6539_ = lean_ctor_get(v_matcherApp_6522_, 3);
v_motive_6540_ = lean_ctor_get(v_matcherApp_6522_, 4);
v_discrs_6541_ = lean_ctor_get(v_matcherApp_6522_, 5);
v_alts_6542_ = lean_ctor_get(v_matcherApp_6522_, 6);
lean_inc_ref(v_alts_6542_);
v_remaining_6543_ = lean_ctor_get(v_matcherApp_6522_, 7);
lean_inc_ref(v_remaining_6543_);
v_isCasesOn_6642_ = l_Lean_isCasesOnRecursor(v_env_6535_, v_matcherName_6537_);
if (v_isCasesOn_6642_ == 0)
{
lean_object* v___x_6903_; lean_object* v_a_6904_; 
lean_inc(v_matcherName_6537_);
v___x_6903_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6537_, v___y_6532_);
v_a_6904_ = lean_ctor_get(v___x_6903_, 0);
lean_inc(v_a_6904_);
lean_dec_ref(v___x_6903_);
if (lean_obj_tag(v_a_6904_) == 0)
{
lean_object* v___x_6905_; lean_object* v___x_6906_; lean_object* v___x_6907_; lean_object* v___x_6908_; lean_object* v___x_6909_; lean_object* v___x_6910_; lean_object* v_a_6911_; lean_object* v___x_6913_; uint8_t v_isShared_6914_; uint8_t v_isSharedCheck_6918_; 
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
lean_dec_ref(v_onMotive_6526_);
lean_dec_ref(v_onParams_6525_);
lean_dec_ref(v_matcherApp_6522_);
v___x_6905_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6906_ = l_Lean_MessageData_ofName(v_matcherName_6537_);
v___x_6907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6907_, 0, v___x_6905_);
lean_ctor_set(v___x_6907_, 1, v___x_6906_);
v___x_6908_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6909_, 0, v___x_6907_);
lean_ctor_set(v___x_6909_, 1, v___x_6908_);
v___x_6910_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6909_, v___y_6529_, v___y_6530_, v___y_6531_, v___y_6532_);
v_a_6911_ = lean_ctor_get(v___x_6910_, 0);
v_isSharedCheck_6918_ = !lean_is_exclusive(v___x_6910_);
if (v_isSharedCheck_6918_ == 0)
{
v___x_6913_ = v___x_6910_;
v_isShared_6914_ = v_isSharedCheck_6918_;
goto v_resetjp_6912_;
}
else
{
lean_inc(v_a_6911_);
lean_dec(v___x_6910_);
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
else
{
lean_object* v_val_6919_; lean_object* v___x_6920_; 
v_val_6919_ = lean_ctor_get(v_a_6904_, 0);
lean_inc(v_val_6919_);
lean_dec_ref_known(v_a_6904_, 1);
v___x_6920_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6919_);
lean_dec(v_val_6919_);
v_numDiscrEqs_6849_ = v___x_6920_;
v___y_6850_ = v___y_6529_;
v___y_6851_ = v___y_6530_;
v___y_6852_ = v___y_6531_;
v___y_6853_ = v___y_6532_;
goto v___jp_6848_;
}
}
else
{
lean_object* v___x_6921_; 
v___x_6921_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6849_ = v___x_6921_;
v___y_6850_ = v___y_6529_;
v___y_6851_ = v___y_6530_;
v___y_6852_ = v___y_6531_;
v___y_6853_ = v___y_6532_;
goto v___jp_6848_;
}
v___jp_6544_:
{
lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v_aux_6560_; lean_object* v_aux_6561_; lean_object* v_aux_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___f_6566_; uint8_t v___x_6567_; lean_object* v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; 
lean_inc_ref(v___y_6547_);
v___x_6558_ = lean_array_to_list(v___y_6547_);
lean_inc(v_matcherName_6537_);
v___x_6559_ = l_Lean_mkConst(v_matcherName_6537_, v___x_6558_);
v_aux_6560_ = l_Lean_mkAppN(v___x_6559_, v___y_6556_);
lean_inc_ref(v___y_6550_);
v_aux_6561_ = l_Lean_Expr_app___override(v_aux_6560_, v___y_6550_);
v_aux_6562_ = l_Lean_mkAppN(v_aux_6561_, v___y_6545_);
v___x_6563_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6562_, 2);
v___x_6564_ = l_Lean_indentExpr(v_aux_6562_);
v___x_6565_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6565_, 0, v___x_6563_);
lean_ctor_set(v___x_6565_, 1, v___x_6564_);
v___f_6566_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6566_, 0, v___x_6565_);
v___x_6567_ = 0;
v___x_6568_ = lean_box(v___x_6567_);
v___x_6569_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6569_, 0, v_aux_6562_);
lean_closure_set(v___x_6569_, 1, v___x_6568_);
v___x_6570_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6569_, v___f_6566_, v___y_6551_, v___y_6555_, v___y_6552_, v___y_6548_);
if (lean_obj_tag(v___x_6570_) == 0)
{
lean_object* v___x_6571_; lean_object* v___x_6572_; 
lean_dec_ref_known(v___x_6570_, 1);
v___x_6571_ = lean_array_get_size(v_alts_6542_);
v___x_6572_ = l_Lean_Meta_inferArgumentTypesN(v___x_6571_, v_aux_6562_, v___y_6551_, v___y_6555_, v___y_6552_, v___y_6548_);
if (lean_obj_tag(v___x_6572_) == 0)
{
lean_object* v_a_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; lean_object* v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; 
v_a_6573_ = lean_ctor_get(v___x_6572_, 0);
lean_inc(v_a_6573_);
lean_dec_ref_known(v___x_6572_, 1);
v___x_6574_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6522_);
v___x_6575_ = lean_array_get_size(v___x_6574_);
v___x_6576_ = lean_array_get_size(v_a_6573_);
lean_inc_n(v___y_6554_, 3);
v___x_6577_ = l_Array_toSubarray___redArg(v_alts_6542_, v___y_6554_, v___x_6571_);
v___x_6578_ = l_Array_toSubarray___redArg(v___x_6574_, v___y_6554_, v___x_6575_);
v___x_6579_ = l_Array_toSubarray___redArg(v_a_6573_, v___y_6554_, v___x_6576_);
v___x_6580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6580_, 0, v___x_6578_);
lean_ctor_set(v___x_6580_, 1, v___x_6579_);
v___x_6581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6581_, 0, v___x_6577_);
lean_ctor_set(v___x_6581_, 1, v___x_6580_);
lean_inc_ref(v___y_6549_);
v___x_6582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6582_, 0, v___y_6549_);
lean_ctor_set(v___x_6582_, 1, v___x_6581_);
v___x_6583_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6571_, v_onAlt_6527_, v___y_6557_, v___y_6554_, v___x_6582_, v___y_6551_, v___y_6555_, v___y_6552_, v___y_6548_);
if (lean_obj_tag(v___x_6583_) == 0)
{
lean_object* v_a_6584_; lean_object* v_fst_6585_; lean_object* v___x_6586_; 
v_a_6584_ = lean_ctor_get(v___x_6583_, 0);
lean_inc(v_a_6584_);
lean_dec_ref_known(v___x_6583_, 1);
v_fst_6585_ = lean_ctor_get(v_a_6584_, 0);
lean_inc(v_fst_6585_);
lean_dec(v_a_6584_);
lean_inc(v___y_6548_);
lean_inc_ref(v___y_6552_);
lean_inc(v___y_6555_);
lean_inc_ref(v___y_6551_);
v___x_6586_ = lean_apply_6(v_onRemaining_6528_, v_remaining_6543_, v___y_6551_, v___y_6555_, v___y_6552_, v___y_6548_, lean_box(0));
if (lean_obj_tag(v___x_6586_) == 0)
{
lean_object* v_a_6587_; lean_object* v___x_6589_; uint8_t v_isShared_6590_; uint8_t v_isSharedCheck_6609_; 
v_a_6587_ = lean_ctor_get(v___x_6586_, 0);
v_isSharedCheck_6609_ = !lean_is_exclusive(v___x_6586_);
if (v_isSharedCheck_6609_ == 0)
{
v___x_6589_ = v___x_6586_;
v_isShared_6590_ = v_isSharedCheck_6609_;
goto v_resetjp_6588_;
}
else
{
lean_inc(v_a_6587_);
lean_dec(v___x_6586_);
v___x_6589_ = lean_box(0);
v_isShared_6590_ = v_isSharedCheck_6609_;
goto v_resetjp_6588_;
}
v_resetjp_6588_:
{
lean_object* v_numParams_6591_; lean_object* v_numDiscrs_6592_; lean_object* v_altInfos_6593_; lean_object* v_uElimPos_x3f_6594_; lean_object* v_overlaps_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6607_; 
v_numParams_6591_ = lean_ctor_get(v_toMatcherInfo_6536_, 0);
v_numDiscrs_6592_ = lean_ctor_get(v_toMatcherInfo_6536_, 1);
v_altInfos_6593_ = lean_ctor_get(v_toMatcherInfo_6536_, 2);
v_uElimPos_x3f_6594_ = lean_ctor_get(v_toMatcherInfo_6536_, 3);
v_overlaps_6595_ = lean_ctor_get(v_toMatcherInfo_6536_, 5);
v_isSharedCheck_6607_ = !lean_is_exclusive(v_toMatcherInfo_6536_);
if (v_isSharedCheck_6607_ == 0)
{
lean_object* v_unused_6608_; 
v_unused_6608_ = lean_ctor_get(v_toMatcherInfo_6536_, 4);
lean_dec(v_unused_6608_);
v___x_6597_ = v_toMatcherInfo_6536_;
v_isShared_6598_ = v_isSharedCheck_6607_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_overlaps_6595_);
lean_inc(v_uElimPos_x3f_6594_);
lean_inc(v_altInfos_6593_);
lean_inc(v_numDiscrs_6592_);
lean_inc(v_numParams_6591_);
lean_dec(v_toMatcherInfo_6536_);
v___x_6597_ = lean_box(0);
v_isShared_6598_ = v_isSharedCheck_6607_;
goto v_resetjp_6596_;
}
v_resetjp_6596_:
{
lean_object* v_remaining_x27_6599_; lean_object* v___x_6601_; 
v_remaining_x27_6599_ = l_Array_append___redArg(v___y_6546_, v_a_6587_);
lean_dec(v_a_6587_);
if (v_isShared_6598_ == 0)
{
lean_ctor_set(v___x_6597_, 4, v___y_6553_);
v___x_6601_ = v___x_6597_;
goto v_reusejp_6600_;
}
else
{
lean_object* v_reuseFailAlloc_6606_; 
v_reuseFailAlloc_6606_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6606_, 0, v_numParams_6591_);
lean_ctor_set(v_reuseFailAlloc_6606_, 1, v_numDiscrs_6592_);
lean_ctor_set(v_reuseFailAlloc_6606_, 2, v_altInfos_6593_);
lean_ctor_set(v_reuseFailAlloc_6606_, 3, v_uElimPos_x3f_6594_);
lean_ctor_set(v_reuseFailAlloc_6606_, 4, v___y_6553_);
lean_ctor_set(v_reuseFailAlloc_6606_, 5, v_overlaps_6595_);
v___x_6601_ = v_reuseFailAlloc_6606_;
goto v_reusejp_6600_;
}
v_reusejp_6600_:
{
lean_object* v___x_6602_; lean_object* v___x_6604_; 
v___x_6602_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6602_, 0, v___x_6601_);
lean_ctor_set(v___x_6602_, 1, v_matcherName_6537_);
lean_ctor_set(v___x_6602_, 2, v___y_6547_);
lean_ctor_set(v___x_6602_, 3, v___y_6556_);
lean_ctor_set(v___x_6602_, 4, v___y_6550_);
lean_ctor_set(v___x_6602_, 5, v___y_6545_);
lean_ctor_set(v___x_6602_, 6, v_fst_6585_);
lean_ctor_set(v___x_6602_, 7, v_remaining_x27_6599_);
if (v_isShared_6590_ == 0)
{
lean_ctor_set(v___x_6589_, 0, v___x_6602_);
v___x_6604_ = v___x_6589_;
goto v_reusejp_6603_;
}
else
{
lean_object* v_reuseFailAlloc_6605_; 
v_reuseFailAlloc_6605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6605_, 0, v___x_6602_);
v___x_6604_ = v_reuseFailAlloc_6605_;
goto v_reusejp_6603_;
}
v_reusejp_6603_:
{
return v___x_6604_;
}
}
}
}
}
else
{
lean_object* v_a_6610_; lean_object* v___x_6612_; uint8_t v_isShared_6613_; uint8_t v_isSharedCheck_6617_; 
lean_dec(v_fst_6585_);
lean_dec_ref(v___y_6556_);
lean_dec_ref(v___y_6553_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6547_);
lean_dec(v___y_6546_);
lean_dec_ref(v___y_6545_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
v_a_6610_ = lean_ctor_get(v___x_6586_, 0);
v_isSharedCheck_6617_ = !lean_is_exclusive(v___x_6586_);
if (v_isSharedCheck_6617_ == 0)
{
v___x_6612_ = v___x_6586_;
v_isShared_6613_ = v_isSharedCheck_6617_;
goto v_resetjp_6611_;
}
else
{
lean_inc(v_a_6610_);
lean_dec(v___x_6586_);
v___x_6612_ = lean_box(0);
v_isShared_6613_ = v_isSharedCheck_6617_;
goto v_resetjp_6611_;
}
v_resetjp_6611_:
{
lean_object* v___x_6615_; 
if (v_isShared_6613_ == 0)
{
v___x_6615_ = v___x_6612_;
goto v_reusejp_6614_;
}
else
{
lean_object* v_reuseFailAlloc_6616_; 
v_reuseFailAlloc_6616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6616_, 0, v_a_6610_);
v___x_6615_ = v_reuseFailAlloc_6616_;
goto v_reusejp_6614_;
}
v_reusejp_6614_:
{
return v___x_6615_;
}
}
}
}
else
{
lean_object* v_a_6618_; lean_object* v___x_6620_; uint8_t v_isShared_6621_; uint8_t v_isSharedCheck_6625_; 
lean_dec_ref(v___y_6556_);
lean_dec_ref(v___y_6553_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6547_);
lean_dec(v___y_6546_);
lean_dec_ref(v___y_6545_);
lean_dec_ref(v_remaining_6543_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
v_a_6618_ = lean_ctor_get(v___x_6583_, 0);
v_isSharedCheck_6625_ = !lean_is_exclusive(v___x_6583_);
if (v_isSharedCheck_6625_ == 0)
{
v___x_6620_ = v___x_6583_;
v_isShared_6621_ = v_isSharedCheck_6625_;
goto v_resetjp_6619_;
}
else
{
lean_inc(v_a_6618_);
lean_dec(v___x_6583_);
v___x_6620_ = lean_box(0);
v_isShared_6621_ = v_isSharedCheck_6625_;
goto v_resetjp_6619_;
}
v_resetjp_6619_:
{
lean_object* v___x_6623_; 
if (v_isShared_6621_ == 0)
{
v___x_6623_ = v___x_6620_;
goto v_reusejp_6622_;
}
else
{
lean_object* v_reuseFailAlloc_6624_; 
v_reuseFailAlloc_6624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6624_, 0, v_a_6618_);
v___x_6623_ = v_reuseFailAlloc_6624_;
goto v_reusejp_6622_;
}
v_reusejp_6622_:
{
return v___x_6623_;
}
}
}
}
else
{
lean_object* v_a_6626_; lean_object* v___x_6628_; uint8_t v_isShared_6629_; uint8_t v_isSharedCheck_6633_; 
lean_dec(v___y_6557_);
lean_dec_ref(v___y_6556_);
lean_dec(v___y_6554_);
lean_dec_ref(v___y_6553_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6547_);
lean_dec(v___y_6546_);
lean_dec_ref(v___y_6545_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
lean_dec_ref(v_matcherApp_6522_);
v_a_6626_ = lean_ctor_get(v___x_6572_, 0);
v_isSharedCheck_6633_ = !lean_is_exclusive(v___x_6572_);
if (v_isSharedCheck_6633_ == 0)
{
v___x_6628_ = v___x_6572_;
v_isShared_6629_ = v_isSharedCheck_6633_;
goto v_resetjp_6627_;
}
else
{
lean_inc(v_a_6626_);
lean_dec(v___x_6572_);
v___x_6628_ = lean_box(0);
v_isShared_6629_ = v_isSharedCheck_6633_;
goto v_resetjp_6627_;
}
v_resetjp_6627_:
{
lean_object* v___x_6631_; 
if (v_isShared_6629_ == 0)
{
v___x_6631_ = v___x_6628_;
goto v_reusejp_6630_;
}
else
{
lean_object* v_reuseFailAlloc_6632_; 
v_reuseFailAlloc_6632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6632_, 0, v_a_6626_);
v___x_6631_ = v_reuseFailAlloc_6632_;
goto v_reusejp_6630_;
}
v_reusejp_6630_:
{
return v___x_6631_;
}
}
}
}
else
{
lean_object* v_a_6634_; lean_object* v___x_6636_; uint8_t v_isShared_6637_; uint8_t v_isSharedCheck_6641_; 
lean_dec_ref(v_aux_6562_);
lean_dec(v___y_6557_);
lean_dec_ref(v___y_6556_);
lean_dec(v___y_6554_);
lean_dec_ref(v___y_6553_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6547_);
lean_dec(v___y_6546_);
lean_dec_ref(v___y_6545_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
lean_dec_ref(v_matcherApp_6522_);
v_a_6634_ = lean_ctor_get(v___x_6570_, 0);
v_isSharedCheck_6641_ = !lean_is_exclusive(v___x_6570_);
if (v_isSharedCheck_6641_ == 0)
{
v___x_6636_ = v___x_6570_;
v_isShared_6637_ = v_isSharedCheck_6641_;
goto v_resetjp_6635_;
}
else
{
lean_inc(v_a_6634_);
lean_dec(v___x_6570_);
v___x_6636_ = lean_box(0);
v_isShared_6637_ = v_isSharedCheck_6641_;
goto v_resetjp_6635_;
}
v_resetjp_6635_:
{
lean_object* v___x_6639_; 
if (v_isShared_6637_ == 0)
{
v___x_6639_ = v___x_6636_;
goto v_reusejp_6638_;
}
else
{
lean_object* v_reuseFailAlloc_6640_; 
v_reuseFailAlloc_6640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6640_, 0, v_a_6634_);
v___x_6639_ = v_reuseFailAlloc_6640_;
goto v_reusejp_6638_;
}
v_reusejp_6638_:
{
return v___x_6639_;
}
}
}
}
v___jp_6643_:
{
lean_object* v___x_6656_; lean_object* v_remaining_x27_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; lean_object* v___x_6661_; lean_object* v___x_6662_; lean_object* v___x_6663_; size_t v_sz_6664_; lean_object* v___x_6665_; 
v___x_6656_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6657_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6658_ = l_Array_reverse___redArg(v___y_6644_);
v___x_6659_ = lean_array_get_size(v___x_6658_);
v___x_6660_ = l_Array_toSubarray___redArg(v___x_6658_, v___x_6656_, v___x_6659_);
lean_inc_ref(v___y_6647_);
v___x_6661_ = l_Array_reverse___redArg(v___y_6647_);
v___x_6662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6662_, 0, v___x_6656_);
lean_ctor_set(v___x_6662_, 1, v___x_6660_);
v___x_6663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6663_, 0, v_remaining_x27_6657_);
lean_ctor_set(v___x_6663_, 1, v___x_6662_);
v_sz_6664_ = lean_array_size(v___x_6661_);
v___x_6665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6661_, v_sz_6664_, v___y_6646_, v___x_6663_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
lean_dec_ref(v___x_6661_);
if (lean_obj_tag(v___x_6665_) == 0)
{
lean_object* v_a_6666_; lean_object* v_snd_6667_; 
v_a_6666_ = lean_ctor_get(v___x_6665_, 0);
lean_inc(v_a_6666_);
lean_dec_ref_known(v___x_6665_, 1);
v_snd_6667_ = lean_ctor_get(v_a_6666_, 1);
lean_inc(v_snd_6667_);
if (v_useSplitter_6523_ == 0)
{
lean_object* v_fst_6668_; lean_object* v_fst_6669_; 
lean_dec(v___y_6650_);
v_fst_6668_ = lean_ctor_get(v_a_6666_, 0);
lean_inc(v_fst_6668_);
lean_dec(v_a_6666_);
v_fst_6669_ = lean_ctor_get(v_snd_6667_, 0);
lean_inc(v_fst_6669_);
lean_dec(v_snd_6667_);
v___y_6545_ = v___y_6647_;
v___y_6546_ = v_fst_6668_;
v___y_6547_ = v_matcherLevels_6651_;
v___y_6548_ = v___y_6655_;
v___y_6549_ = v_remaining_x27_6657_;
v___y_6550_ = v___y_6648_;
v___y_6551_ = v___y_6652_;
v___y_6552_ = v___y_6654_;
v___y_6553_ = v___y_6645_;
v___y_6554_ = v___x_6656_;
v___y_6555_ = v___y_6653_;
v___y_6556_ = v___y_6649_;
v___y_6557_ = v_fst_6669_;
goto v___jp_6544_;
}
else
{
if (v_isCasesOn_6642_ == 0)
{
lean_object* v___x_6671_; uint8_t v_isShared_6672_; uint8_t v_isSharedCheck_6829_; 
v_isSharedCheck_6829_ = !lean_is_exclusive(v_matcherApp_6522_);
if (v_isSharedCheck_6829_ == 0)
{
lean_object* v_unused_6830_; lean_object* v_unused_6831_; lean_object* v_unused_6832_; lean_object* v_unused_6833_; lean_object* v_unused_6834_; lean_object* v_unused_6835_; lean_object* v_unused_6836_; lean_object* v_unused_6837_; 
v_unused_6830_ = lean_ctor_get(v_matcherApp_6522_, 7);
lean_dec(v_unused_6830_);
v_unused_6831_ = lean_ctor_get(v_matcherApp_6522_, 6);
lean_dec(v_unused_6831_);
v_unused_6832_ = lean_ctor_get(v_matcherApp_6522_, 5);
lean_dec(v_unused_6832_);
v_unused_6833_ = lean_ctor_get(v_matcherApp_6522_, 4);
lean_dec(v_unused_6833_);
v_unused_6834_ = lean_ctor_get(v_matcherApp_6522_, 3);
lean_dec(v_unused_6834_);
v_unused_6835_ = lean_ctor_get(v_matcherApp_6522_, 2);
lean_dec(v_unused_6835_);
v_unused_6836_ = lean_ctor_get(v_matcherApp_6522_, 1);
lean_dec(v_unused_6836_);
v_unused_6837_ = lean_ctor_get(v_matcherApp_6522_, 0);
lean_dec(v_unused_6837_);
v___x_6671_ = v_matcherApp_6522_;
v_isShared_6672_ = v_isSharedCheck_6829_;
goto v_resetjp_6670_;
}
else
{
lean_dec(v_matcherApp_6522_);
v___x_6671_ = lean_box(0);
v_isShared_6672_ = v_isSharedCheck_6829_;
goto v_resetjp_6670_;
}
v_resetjp_6670_:
{
lean_object* v_fst_6673_; lean_object* v___x_6675_; uint8_t v_isShared_6676_; uint8_t v_isSharedCheck_6827_; 
v_fst_6673_ = lean_ctor_get(v_a_6666_, 0);
v_isSharedCheck_6827_ = !lean_is_exclusive(v_a_6666_);
if (v_isSharedCheck_6827_ == 0)
{
lean_object* v_unused_6828_; 
v_unused_6828_ = lean_ctor_get(v_a_6666_, 1);
lean_dec(v_unused_6828_);
v___x_6675_ = v_a_6666_;
v_isShared_6676_ = v_isSharedCheck_6827_;
goto v_resetjp_6674_;
}
else
{
lean_inc(v_fst_6673_);
lean_dec(v_a_6666_);
v___x_6675_ = lean_box(0);
v_isShared_6676_ = v_isSharedCheck_6827_;
goto v_resetjp_6674_;
}
v_resetjp_6674_:
{
lean_object* v_fst_6677_; lean_object* v___x_6679_; uint8_t v_isShared_6680_; uint8_t v_isSharedCheck_6825_; 
v_fst_6677_ = lean_ctor_get(v_snd_6667_, 0);
v_isSharedCheck_6825_ = !lean_is_exclusive(v_snd_6667_);
if (v_isSharedCheck_6825_ == 0)
{
lean_object* v_unused_6826_; 
v_unused_6826_ = lean_ctor_get(v_snd_6667_, 1);
lean_dec(v_unused_6826_);
v___x_6679_ = v_snd_6667_;
v_isShared_6680_ = v_isSharedCheck_6825_;
goto v_resetjp_6678_;
}
else
{
lean_inc(v_fst_6677_);
lean_dec(v_snd_6667_);
v___x_6679_ = lean_box(0);
v_isShared_6680_ = v_isSharedCheck_6825_;
goto v_resetjp_6678_;
}
v_resetjp_6678_:
{
lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v_aux1_6683_; lean_object* v_aux1_6684_; lean_object* v_aux1_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___f_6691_; uint8_t v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; 
lean_inc_ref(v_matcherLevels_6651_);
v___x_6681_ = lean_array_to_list(v_matcherLevels_6651_);
lean_inc(v___x_6681_);
lean_inc(v_matcherName_6537_);
v___x_6682_ = l_Lean_mkConst(v_matcherName_6537_, v___x_6681_);
v_aux1_6683_ = l_Lean_mkAppN(v___x_6682_, v___y_6649_);
lean_inc_ref(v___y_6648_);
v_aux1_6684_ = l_Lean_Expr_app___override(v_aux1_6683_, v___y_6648_);
v_aux1_6685_ = l_Lean_mkAppN(v_aux1_6684_, v___y_6647_);
v___x_6686_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6685_, 2);
v___x_6687_ = l_Lean_indentExpr(v_aux1_6685_);
v___x_6688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6688_, 0, v___x_6686_);
lean_ctor_set(v___x_6688_, 1, v___x_6687_);
v___x_6689_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6690_, 0, v___x_6688_);
lean_ctor_set(v___x_6690_, 1, v___x_6689_);
v___f_6691_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6691_, 0, v___x_6690_);
v___x_6692_ = 0;
v___x_6693_ = lean_box(v___x_6692_);
v___x_6694_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6694_, 0, v_aux1_6685_);
lean_closure_set(v___x_6694_, 1, v___x_6693_);
v___x_6695_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6694_, v___f_6691_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
if (lean_obj_tag(v___x_6695_) == 0)
{
lean_object* v___x_6696_; lean_object* v___x_6697_; 
lean_dec_ref_known(v___x_6695_, 1);
v___x_6696_ = lean_array_get_size(v_alts_6542_);
v___x_6697_ = l_Lean_Meta_inferArgumentTypesN(v___x_6696_, v_aux1_6685_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
if (lean_obj_tag(v___x_6697_) == 0)
{
lean_object* v_a_6698_; lean_object* v___x_6699_; 
v_a_6698_ = lean_ctor_get(v___x_6697_, 0);
lean_inc(v_a_6698_);
lean_dec_ref_known(v___x_6697_, 1);
lean_inc(v___y_6655_);
lean_inc_ref(v___y_6654_);
lean_inc(v___y_6653_);
lean_inc_ref(v___y_6652_);
v___x_6699_ = lean_get_match_equations_for(v_matcherName_6537_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
if (lean_obj_tag(v___x_6699_) == 0)
{
lean_object* v_a_6700_; lean_object* v_splitterName_6701_; lean_object* v_splitterMatchInfo_6702_; lean_object* v___x_6703_; lean_object* v_aux2_6704_; lean_object* v_aux2_6705_; lean_object* v_aux2_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___f_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; lean_object* v___x_6714_; 
v_a_6700_ = lean_ctor_get(v___x_6699_, 0);
lean_inc(v_a_6700_);
lean_dec_ref_known(v___x_6699_, 1);
v_splitterName_6701_ = lean_ctor_get(v_a_6700_, 1);
lean_inc_n(v_splitterName_6701_, 2);
v_splitterMatchInfo_6702_ = lean_ctor_get(v_a_6700_, 2);
lean_inc_ref(v_splitterMatchInfo_6702_);
lean_dec(v_a_6700_);
v___x_6703_ = l_Lean_mkConst(v_splitterName_6701_, v___x_6681_);
v_aux2_6704_ = l_Lean_mkAppN(v___x_6703_, v___y_6649_);
lean_inc_ref(v___y_6648_);
v_aux2_6705_ = l_Lean_Expr_app___override(v_aux2_6704_, v___y_6648_);
v_aux2_6706_ = l_Lean_mkAppN(v_aux2_6705_, v___y_6647_);
v___x_6707_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6706_, 2);
v___x_6708_ = l_Lean_indentExpr(v_aux2_6706_);
v___x_6709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6709_, 0, v___x_6707_);
lean_ctor_set(v___x_6709_, 1, v___x_6708_);
v___x_6710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6710_, 0, v___x_6709_);
lean_ctor_set(v___x_6710_, 1, v___x_6689_);
v___f_6711_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6711_, 0, v___x_6710_);
v___x_6712_ = lean_box(v___x_6692_);
v___x_6713_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6713_, 0, v_aux2_6706_);
lean_closure_set(v___x_6713_, 1, v___x_6712_);
v___x_6714_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6713_, v___f_6711_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
if (lean_obj_tag(v___x_6714_) == 0)
{
lean_object* v___x_6715_; 
lean_dec_ref_known(v___x_6714_, 1);
v___x_6715_ = l_Lean_Meta_inferArgumentTypesN(v___x_6696_, v_aux2_6706_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
if (lean_obj_tag(v___x_6715_) == 0)
{
lean_object* v_a_6716_; lean_object* v_numParams_6717_; lean_object* v_numDiscrs_6718_; lean_object* v_altInfos_6719_; lean_object* v_uElimPos_x3f_6720_; lean_object* v_overlaps_6721_; lean_object* v_altInfos_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6779_; 
v_a_6716_ = lean_ctor_get(v___x_6715_, 0);
lean_inc(v_a_6716_);
lean_dec_ref_known(v___x_6715_, 1);
v_numParams_6717_ = lean_ctor_get(v_toMatcherInfo_6536_, 0);
lean_inc(v_numParams_6717_);
v_numDiscrs_6718_ = lean_ctor_get(v_toMatcherInfo_6536_, 1);
lean_inc(v_numDiscrs_6718_);
v_altInfos_6719_ = lean_ctor_get(v_toMatcherInfo_6536_, 2);
lean_inc_ref(v_altInfos_6719_);
v_uElimPos_x3f_6720_ = lean_ctor_get(v_toMatcherInfo_6536_, 3);
lean_inc(v_uElimPos_x3f_6720_);
v_overlaps_6721_ = lean_ctor_get(v_toMatcherInfo_6536_, 5);
lean_inc_ref(v_overlaps_6721_);
lean_dec_ref(v_toMatcherInfo_6536_);
v_altInfos_6722_ = lean_ctor_get(v_splitterMatchInfo_6702_, 2);
v_isSharedCheck_6779_ = !lean_is_exclusive(v_splitterMatchInfo_6702_);
if (v_isSharedCheck_6779_ == 0)
{
lean_object* v_unused_6780_; lean_object* v_unused_6781_; lean_object* v_unused_6782_; lean_object* v_unused_6783_; lean_object* v_unused_6784_; 
v_unused_6780_ = lean_ctor_get(v_splitterMatchInfo_6702_, 5);
lean_dec(v_unused_6780_);
v_unused_6781_ = lean_ctor_get(v_splitterMatchInfo_6702_, 4);
lean_dec(v_unused_6781_);
v_unused_6782_ = lean_ctor_get(v_splitterMatchInfo_6702_, 3);
lean_dec(v_unused_6782_);
v_unused_6783_ = lean_ctor_get(v_splitterMatchInfo_6702_, 1);
lean_dec(v_unused_6783_);
v_unused_6784_ = lean_ctor_get(v_splitterMatchInfo_6702_, 0);
lean_dec(v_unused_6784_);
v___x_6724_ = v_splitterMatchInfo_6702_;
v_isShared_6725_ = v_isSharedCheck_6779_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_altInfos_6722_);
lean_dec(v_splitterMatchInfo_6702_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6779_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; lean_object* v___x_6733_; lean_object* v___x_6734_; lean_object* v___x_6736_; 
v___x_6726_ = lean_array_get_size(v_altInfos_6719_);
v___x_6727_ = lean_array_get_size(v_altInfos_6722_);
v___x_6728_ = lean_array_get_size(v_a_6698_);
v___x_6729_ = lean_array_get_size(v_a_6716_);
v___x_6730_ = l_Array_toSubarray___redArg(v_alts_6542_, v___x_6656_, v___x_6696_);
lean_inc_ref(v_altInfos_6719_);
v___x_6731_ = l_Array_toSubarray___redArg(v_altInfos_6719_, v___x_6656_, v___x_6726_);
v___x_6732_ = l_Array_toSubarray___redArg(v_altInfos_6722_, v___x_6656_, v___x_6727_);
v___x_6733_ = l_Array_toSubarray___redArg(v_a_6698_, v___x_6656_, v___x_6728_);
v___x_6734_ = l_Array_toSubarray___redArg(v_a_6716_, v___x_6656_, v___x_6729_);
if (v_isShared_6680_ == 0)
{
lean_ctor_set(v___x_6679_, 1, v___x_6734_);
lean_ctor_set(v___x_6679_, 0, v___x_6733_);
v___x_6736_ = v___x_6679_;
goto v_reusejp_6735_;
}
else
{
lean_object* v_reuseFailAlloc_6778_; 
v_reuseFailAlloc_6778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6778_, 0, v___x_6733_);
lean_ctor_set(v_reuseFailAlloc_6778_, 1, v___x_6734_);
v___x_6736_ = v_reuseFailAlloc_6778_;
goto v_reusejp_6735_;
}
v_reusejp_6735_:
{
lean_object* v___x_6738_; 
if (v_isShared_6676_ == 0)
{
lean_ctor_set(v___x_6675_, 1, v___x_6736_);
lean_ctor_set(v___x_6675_, 0, v___x_6732_);
v___x_6738_ = v___x_6675_;
goto v_reusejp_6737_;
}
else
{
lean_object* v_reuseFailAlloc_6777_; 
v_reuseFailAlloc_6777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6777_, 0, v___x_6732_);
lean_ctor_set(v_reuseFailAlloc_6777_, 1, v___x_6736_);
v___x_6738_ = v_reuseFailAlloc_6777_;
goto v_reusejp_6737_;
}
v_reusejp_6737_:
{
lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; 
v___x_6739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6739_, 0, v___x_6731_);
lean_ctor_set(v___x_6739_, 1, v___x_6738_);
v___x_6740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6740_, 0, v___x_6730_);
lean_ctor_set(v___x_6740_, 1, v___x_6739_);
v___x_6741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6741_, 0, v_remaining_x27_6657_);
lean_ctor_set(v___x_6741_, 1, v___x_6740_);
v___x_6742_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6696_, v_onAlt_6527_, v_useSplitter_6523_, v_fst_6677_, v___y_6650_, v___x_6656_, v___x_6741_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_);
if (lean_obj_tag(v___x_6742_) == 0)
{
lean_object* v_a_6743_; lean_object* v_fst_6744_; lean_object* v___x_6745_; 
v_a_6743_ = lean_ctor_get(v___x_6742_, 0);
lean_inc(v_a_6743_);
lean_dec_ref_known(v___x_6742_, 1);
v_fst_6744_ = lean_ctor_get(v_a_6743_, 0);
lean_inc(v_fst_6744_);
lean_dec(v_a_6743_);
lean_inc(v___y_6655_);
lean_inc_ref(v___y_6654_);
lean_inc(v___y_6653_);
lean_inc_ref(v___y_6652_);
v___x_6745_ = lean_apply_6(v_onRemaining_6528_, v_remaining_6543_, v___y_6652_, v___y_6653_, v___y_6654_, v___y_6655_, lean_box(0));
if (lean_obj_tag(v___x_6745_) == 0)
{
lean_object* v_a_6746_; lean_object* v___x_6748_; uint8_t v_isShared_6749_; uint8_t v_isSharedCheck_6760_; 
v_a_6746_ = lean_ctor_get(v___x_6745_, 0);
v_isSharedCheck_6760_ = !lean_is_exclusive(v___x_6745_);
if (v_isSharedCheck_6760_ == 0)
{
v___x_6748_ = v___x_6745_;
v_isShared_6749_ = v_isSharedCheck_6760_;
goto v_resetjp_6747_;
}
else
{
lean_inc(v_a_6746_);
lean_dec(v___x_6745_);
v___x_6748_ = lean_box(0);
v_isShared_6749_ = v_isSharedCheck_6760_;
goto v_resetjp_6747_;
}
v_resetjp_6747_:
{
lean_object* v_remaining_x27_6750_; lean_object* v___x_6752_; 
v_remaining_x27_6750_ = l_Array_append___redArg(v_fst_6673_, v_a_6746_);
lean_dec(v_a_6746_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 5, v_overlaps_6721_);
lean_ctor_set(v___x_6724_, 4, v___y_6645_);
lean_ctor_set(v___x_6724_, 3, v_uElimPos_x3f_6720_);
lean_ctor_set(v___x_6724_, 2, v_altInfos_6719_);
lean_ctor_set(v___x_6724_, 1, v_numDiscrs_6718_);
lean_ctor_set(v___x_6724_, 0, v_numParams_6717_);
v___x_6752_ = v___x_6724_;
goto v_reusejp_6751_;
}
else
{
lean_object* v_reuseFailAlloc_6759_; 
v_reuseFailAlloc_6759_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6759_, 0, v_numParams_6717_);
lean_ctor_set(v_reuseFailAlloc_6759_, 1, v_numDiscrs_6718_);
lean_ctor_set(v_reuseFailAlloc_6759_, 2, v_altInfos_6719_);
lean_ctor_set(v_reuseFailAlloc_6759_, 3, v_uElimPos_x3f_6720_);
lean_ctor_set(v_reuseFailAlloc_6759_, 4, v___y_6645_);
lean_ctor_set(v_reuseFailAlloc_6759_, 5, v_overlaps_6721_);
v___x_6752_ = v_reuseFailAlloc_6759_;
goto v_reusejp_6751_;
}
v_reusejp_6751_:
{
lean_object* v___x_6754_; 
if (v_isShared_6672_ == 0)
{
lean_ctor_set(v___x_6671_, 7, v_remaining_x27_6750_);
lean_ctor_set(v___x_6671_, 6, v_fst_6744_);
lean_ctor_set(v___x_6671_, 5, v___y_6647_);
lean_ctor_set(v___x_6671_, 4, v___y_6648_);
lean_ctor_set(v___x_6671_, 3, v___y_6649_);
lean_ctor_set(v___x_6671_, 2, v_matcherLevels_6651_);
lean_ctor_set(v___x_6671_, 1, v_splitterName_6701_);
lean_ctor_set(v___x_6671_, 0, v___x_6752_);
v___x_6754_ = v___x_6671_;
goto v_reusejp_6753_;
}
else
{
lean_object* v_reuseFailAlloc_6758_; 
v_reuseFailAlloc_6758_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6758_, 0, v___x_6752_);
lean_ctor_set(v_reuseFailAlloc_6758_, 1, v_splitterName_6701_);
lean_ctor_set(v_reuseFailAlloc_6758_, 2, v_matcherLevels_6651_);
lean_ctor_set(v_reuseFailAlloc_6758_, 3, v___y_6649_);
lean_ctor_set(v_reuseFailAlloc_6758_, 4, v___y_6648_);
lean_ctor_set(v_reuseFailAlloc_6758_, 5, v___y_6647_);
lean_ctor_set(v_reuseFailAlloc_6758_, 6, v_fst_6744_);
lean_ctor_set(v_reuseFailAlloc_6758_, 7, v_remaining_x27_6750_);
v___x_6754_ = v_reuseFailAlloc_6758_;
goto v_reusejp_6753_;
}
v_reusejp_6753_:
{
lean_object* v___x_6756_; 
if (v_isShared_6749_ == 0)
{
lean_ctor_set(v___x_6748_, 0, v___x_6754_);
v___x_6756_ = v___x_6748_;
goto v_reusejp_6755_;
}
else
{
lean_object* v_reuseFailAlloc_6757_; 
v_reuseFailAlloc_6757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6757_, 0, v___x_6754_);
v___x_6756_ = v_reuseFailAlloc_6757_;
goto v_reusejp_6755_;
}
v_reusejp_6755_:
{
return v___x_6756_;
}
}
}
}
}
else
{
lean_object* v_a_6761_; lean_object* v___x_6763_; uint8_t v_isShared_6764_; uint8_t v_isSharedCheck_6768_; 
lean_dec(v_fst_6744_);
lean_del_object(v___x_6724_);
lean_dec_ref(v_overlaps_6721_);
lean_dec(v_uElimPos_x3f_6720_);
lean_dec_ref(v_altInfos_6719_);
lean_dec(v_numDiscrs_6718_);
lean_dec(v_numParams_6717_);
lean_dec(v_splitterName_6701_);
lean_dec(v_fst_6673_);
lean_del_object(v___x_6671_);
lean_dec_ref(v_matcherLevels_6651_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
v_a_6761_ = lean_ctor_get(v___x_6745_, 0);
v_isSharedCheck_6768_ = !lean_is_exclusive(v___x_6745_);
if (v_isSharedCheck_6768_ == 0)
{
v___x_6763_ = v___x_6745_;
v_isShared_6764_ = v_isSharedCheck_6768_;
goto v_resetjp_6762_;
}
else
{
lean_inc(v_a_6761_);
lean_dec(v___x_6745_);
v___x_6763_ = lean_box(0);
v_isShared_6764_ = v_isSharedCheck_6768_;
goto v_resetjp_6762_;
}
v_resetjp_6762_:
{
lean_object* v___x_6766_; 
if (v_isShared_6764_ == 0)
{
v___x_6766_ = v___x_6763_;
goto v_reusejp_6765_;
}
else
{
lean_object* v_reuseFailAlloc_6767_; 
v_reuseFailAlloc_6767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6767_, 0, v_a_6761_);
v___x_6766_ = v_reuseFailAlloc_6767_;
goto v_reusejp_6765_;
}
v_reusejp_6765_:
{
return v___x_6766_;
}
}
}
}
else
{
lean_object* v_a_6769_; lean_object* v___x_6771_; uint8_t v_isShared_6772_; uint8_t v_isSharedCheck_6776_; 
lean_del_object(v___x_6724_);
lean_dec_ref(v_overlaps_6721_);
lean_dec(v_uElimPos_x3f_6720_);
lean_dec_ref(v_altInfos_6719_);
lean_dec(v_numDiscrs_6718_);
lean_dec(v_numParams_6717_);
lean_dec(v_splitterName_6701_);
lean_dec(v_fst_6673_);
lean_del_object(v___x_6671_);
lean_dec_ref(v_matcherLevels_6651_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_onRemaining_6528_);
v_a_6769_ = lean_ctor_get(v___x_6742_, 0);
v_isSharedCheck_6776_ = !lean_is_exclusive(v___x_6742_);
if (v_isSharedCheck_6776_ == 0)
{
v___x_6771_ = v___x_6742_;
v_isShared_6772_ = v_isSharedCheck_6776_;
goto v_resetjp_6770_;
}
else
{
lean_inc(v_a_6769_);
lean_dec(v___x_6742_);
v___x_6771_ = lean_box(0);
v_isShared_6772_ = v_isSharedCheck_6776_;
goto v_resetjp_6770_;
}
v_resetjp_6770_:
{
lean_object* v___x_6774_; 
if (v_isShared_6772_ == 0)
{
v___x_6774_ = v___x_6771_;
goto v_reusejp_6773_;
}
else
{
lean_object* v_reuseFailAlloc_6775_; 
v_reuseFailAlloc_6775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6775_, 0, v_a_6769_);
v___x_6774_ = v_reuseFailAlloc_6775_;
goto v_reusejp_6773_;
}
v_reusejp_6773_:
{
return v___x_6774_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6785_; lean_object* v___x_6787_; uint8_t v_isShared_6788_; uint8_t v_isSharedCheck_6792_; 
lean_dec_ref(v_splitterMatchInfo_6702_);
lean_dec(v_splitterName_6701_);
lean_dec(v_a_6698_);
lean_del_object(v___x_6679_);
lean_dec(v_fst_6677_);
lean_del_object(v___x_6675_);
lean_dec(v_fst_6673_);
lean_del_object(v___x_6671_);
lean_dec_ref(v_matcherLevels_6651_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
v_a_6785_ = lean_ctor_get(v___x_6715_, 0);
v_isSharedCheck_6792_ = !lean_is_exclusive(v___x_6715_);
if (v_isSharedCheck_6792_ == 0)
{
v___x_6787_ = v___x_6715_;
v_isShared_6788_ = v_isSharedCheck_6792_;
goto v_resetjp_6786_;
}
else
{
lean_inc(v_a_6785_);
lean_dec(v___x_6715_);
v___x_6787_ = lean_box(0);
v_isShared_6788_ = v_isSharedCheck_6792_;
goto v_resetjp_6786_;
}
v_resetjp_6786_:
{
lean_object* v___x_6790_; 
if (v_isShared_6788_ == 0)
{
v___x_6790_ = v___x_6787_;
goto v_reusejp_6789_;
}
else
{
lean_object* v_reuseFailAlloc_6791_; 
v_reuseFailAlloc_6791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6791_, 0, v_a_6785_);
v___x_6790_ = v_reuseFailAlloc_6791_;
goto v_reusejp_6789_;
}
v_reusejp_6789_:
{
return v___x_6790_;
}
}
}
}
else
{
lean_object* v_a_6793_; lean_object* v___x_6795_; uint8_t v_isShared_6796_; uint8_t v_isSharedCheck_6800_; 
lean_dec_ref(v_aux2_6706_);
lean_dec_ref(v_splitterMatchInfo_6702_);
lean_dec(v_splitterName_6701_);
lean_dec(v_a_6698_);
lean_del_object(v___x_6679_);
lean_dec(v_fst_6677_);
lean_del_object(v___x_6675_);
lean_dec(v_fst_6673_);
lean_del_object(v___x_6671_);
lean_dec_ref(v_matcherLevels_6651_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
v_a_6793_ = lean_ctor_get(v___x_6714_, 0);
v_isSharedCheck_6800_ = !lean_is_exclusive(v___x_6714_);
if (v_isSharedCheck_6800_ == 0)
{
v___x_6795_ = v___x_6714_;
v_isShared_6796_ = v_isSharedCheck_6800_;
goto v_resetjp_6794_;
}
else
{
lean_inc(v_a_6793_);
lean_dec(v___x_6714_);
v___x_6795_ = lean_box(0);
v_isShared_6796_ = v_isSharedCheck_6800_;
goto v_resetjp_6794_;
}
v_resetjp_6794_:
{
lean_object* v___x_6798_; 
if (v_isShared_6796_ == 0)
{
v___x_6798_ = v___x_6795_;
goto v_reusejp_6797_;
}
else
{
lean_object* v_reuseFailAlloc_6799_; 
v_reuseFailAlloc_6799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6799_, 0, v_a_6793_);
v___x_6798_ = v_reuseFailAlloc_6799_;
goto v_reusejp_6797_;
}
v_reusejp_6797_:
{
return v___x_6798_;
}
}
}
}
else
{
lean_object* v_a_6801_; lean_object* v___x_6803_; uint8_t v_isShared_6804_; uint8_t v_isSharedCheck_6808_; 
lean_dec(v_a_6698_);
lean_dec(v___x_6681_);
lean_del_object(v___x_6679_);
lean_dec(v_fst_6677_);
lean_del_object(v___x_6675_);
lean_dec(v_fst_6673_);
lean_del_object(v___x_6671_);
lean_dec_ref(v_matcherLevels_6651_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
v_a_6801_ = lean_ctor_get(v___x_6699_, 0);
v_isSharedCheck_6808_ = !lean_is_exclusive(v___x_6699_);
if (v_isSharedCheck_6808_ == 0)
{
v___x_6803_ = v___x_6699_;
v_isShared_6804_ = v_isSharedCheck_6808_;
goto v_resetjp_6802_;
}
else
{
lean_inc(v_a_6801_);
lean_dec(v___x_6699_);
v___x_6803_ = lean_box(0);
v_isShared_6804_ = v_isSharedCheck_6808_;
goto v_resetjp_6802_;
}
v_resetjp_6802_:
{
lean_object* v___x_6806_; 
if (v_isShared_6804_ == 0)
{
v___x_6806_ = v___x_6803_;
goto v_reusejp_6805_;
}
else
{
lean_object* v_reuseFailAlloc_6807_; 
v_reuseFailAlloc_6807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6807_, 0, v_a_6801_);
v___x_6806_ = v_reuseFailAlloc_6807_;
goto v_reusejp_6805_;
}
v_reusejp_6805_:
{
return v___x_6806_;
}
}
}
}
else
{
lean_object* v_a_6809_; lean_object* v___x_6811_; uint8_t v_isShared_6812_; uint8_t v_isSharedCheck_6816_; 
lean_dec(v___x_6681_);
lean_del_object(v___x_6679_);
lean_dec(v_fst_6677_);
lean_del_object(v___x_6675_);
lean_dec(v_fst_6673_);
lean_del_object(v___x_6671_);
lean_dec_ref(v_matcherLevels_6651_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
v_a_6809_ = lean_ctor_get(v___x_6697_, 0);
v_isSharedCheck_6816_ = !lean_is_exclusive(v___x_6697_);
if (v_isSharedCheck_6816_ == 0)
{
v___x_6811_ = v___x_6697_;
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
else
{
lean_inc(v_a_6809_);
lean_dec(v___x_6697_);
v___x_6811_ = lean_box(0);
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
v_resetjp_6810_:
{
lean_object* v___x_6814_; 
if (v_isShared_6812_ == 0)
{
v___x_6814_ = v___x_6811_;
goto v_reusejp_6813_;
}
else
{
lean_object* v_reuseFailAlloc_6815_; 
v_reuseFailAlloc_6815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_a_6809_);
v___x_6814_ = v_reuseFailAlloc_6815_;
goto v_reusejp_6813_;
}
v_reusejp_6813_:
{
return v___x_6814_;
}
}
}
}
else
{
lean_object* v_a_6817_; lean_object* v___x_6819_; uint8_t v_isShared_6820_; uint8_t v_isSharedCheck_6824_; 
lean_dec_ref(v_aux1_6685_);
lean_dec(v___x_6681_);
lean_del_object(v___x_6679_);
lean_dec(v_fst_6677_);
lean_del_object(v___x_6675_);
lean_dec(v_fst_6673_);
lean_del_object(v___x_6671_);
lean_dec_ref(v_matcherLevels_6651_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
v_a_6817_ = lean_ctor_get(v___x_6695_, 0);
v_isSharedCheck_6824_ = !lean_is_exclusive(v___x_6695_);
if (v_isSharedCheck_6824_ == 0)
{
v___x_6819_ = v___x_6695_;
v_isShared_6820_ = v_isSharedCheck_6824_;
goto v_resetjp_6818_;
}
else
{
lean_inc(v_a_6817_);
lean_dec(v___x_6695_);
v___x_6819_ = lean_box(0);
v_isShared_6820_ = v_isSharedCheck_6824_;
goto v_resetjp_6818_;
}
v_resetjp_6818_:
{
lean_object* v___x_6822_; 
if (v_isShared_6820_ == 0)
{
v___x_6822_ = v___x_6819_;
goto v_reusejp_6821_;
}
else
{
lean_object* v_reuseFailAlloc_6823_; 
v_reuseFailAlloc_6823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6823_, 0, v_a_6817_);
v___x_6822_ = v_reuseFailAlloc_6823_;
goto v_reusejp_6821_;
}
v_reusejp_6821_:
{
return v___x_6822_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6838_; lean_object* v_fst_6839_; 
lean_dec(v___y_6650_);
v_fst_6838_ = lean_ctor_get(v_a_6666_, 0);
lean_inc(v_fst_6838_);
lean_dec(v_a_6666_);
v_fst_6839_ = lean_ctor_get(v_snd_6667_, 0);
lean_inc(v_fst_6839_);
lean_dec(v_snd_6667_);
v___y_6545_ = v___y_6647_;
v___y_6546_ = v_fst_6838_;
v___y_6547_ = v_matcherLevels_6651_;
v___y_6548_ = v___y_6655_;
v___y_6549_ = v_remaining_x27_6657_;
v___y_6550_ = v___y_6648_;
v___y_6551_ = v___y_6652_;
v___y_6552_ = v___y_6654_;
v___y_6553_ = v___y_6645_;
v___y_6554_ = v___x_6656_;
v___y_6555_ = v___y_6653_;
v___y_6556_ = v___y_6649_;
v___y_6557_ = v_fst_6839_;
goto v___jp_6544_;
}
}
}
else
{
lean_object* v_a_6840_; lean_object* v___x_6842_; uint8_t v_isShared_6843_; uint8_t v_isSharedCheck_6847_; 
lean_dec_ref(v_matcherLevels_6651_);
lean_dec(v___y_6650_);
lean_dec_ref(v___y_6649_);
lean_dec_ref(v___y_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
lean_dec_ref(v_matcherApp_6522_);
v_a_6840_ = lean_ctor_get(v___x_6665_, 0);
v_isSharedCheck_6847_ = !lean_is_exclusive(v___x_6665_);
if (v_isSharedCheck_6847_ == 0)
{
v___x_6842_ = v___x_6665_;
v_isShared_6843_ = v_isSharedCheck_6847_;
goto v_resetjp_6841_;
}
else
{
lean_inc(v_a_6840_);
lean_dec(v___x_6665_);
v___x_6842_ = lean_box(0);
v_isShared_6843_ = v_isSharedCheck_6847_;
goto v_resetjp_6841_;
}
v_resetjp_6841_:
{
lean_object* v___x_6845_; 
if (v_isShared_6843_ == 0)
{
v___x_6845_ = v___x_6842_;
goto v_reusejp_6844_;
}
else
{
lean_object* v_reuseFailAlloc_6846_; 
v_reuseFailAlloc_6846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6846_, 0, v_a_6840_);
v___x_6845_ = v_reuseFailAlloc_6846_;
goto v_reusejp_6844_;
}
v_reusejp_6844_:
{
return v___x_6845_;
}
}
}
}
v___jp_6848_:
{
size_t v_sz_6854_; size_t v___x_6855_; lean_object* v___x_6856_; 
v_sz_6854_ = lean_array_size(v_params_6539_);
v___x_6855_ = ((size_t)0ULL);
lean_inc_ref(v_params_6539_);
lean_inc_ref(v_onParams_6525_);
v___x_6856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6525_, v_sz_6854_, v___x_6855_, v_params_6539_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_);
if (lean_obj_tag(v___x_6856_) == 0)
{
lean_object* v_a_6857_; size_t v_sz_6858_; lean_object* v___x_6859_; 
v_a_6857_ = lean_ctor_get(v___x_6856_, 0);
lean_inc(v_a_6857_);
lean_dec_ref_known(v___x_6856_, 1);
v_sz_6858_ = lean_array_size(v_discrs_6541_);
lean_inc_ref(v_discrs_6541_);
v___x_6859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6525_, v_sz_6858_, v___x_6855_, v_discrs_6541_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_);
if (lean_obj_tag(v___x_6859_) == 0)
{
lean_object* v_a_6860_; lean_object* v___x_6861_; lean_object* v___x_6862_; lean_object* v___f_6863_; uint8_t v___x_6864_; lean_object* v___x_6865_; 
v_a_6860_ = lean_ctor_get(v___x_6859_, 0);
lean_inc_n(v_a_6860_, 2);
lean_dec_ref_known(v___x_6859_, 1);
v___x_6861_ = lean_box(v_addEqualities_6524_);
v___x_6862_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6541_);
lean_inc_ref(v_toMatcherInfo_6536_);
v___f_6863_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6863_, 0, v_onMotive_6526_);
lean_closure_set(v___f_6863_, 1, v_toMatcherInfo_6536_);
lean_closure_set(v___f_6863_, 2, v_a_6860_);
lean_closure_set(v___f_6863_, 3, v___x_6861_);
lean_closure_set(v___f_6863_, 4, v___x_6862_);
lean_closure_set(v___f_6863_, 5, v_discrs_6541_);
v___x_6864_ = 0;
lean_inc_ref(v_motive_6540_);
v___x_6865_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6540_, v___f_6863_, v___x_6864_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_);
if (lean_obj_tag(v___x_6865_) == 0)
{
lean_object* v_a_6866_; lean_object* v_snd_6867_; lean_object* v_snd_6868_; lean_object* v_uElimPos_x3f_6869_; 
v_a_6866_ = lean_ctor_get(v___x_6865_, 0);
lean_inc(v_a_6866_);
lean_dec_ref_known(v___x_6865_, 1);
v_snd_6867_ = lean_ctor_get(v_a_6866_, 1);
v_snd_6868_ = lean_ctor_get(v_snd_6867_, 1);
lean_inc(v_snd_6868_);
v_uElimPos_x3f_6869_ = lean_ctor_get(v_toMatcherInfo_6536_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6869_) == 0)
{
lean_object* v_fst_6870_; lean_object* v_fst_6871_; lean_object* v_snd_6872_; 
v_fst_6870_ = lean_ctor_get(v_a_6866_, 0);
lean_inc(v_fst_6870_);
lean_dec(v_a_6866_);
v_fst_6871_ = lean_ctor_get(v_snd_6868_, 0);
lean_inc(v_fst_6871_);
v_snd_6872_ = lean_ctor_get(v_snd_6868_, 1);
lean_inc(v_snd_6872_);
lean_dec(v_snd_6868_);
lean_inc_ref(v_matcherLevels_6538_);
v___y_6644_ = v_fst_6871_;
v___y_6645_ = v_snd_6872_;
v___y_6646_ = v___x_6855_;
v___y_6647_ = v_a_6860_;
v___y_6648_ = v_fst_6870_;
v___y_6649_ = v_a_6857_;
v___y_6650_ = v_numDiscrEqs_6849_;
v_matcherLevels_6651_ = v_matcherLevels_6538_;
v___y_6652_ = v___y_6850_;
v___y_6653_ = v___y_6851_;
v___y_6654_ = v___y_6852_;
v___y_6655_ = v___y_6853_;
goto v___jp_6643_;
}
else
{
lean_object* v_fst_6873_; lean_object* v_fst_6874_; lean_object* v_fst_6875_; lean_object* v_snd_6876_; lean_object* v_val_6877_; lean_object* v___x_6878_; 
lean_inc(v_snd_6867_);
v_fst_6873_ = lean_ctor_get(v_a_6866_, 0);
lean_inc(v_fst_6873_);
lean_dec(v_a_6866_);
v_fst_6874_ = lean_ctor_get(v_snd_6867_, 0);
lean_inc(v_fst_6874_);
lean_dec(v_snd_6867_);
v_fst_6875_ = lean_ctor_get(v_snd_6868_, 0);
lean_inc(v_fst_6875_);
v_snd_6876_ = lean_ctor_get(v_snd_6868_, 1);
lean_inc(v_snd_6876_);
lean_dec(v_snd_6868_);
v_val_6877_ = lean_ctor_get(v_uElimPos_x3f_6869_, 0);
lean_inc_ref(v_matcherLevels_6538_);
v___x_6878_ = lean_array_set(v_matcherLevels_6538_, v_val_6877_, v_fst_6874_);
v___y_6644_ = v_fst_6875_;
v___y_6645_ = v_snd_6876_;
v___y_6646_ = v___x_6855_;
v___y_6647_ = v_a_6860_;
v___y_6648_ = v_fst_6873_;
v___y_6649_ = v_a_6857_;
v___y_6650_ = v_numDiscrEqs_6849_;
v_matcherLevels_6651_ = v___x_6878_;
v___y_6652_ = v___y_6850_;
v___y_6653_ = v___y_6851_;
v___y_6654_ = v___y_6852_;
v___y_6655_ = v___y_6853_;
goto v___jp_6643_;
}
}
else
{
lean_object* v_a_6879_; lean_object* v___x_6881_; uint8_t v_isShared_6882_; uint8_t v_isSharedCheck_6886_; 
lean_dec(v_a_6860_);
lean_dec(v_a_6857_);
lean_dec(v_numDiscrEqs_6849_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
lean_dec_ref(v_matcherApp_6522_);
v_a_6879_ = lean_ctor_get(v___x_6865_, 0);
v_isSharedCheck_6886_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6886_ == 0)
{
v___x_6881_ = v___x_6865_;
v_isShared_6882_ = v_isSharedCheck_6886_;
goto v_resetjp_6880_;
}
else
{
lean_inc(v_a_6879_);
lean_dec(v___x_6865_);
v___x_6881_ = lean_box(0);
v_isShared_6882_ = v_isSharedCheck_6886_;
goto v_resetjp_6880_;
}
v_resetjp_6880_:
{
lean_object* v___x_6884_; 
if (v_isShared_6882_ == 0)
{
v___x_6884_ = v___x_6881_;
goto v_reusejp_6883_;
}
else
{
lean_object* v_reuseFailAlloc_6885_; 
v_reuseFailAlloc_6885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6885_, 0, v_a_6879_);
v___x_6884_ = v_reuseFailAlloc_6885_;
goto v_reusejp_6883_;
}
v_reusejp_6883_:
{
return v___x_6884_;
}
}
}
}
else
{
lean_object* v_a_6887_; lean_object* v___x_6889_; uint8_t v_isShared_6890_; uint8_t v_isSharedCheck_6894_; 
lean_dec(v_a_6857_);
lean_dec(v_numDiscrEqs_6849_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
lean_dec_ref(v_onMotive_6526_);
lean_dec_ref(v_matcherApp_6522_);
v_a_6887_ = lean_ctor_get(v___x_6859_, 0);
v_isSharedCheck_6894_ = !lean_is_exclusive(v___x_6859_);
if (v_isSharedCheck_6894_ == 0)
{
v___x_6889_ = v___x_6859_;
v_isShared_6890_ = v_isSharedCheck_6894_;
goto v_resetjp_6888_;
}
else
{
lean_inc(v_a_6887_);
lean_dec(v___x_6859_);
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
lean_dec(v_numDiscrEqs_6849_);
lean_dec_ref(v_remaining_6543_);
lean_dec_ref(v_alts_6542_);
lean_dec(v_matcherName_6537_);
lean_dec_ref(v_toMatcherInfo_6536_);
lean_dec_ref(v_onRemaining_6528_);
lean_dec_ref(v_onAlt_6527_);
lean_dec_ref(v_onMotive_6526_);
lean_dec_ref(v_onParams_6525_);
lean_dec_ref(v_matcherApp_6522_);
v_a_6895_ = lean_ctor_get(v___x_6856_, 0);
v_isSharedCheck_6902_ = !lean_is_exclusive(v___x_6856_);
if (v_isSharedCheck_6902_ == 0)
{
v___x_6897_ = v___x_6856_;
v_isShared_6898_ = v_isSharedCheck_6902_;
goto v_resetjp_6896_;
}
else
{
lean_inc(v_a_6895_);
lean_dec(v___x_6856_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6922_, lean_object* v_useSplitter_6923_, lean_object* v_addEqualities_6924_, lean_object* v_onParams_6925_, lean_object* v_onMotive_6926_, lean_object* v_onAlt_6927_, lean_object* v_onRemaining_6928_, lean_object* v___y_6929_, lean_object* v___y_6930_, lean_object* v___y_6931_, lean_object* v___y_6932_, lean_object* v___y_6933_){
_start:
{
uint8_t v_useSplitter_boxed_6934_; uint8_t v_addEqualities_boxed_6935_; lean_object* v_res_6936_; 
v_useSplitter_boxed_6934_ = lean_unbox(v_useSplitter_6923_);
v_addEqualities_boxed_6935_ = lean_unbox(v_addEqualities_6924_);
v_res_6936_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6922_, v_useSplitter_boxed_6934_, v_addEqualities_boxed_6935_, v_onParams_6925_, v_onMotive_6926_, v_onAlt_6927_, v_onRemaining_6928_, v___y_6929_, v___y_6930_, v___y_6931_, v___y_6932_);
lean_dec(v___y_6932_);
lean_dec_ref(v___y_6931_);
lean_dec(v___y_6930_);
lean_dec_ref(v___y_6929_);
return v_res_6936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6942_, lean_object* v_a_6943_, lean_object* v_a_6944_, lean_object* v_a_6945_, lean_object* v_a_6946_){
_start:
{
lean_object* v_toMatcherInfo_6948_; lean_object* v_matcherName_6949_; lean_object* v_matcherLevels_6950_; lean_object* v_params_6951_; lean_object* v_alts_6952_; lean_object* v_remaining_6953_; lean_object* v___f_6954_; lean_object* v___f_6955_; lean_object* v_nExtra_6956_; uint8_t v___x_6957_; lean_object* v___f_6958_; uint8_t v___x_6959_; lean_object* v___x_6960_; lean_object* v___x_6961_; lean_object* v___f_6962_; lean_object* v___x_6963_; 
v_toMatcherInfo_6948_ = lean_ctor_get(v_matcherApp_6942_, 0);
v_matcherName_6949_ = lean_ctor_get(v_matcherApp_6942_, 1);
v_matcherLevels_6950_ = lean_ctor_get(v_matcherApp_6942_, 2);
v_params_6951_ = lean_ctor_get(v_matcherApp_6942_, 3);
v_alts_6952_ = lean_ctor_get(v_matcherApp_6942_, 6);
v_remaining_6953_ = lean_ctor_get(v_matcherApp_6942_, 7);
v___f_6954_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6955_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6956_ = lean_array_get_size(v_remaining_6953_);
v___x_6957_ = 1;
v___f_6958_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6959_ = 0;
v___x_6960_ = lean_box(v___x_6959_);
v___x_6961_ = lean_box(v___x_6957_);
lean_inc_ref(v_matcherLevels_6950_);
lean_inc_ref(v_params_6951_);
lean_inc(v_matcherName_6949_);
lean_inc_ref(v_toMatcherInfo_6948_);
lean_inc_ref(v_alts_6952_);
v___f_6962_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6962_, 0, v_nExtra_6956_);
lean_closure_set(v___f_6962_, 1, v___x_6960_);
lean_closure_set(v___f_6962_, 2, v___x_6961_);
lean_closure_set(v___f_6962_, 3, v_alts_6952_);
lean_closure_set(v___f_6962_, 4, v_toMatcherInfo_6948_);
lean_closure_set(v___f_6962_, 5, v_matcherName_6949_);
lean_closure_set(v___f_6962_, 6, v_params_6951_);
lean_closure_set(v___f_6962_, 7, v_matcherLevels_6950_);
v___x_6963_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6942_, v___x_6957_, v___x_6959_, v___f_6954_, v___f_6962_, v___f_6958_, v___f_6955_, v_a_6943_, v_a_6944_, v_a_6945_, v_a_6946_);
return v___x_6963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6964_, lean_object* v_a_6965_, lean_object* v_a_6966_, lean_object* v_a_6967_, lean_object* v_a_6968_, lean_object* v_a_6969_){
_start:
{
lean_object* v_res_6970_; 
v_res_6970_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6964_, v_a_6965_, v_a_6966_, v_a_6967_, v_a_6968_);
lean_dec(v_a_6968_);
lean_dec_ref(v_a_6967_);
lean_dec(v_a_6966_);
lean_dec_ref(v_a_6965_);
return v_res_6970_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6971_, lean_object* v_termAlt_6972_, lean_object* v_inst_6973_, lean_object* v_R_6974_, lean_object* v_a_6975_, lean_object* v_b_6976_, lean_object* v_c_6977_, lean_object* v___y_6978_, lean_object* v___y_6979_, lean_object* v___y_6980_, lean_object* v___y_6981_){
_start:
{
lean_object* v___x_6983_; 
v___x_6983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6971_, v_termAlt_6972_, v_a_6975_, v_b_6976_, v___y_6978_, v___y_6979_, v___y_6980_, v___y_6981_);
return v___x_6983_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6984_, lean_object* v_termAlt_6985_, lean_object* v_inst_6986_, lean_object* v_R_6987_, lean_object* v_a_6988_, lean_object* v_b_6989_, lean_object* v_c_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_, lean_object* v___y_6993_, lean_object* v___y_6994_, lean_object* v___y_6995_){
_start:
{
lean_object* v_res_6996_; 
v_res_6996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6984_, v_termAlt_6985_, v_inst_6986_, v_R_6987_, v_a_6988_, v_b_6989_, v_c_6990_, v___y_6991_, v___y_6992_, v___y_6993_, v___y_6994_);
lean_dec(v___y_6994_);
lean_dec_ref(v___y_6993_);
lean_dec(v___y_6992_);
lean_dec_ref(v___y_6991_);
return v_res_6996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6997_, lean_object* v_fvars_6998_, lean_object* v_names_6999_, lean_object* v_k_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_){
_start:
{
lean_object* v___x_7006_; 
v___x_7006_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6998_, v_names_6999_, v_k_7000_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_);
return v___x_7006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_7007_, lean_object* v_fvars_7008_, lean_object* v_names_7009_, lean_object* v_k_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_, lean_object* v___y_7014_, lean_object* v___y_7015_){
_start:
{
lean_object* v_res_7016_; 
v_res_7016_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_7007_, v_fvars_7008_, v_names_7009_, v_k_7010_, v___y_7011_, v___y_7012_, v___y_7013_, v___y_7014_);
lean_dec(v___y_7014_);
lean_dec_ref(v___y_7013_);
lean_dec(v___y_7012_);
lean_dec_ref(v___y_7011_);
lean_dec_ref(v_names_7009_);
lean_dec_ref(v_fvars_7008_);
return v_res_7016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7017_, lean_object* v_origAltType_7018_, lean_object* v_altInfo_7019_, lean_object* v_k_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_){
_start:
{
lean_object* v___x_7026_; 
v___x_7026_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7018_, v_altInfo_7019_, v_k_7020_, v___y_7021_, v___y_7022_, v___y_7023_, v___y_7024_);
return v___x_7026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7027_, lean_object* v_origAltType_7028_, lean_object* v_altInfo_7029_, lean_object* v_k_7030_, lean_object* v___y_7031_, lean_object* v___y_7032_, lean_object* v___y_7033_, lean_object* v___y_7034_, lean_object* v___y_7035_){
_start:
{
lean_object* v_res_7036_; 
v_res_7036_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7027_, v_origAltType_7028_, v_altInfo_7029_, v_k_7030_, v___y_7031_, v___y_7032_, v___y_7033_, v___y_7034_);
lean_dec(v___y_7034_);
lean_dec_ref(v___y_7033_);
lean_dec(v___y_7032_);
lean_dec_ref(v___y_7031_);
return v_res_7036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7037_, lean_object* v___y_7038_, lean_object* v___y_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_){
_start:
{
lean_object* v___x_7043_; 
v___x_7043_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7037_, v___y_7041_);
return v___x_7043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_){
_start:
{
lean_object* v_res_7050_; 
v_res_7050_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7044_, v___y_7045_, v___y_7046_, v___y_7047_, v___y_7048_);
lean_dec(v___y_7048_);
lean_dec_ref(v___y_7047_);
lean_dec(v___y_7046_);
lean_dec_ref(v___y_7045_);
return v_res_7050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7051_, size_t v_i_7052_, lean_object* v_bs_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_){
_start:
{
lean_object* v___x_7059_; 
v___x_7059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7051_, v_i_7052_, v_bs_7053_, v___y_7054_, v___y_7056_, v___y_7057_);
return v___x_7059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7060_, lean_object* v_i_7061_, lean_object* v_bs_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_, lean_object* v___y_7065_, lean_object* v___y_7066_, lean_object* v___y_7067_){
_start:
{
size_t v_sz_boxed_7068_; size_t v_i_boxed_7069_; lean_object* v_res_7070_; 
v_sz_boxed_7068_ = lean_unbox_usize(v_sz_7060_);
lean_dec(v_sz_7060_);
v_i_boxed_7069_ = lean_unbox_usize(v_i_7061_);
lean_dec(v_i_7061_);
v_res_7070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7068_, v_i_boxed_7069_, v_bs_7062_, v___y_7063_, v___y_7064_, v___y_7065_, v___y_7066_);
lean_dec(v___y_7066_);
lean_dec_ref(v___y_7065_);
lean_dec(v___y_7064_);
lean_dec_ref(v___y_7063_);
return v_res_7070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7071_, lean_object* v_onAlt_7072_, lean_object* v_extraEqualities_7073_, lean_object* v_inst_7074_, lean_object* v_R_7075_, lean_object* v_a_7076_, lean_object* v_b_7077_, lean_object* v_c_7078_, lean_object* v___y_7079_, lean_object* v___y_7080_, lean_object* v___y_7081_, lean_object* v___y_7082_){
_start:
{
lean_object* v___x_7084_; 
v___x_7084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7071_, v_onAlt_7072_, v_extraEqualities_7073_, v_a_7076_, v_b_7077_, v___y_7079_, v___y_7080_, v___y_7081_, v___y_7082_);
return v___x_7084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7085_, lean_object* v_onAlt_7086_, lean_object* v_extraEqualities_7087_, lean_object* v_inst_7088_, lean_object* v_R_7089_, lean_object* v_a_7090_, lean_object* v_b_7091_, lean_object* v_c_7092_, lean_object* v___y_7093_, lean_object* v___y_7094_, lean_object* v___y_7095_, lean_object* v___y_7096_, lean_object* v___y_7097_){
_start:
{
lean_object* v_res_7098_; 
v_res_7098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7085_, v_onAlt_7086_, v_extraEqualities_7087_, v_inst_7088_, v_R_7089_, v_a_7090_, v_b_7091_, v_c_7092_, v___y_7093_, v___y_7094_, v___y_7095_, v___y_7096_);
lean_dec(v___y_7096_);
lean_dec_ref(v___y_7095_);
lean_dec(v___y_7094_);
lean_dec_ref(v___y_7093_);
lean_dec(v_upperBound_7085_);
return v_res_7098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7099_, lean_object* v_onAlt_7100_, uint8_t v_useSplitter_7101_, lean_object* v_extraEqualities_7102_, lean_object* v_numDiscrEqs_7103_, lean_object* v_inst_7104_, lean_object* v_R_7105_, lean_object* v_a_7106_, lean_object* v_b_7107_, lean_object* v_c_7108_, lean_object* v___y_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_, lean_object* v___y_7112_){
_start:
{
lean_object* v___x_7114_; 
v___x_7114_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7099_, v_onAlt_7100_, v_useSplitter_7101_, v_extraEqualities_7102_, v_numDiscrEqs_7103_, v_a_7106_, v_b_7107_, v___y_7109_, v___y_7110_, v___y_7111_, v___y_7112_);
return v___x_7114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7115_, lean_object* v_onAlt_7116_, lean_object* v_useSplitter_7117_, lean_object* v_extraEqualities_7118_, lean_object* v_numDiscrEqs_7119_, lean_object* v_inst_7120_, lean_object* v_R_7121_, lean_object* v_a_7122_, lean_object* v_b_7123_, lean_object* v_c_7124_, lean_object* v___y_7125_, lean_object* v___y_7126_, lean_object* v___y_7127_, lean_object* v___y_7128_, lean_object* v___y_7129_){
_start:
{
uint8_t v_useSplitter_boxed_7130_; lean_object* v_res_7131_; 
v_useSplitter_boxed_7130_ = lean_unbox(v_useSplitter_7117_);
v_res_7131_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7115_, v_onAlt_7116_, v_useSplitter_boxed_7130_, v_extraEqualities_7118_, v_numDiscrEqs_7119_, v_inst_7120_, v_R_7121_, v_a_7122_, v_b_7123_, v_c_7124_, v___y_7125_, v___y_7126_, v___y_7127_, v___y_7128_);
lean_dec(v___y_7128_);
lean_dec_ref(v___y_7127_);
lean_dec(v___y_7126_);
lean_dec_ref(v___y_7125_);
lean_dec(v_upperBound_7115_);
return v_res_7131_;
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
