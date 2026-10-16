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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_3911__boxed_142_; uint8_t v_refined_boxed_143_; lean_object* v_res_144_; 
v___x_3911__boxed_142_ = lean_unbox(v___x_132_);
v_refined_boxed_143_ = lean_unbox(v_refined_133_);
v_res_144_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_xs_130_, v_alt_131_, v___x_3911__boxed_142_, v_refined_boxed_143_, v_unrefinedArgType_134_, v_binderType_135_, v_x_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
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
uint8_t v___x_4087__boxed_300_; uint8_t v_refined_boxed_301_; lean_object* v_res_302_; 
v___x_4087__boxed_300_ = lean_unbox(v___x_288_);
v_refined_boxed_301_ = lean_unbox(v_refined_289_);
v_res_302_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4087__boxed_300_, v_refined_boxed_301_, v_unrefinedArgType_290_, v_binderType_291_, v_numParams_292_, v_xs_293_, v_alt_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_499_, lean_object* v_e_500_, lean_object* v_discrs_501_, lean_object* v_toMatcherInfo_502_, lean_object* v_matcherName_503_, lean_object* v_alts_504_, lean_object* v_params_505_, lean_object* v_remaining_506_, lean_object* v_matcherLevels_507_, lean_object* v_motiveArgs_508_, lean_object* v_motiveBody_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
uint8_t v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v_matcherLevels_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_659_ = lean_array_get_size(v_motiveArgs_508_);
v___x_660_ = lean_array_get_size(v_discrs_501_);
v___x_661_ = lean_nat_dec_eq(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v_motiveBody_509_);
lean_dec_ref(v_matcherLevels_507_);
lean_dec_ref(v_params_505_);
lean_dec_ref(v_alts_504_);
lean_dec(v_matcherName_503_);
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
v___x_531_ = lean_infer_type(v___y_520_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_a_532_);
lean_dec_ref_known(v___x_531_, 1);
v___x_533_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_499_);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_524_, v_a_532_, v___x_533_, v___y_518_, v___y_516_, v___x_534_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
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
v___x_543_ = l_Array_append___redArg(v___x_542_, v___y_526_);
v___x_544_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_544_, 0, v___y_523_);
lean_ctor_set(v___x_544_, 1, v___y_517_);
lean_ctor_set(v___x_544_, 2, v___y_525_);
lean_ctor_set(v___x_544_, 3, v___y_521_);
lean_ctor_set(v___x_544_, 4, v___y_519_);
lean_ctor_set(v___x_544_, 5, v___y_522_);
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
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_517_);
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
lean_dec_ref(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
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
v___x_582_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_508_, v___y_568_, v___x_579_, v___x_580_, v___x_579_, v___x_580_, v___x_581_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v_a_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_a_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc_n(v_a_583_, 2);
lean_dec_ref_known(v___x_582_, 1);
lean_inc_ref(v_matcherLevels_574_);
v___x_584_ = lean_array_to_list(v_matcherLevels_574_);
lean_inc(v___y_566_);
v___x_585_ = l_Lean_mkConst(v___y_566_, v___x_584_);
v___x_586_ = l_Lean_mkAppN(v___x_585_, v___y_569_);
v___x_587_ = l_Lean_Expr_app___override(v___x_586_, v_a_583_);
v___x_588_ = l_Lean_mkAppN(v___x_587_, v___y_572_);
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
lean_dec_ref(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
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
v___y_516_ = v___x_579_;
v___y_517_ = v___y_566_;
v___y_518_ = v___y_567_;
v___y_519_ = v_a_583_;
v___y_520_ = v___x_588_;
v___y_521_ = v___y_569_;
v___y_522_ = v___y_572_;
v___y_523_ = v___y_571_;
v___y_524_ = v___y_570_;
v___y_525_ = v_matcherLevels_574_;
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
lean_dec_ref(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
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
lean_dec_ref(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec_ref(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
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
v___y_566_ = v_matcherName_503_;
v___y_567_ = v_alts_504_;
v___y_568_ = v_a_629_;
v___y_569_ = v_params_505_;
v___y_570_ = v_a_624_;
v___y_571_ = v_toMatcherInfo_502_;
v___y_572_ = v_discrs_501_;
v___y_573_ = v_remaining_506_;
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
v___y_566_ = v_matcherName_503_;
v___y_567_ = v_alts_504_;
v___y_568_ = v_a_630_;
v___y_569_ = v_params_505_;
v___y_570_ = v_a_624_;
v___y_571_ = v_toMatcherInfo_502_;
v___y_572_ = v_discrs_501_;
v___y_573_ = v_remaining_506_;
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
lean_dec_ref(v_params_505_);
lean_dec_ref(v_alts_504_);
lean_dec(v_matcherName_503_);
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
lean_dec_ref(v_params_505_);
lean_dec_ref(v_alts_504_);
lean_dec(v_matcherName_503_);
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
lean_dec_ref(v_params_505_);
lean_dec_ref(v_alts_504_);
lean_dec(v_matcherName_503_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_678_, lean_object* v_e_679_, lean_object* v_discrs_680_, lean_object* v_toMatcherInfo_681_, lean_object* v_matcherName_682_, lean_object* v_alts_683_, lean_object* v_params_684_, lean_object* v_remaining_685_, lean_object* v_matcherLevels_686_, lean_object* v_motiveArgs_687_, lean_object* v_motiveBody_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_678_, v_e_679_, v_discrs_680_, v_toMatcherInfo_681_, v_matcherName_682_, v_alts_683_, v_params_684_, v_remaining_685_, v_matcherLevels_686_, v_motiveArgs_687_, v_motiveBody_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec_ref(v_motiveArgs_687_);
lean_dec_ref(v_remaining_685_);
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
lean_closure_set(v___f_710_, 4, v_matcherName_703_);
lean_closure_set(v___f_710_, 5, v_alts_708_);
lean_closure_set(v___f_710_, 6, v_params_705_);
lean_closure_set(v___f_710_, 7, v_remaining_709_);
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
lean_object* v___y_1110_; lean_object* v___y_1111_; uint8_t v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1114_; lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v_matcherLevels_1133_; lean_object* v___y_1134_; lean_object* v___y_1135_; lean_object* v___y_1136_; lean_object* v___y_1137_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
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
v___x_1117_ = lean_infer_type(v___y_1111_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v___x_1119_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_a_1118_, v___y_1110_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
return v___x_1119_;
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v___y_1110_);
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
v___x_1141_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1102_, v___y_1129_, v___x_1138_, v___x_1139_, v___x_1138_, v___x_1139_, v___x_1140_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
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
v___x_1147_ = l_Lean_mkAppN(v___x_1146_, v___y_1132_);
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
v___y_1110_ = v___f_1095_;
v___y_1111_ = v___x_1147_;
v___y_1112_ = v___x_1138_;
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
v___y_1129_ = v_a_1187_;
v___y_1130_ = v_matcherName_1099_;
v___y_1131_ = v_params_1100_;
v___y_1132_ = v_discrs_1096_;
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
v___y_1129_ = v_a_1188_;
v___y_1130_ = v_matcherName_1099_;
v___y_1131_ = v_params_1100_;
v___y_1132_ = v_discrs_1096_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2791_, lean_object* v___x_2792_, lean_object* v_toMonadExceptOf_2793_, uint8_t v___x_2794_, uint8_t v_useSplitter_2795_, lean_object* v_inst_2796_, lean_object* v_onAlt_2797_, lean_object* v_next_2798_, lean_object* v_toBind_2799_, lean_object* v___x_2800_, lean_object* v___f_2801_, lean_object* v_fst_2802_, lean_object* v_inst_2803_, lean_object* v_inst_2804_, lean_object* v_numDiscrEqs_2805_, lean_object* v___f_2806_, uint8_t v_hasUnitThunk_2807_, lean_object* v_toPure_2808_, lean_object* v___x_2809_, lean_object* v___x_2810_, lean_object* v_ys_2811_, lean_object* v_args_2812_){
_start:
{
lean_object* v_numFields_2813_; lean_object* v_numOverlaps_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_numFields_2813_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_numFields_2813_);
v_numOverlaps_2814_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_numOverlaps_2814_);
lean_dec_ref(v___x_2791_);
v___x_2815_ = lean_array_get_size(v_ys_2811_);
v___x_2816_ = lean_nat_dec_eq(v___x_2815_, v_numFields_2813_);
lean_dec(v_numFields_2813_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec(v_numOverlaps_2814_);
lean_dec_ref(v_args_2812_);
lean_dec_ref(v_ys_2811_);
lean_dec_ref(v___x_2810_);
lean_dec(v___x_2809_);
lean_dec(v_toPure_2808_);
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
lean_inc_ref(v_ys_2811_);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2821_, 0, v_toMonadExceptOf_2793_);
lean_closure_set(v___f_2821_, 1, v_ys_2811_);
lean_closure_set(v___f_2821_, 2, v___x_2819_);
lean_closure_set(v___f_2821_, 3, v___x_2820_);
lean_closure_set(v___f_2821_, 4, v_inst_2796_);
lean_closure_set(v___f_2821_, 5, v_args_2812_);
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
lean_closure_set(v___f_2823_, 0, v_numOverlaps_2814_);
lean_closure_set(v___f_2823_, 1, v_inst_2803_);
lean_closure_set(v___f_2823_, 2, v_inst_2804_);
lean_closure_set(v___f_2823_, 3, v___f_2821_);
lean_closure_set(v___f_2823_, 4, v___x_2822_);
lean_closure_set(v___f_2823_, 5, v_toBind_2799_);
lean_closure_set(v___f_2823_, 6, v___f_2806_);
v___f_2824_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2824_, 0, v___f_2823_);
v___x_2825_ = lean_box(v_hasUnitThunk_2807_);
lean_inc_ref(v___f_2824_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2826_, 0, v___x_2825_);
lean_closure_set(v___f_2826_, 1, v_toPure_2808_);
lean_closure_set(v___f_2826_, 2, v_toBind_2799_);
lean_closure_set(v___f_2826_, 3, v___f_2824_);
lean_closure_set(v___f_2826_, 4, v___x_2809_);
lean_closure_set(v___f_2826_, 5, v_inst_2796_);
lean_closure_set(v___f_2826_, 6, v___f_2824_);
v___x_2827_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2827_, 0, v___x_2810_);
lean_closure_set(v___x_2827_, 1, v_ys_2811_);
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
lean_object* v_hasUnitThunk_2846_ = _args[16];
lean_object* v_toPure_2847_ = _args[17];
lean_object* v___x_2848_ = _args[18];
lean_object* v___x_2849_ = _args[19];
lean_object* v_ys_2850_ = _args[20];
lean_object* v_args_2851_ = _args[21];
_start:
{
uint8_t v___x_13607__boxed_2852_; uint8_t v_useSplitter_boxed_2853_; uint8_t v_hasUnitThunk_boxed_2854_; lean_object* v_res_2855_; 
v___x_13607__boxed_2852_ = lean_unbox(v___x_2833_);
v_useSplitter_boxed_2853_ = lean_unbox(v_useSplitter_2834_);
v_hasUnitThunk_boxed_2854_ = lean_unbox(v_hasUnitThunk_2846_);
v_res_2855_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2830_, v___x_2831_, v_toMonadExceptOf_2832_, v___x_13607__boxed_2852_, v_useSplitter_boxed_2853_, v_inst_2835_, v_onAlt_2836_, v_next_2837_, v_toBind_2838_, v___x_2839_, v___f_2840_, v_fst_2841_, v_inst_2842_, v_inst_2843_, v_numDiscrEqs_2844_, v___f_2845_, v_hasUnitThunk_boxed_2854_, v_toPure_2847_, v___x_2848_, v___x_2849_, v_ys_2850_, v_args_2851_);
lean_dec(v___x_2831_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v_fst_2856_, lean_object* v___x_2857_, lean_object* v___x_2858_, lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v___x_2861_, lean_object* v_toPure_2862_, lean_object* v_alt_x27_2863_){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2864_ = lean_array_push(v_fst_2856_, v_alt_x27_2863_);
v___x_2865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2857_);
lean_ctor_set(v___x_2865_, 1, v___x_2858_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2859_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2860_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2861_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2864_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
v___x_2871_ = lean_apply_2(v_toPure_2862_, lean_box(0), v___x_2870_);
return v___x_2871_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2873_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0));
v___x_2874_ = lean_unsigned_to_nat(6u);
v___x_2875_ = lean_unsigned_to_nat(361u);
v___x_2876_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2877_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2878_ = l_mkPanicMessageWithDecl(v___x_2877_, v___x_2876_, v___x_2875_, v___x_2874_, v___x_2873_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2879_, lean_object* v_toPure_2880_, lean_object* v_toBind_2881_, lean_object* v___f_2882_, lean_object* v___x_2883_, lean_object* v___x_2884_, lean_object* v_inst_2885_, lean_object* v___x_2886_, lean_object* v_toMonadExceptOf_2887_, uint8_t v___x_2888_, uint8_t v_useSplitter_2889_, lean_object* v_onAlt_2890_, lean_object* v___f_2891_, lean_object* v_fst_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_numDiscrEqs_2895_, lean_object* v_next_2896_, lean_object* v_acc_2897_, lean_object* v_h_2898_, lean_object* v_G_2899_){
_start:
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_nat_dec_lt(v_next_2896_, v___x_2879_);
if (v___x_2900_ == 0)
{
lean_object* v___x_2901_; 
lean_dec(v_G_2899_);
lean_dec(v_next_2896_);
lean_dec(v_numDiscrEqs_2895_);
lean_dec_ref(v_inst_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec(v_fst_2892_);
lean_dec(v___f_2891_);
lean_dec(v_onAlt_2890_);
lean_dec_ref(v_toMonadExceptOf_2887_);
lean_dec(v___x_2886_);
lean_dec(v_inst_2885_);
lean_dec(v___f_2882_);
lean_dec(v_toBind_2881_);
v___x_2901_ = lean_apply_2(v_toPure_2880_, lean_box(0), v_acc_2897_);
return v___x_2901_;
}
else
{
lean_object* v_snd_2902_; lean_object* v_snd_2903_; lean_object* v_snd_2904_; lean_object* v_snd_2905_; lean_object* v_snd_2906_; lean_object* v_fst_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_3119_; 
v_snd_2902_ = lean_ctor_get(v_acc_2897_, 1);
lean_inc(v_snd_2902_);
v_snd_2903_ = lean_ctor_get(v_snd_2902_, 1);
lean_inc(v_snd_2903_);
v_snd_2904_ = lean_ctor_get(v_snd_2903_, 1);
lean_inc(v_snd_2904_);
v_snd_2905_ = lean_ctor_get(v_snd_2904_, 1);
lean_inc(v_snd_2905_);
v_snd_2906_ = lean_ctor_get(v_snd_2905_, 1);
lean_inc(v_snd_2906_);
v_fst_2907_ = lean_ctor_get(v_acc_2897_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_acc_2897_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v_acc_2897_, 1);
lean_dec(v_unused_3120_);
v___x_2909_ = v_acc_2897_;
v_isShared_2910_ = v_isSharedCheck_3119_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_fst_2907_);
lean_dec(v_acc_2897_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_3119_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_fst_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3117_; 
v_fst_2911_ = lean_ctor_get(v_snd_2902_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_snd_2902_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v_snd_2902_, 1);
lean_dec(v_unused_3118_);
v___x_2913_ = v_snd_2902_;
v_isShared_2914_ = v_isSharedCheck_3117_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_fst_2911_);
lean_dec(v_snd_2902_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3117_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_fst_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_3115_; 
v_fst_2915_ = lean_ctor_get(v_snd_2903_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_snd_2903_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v_snd_2903_, 1);
lean_dec(v_unused_3116_);
v___x_2917_ = v_snd_2903_;
v_isShared_2918_ = v_isSharedCheck_3115_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_fst_2915_);
lean_dec(v_snd_2903_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_3115_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_fst_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_3113_; 
v_fst_2919_ = lean_ctor_get(v_snd_2904_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_snd_2904_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v_snd_2904_, 1);
lean_dec(v_unused_3114_);
v___x_2921_ = v_snd_2904_;
v_isShared_2922_ = v_isSharedCheck_3113_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_fst_2919_);
lean_dec(v_snd_2904_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_3113_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v_fst_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_3111_; 
v_fst_2923_ = lean_ctor_get(v_snd_2905_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_snd_2905_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v_snd_2905_, 1);
lean_dec(v_unused_3112_);
v___x_2925_ = v_snd_2905_;
v_isShared_2926_ = v_isSharedCheck_3111_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_fst_2923_);
lean_dec(v_snd_2905_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_3111_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v_array_2927_; lean_object* v_start_2928_; lean_object* v_stop_2929_; lean_object* v___f_2930_; lean_object* v___y_2932_; uint8_t v___x_2935_; 
v_array_2927_ = lean_ctor_get(v_snd_2906_, 0);
v_start_2928_ = lean_ctor_get(v_snd_2906_, 1);
v_stop_2929_ = lean_ctor_get(v_snd_2906_, 2);
lean_inc(v_next_2896_);
lean_inc(v_toPure_2880_);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_2930_, 0, v_toPure_2880_);
lean_closure_set(v___f_2930_, 1, v_next_2896_);
lean_closure_set(v___f_2930_, 2, v_G_2899_);
v___x_2935_ = lean_nat_dec_lt(v_start_2928_, v_stop_2929_);
if (v___x_2935_ == 0)
{
lean_object* v___x_2937_; 
lean_dec(v_next_2896_);
lean_dec(v_numDiscrEqs_2895_);
lean_dec_ref(v_inst_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec(v_fst_2892_);
lean_dec(v___f_2891_);
lean_dec(v_onAlt_2890_);
lean_dec_ref(v_toMonadExceptOf_2887_);
lean_dec(v___x_2886_);
lean_dec(v_inst_2885_);
if (v_isShared_2926_ == 0)
{
v___x_2937_ = v___x_2925_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_snd_2906_);
v___x_2937_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2939_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_2937_);
v___x_2939_ = v___x_2921_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_2951_, 1, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2941_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v___x_2939_);
v___x_2941_ = v___x_2917_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_fst_2915_);
lean_ctor_set(v_reuseFailAlloc_2950_, 1, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2943_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2941_);
v___x_2943_ = v___x_2913_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_fst_2911_);
lean_ctor_set(v_reuseFailAlloc_2949_, 1, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
lean_object* v___x_2945_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_2943_);
v___x_2945_ = v___x_2909_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_fst_2907_);
lean_ctor_set(v_reuseFailAlloc_2948_, 1, v___x_2943_);
v___x_2945_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
v___x_2947_ = lean_apply_2(v_toPure_2880_, lean_box(0), v___x_2946_);
v___y_2932_ = v___x_2947_;
goto v___jp_2931_;
}
}
}
}
}
}
else
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3107_; 
lean_inc(v_stop_2929_);
lean_inc(v_start_2928_);
lean_inc_ref(v_array_2927_);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_snd_2906_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; lean_object* v_unused_3109_; lean_object* v_unused_3110_; 
v_unused_3108_ = lean_ctor_get(v_snd_2906_, 2);
lean_dec(v_unused_3108_);
v_unused_3109_ = lean_ctor_get(v_snd_2906_, 1);
lean_dec(v_unused_3109_);
v_unused_3110_ = lean_ctor_get(v_snd_2906_, 0);
lean_dec(v_unused_3110_);
v___x_2954_ = v_snd_2906_;
v_isShared_2955_ = v_isSharedCheck_3107_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v_snd_2906_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3107_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v_array_2956_; lean_object* v_start_2957_; lean_object* v_stop_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2963_; 
v_array_2956_ = lean_ctor_get(v_fst_2923_, 0);
v_start_2957_ = lean_ctor_get(v_fst_2923_, 1);
v_stop_2958_ = lean_ctor_get(v_fst_2923_, 2);
v___x_2959_ = lean_array_fget(v_array_2927_, v_start_2928_);
v___x_2960_ = lean_unsigned_to_nat(1u);
v___x_2961_ = lean_nat_add(v_start_2928_, v___x_2960_);
lean_dec(v_start_2928_);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2961_);
v___x_2963_ = v___x_2954_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_array_2927_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v_stop_2929_);
v___x_2963_ = v_reuseFailAlloc_3106_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_nat_dec_lt(v_start_2957_, v_stop_2958_);
if (v___x_2964_ == 0)
{
lean_object* v___x_2966_; 
lean_dec(v___x_2959_);
lean_dec(v_next_2896_);
lean_dec(v_numDiscrEqs_2895_);
lean_dec_ref(v_inst_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec(v_fst_2892_);
lean_dec(v___f_2891_);
lean_dec(v_onAlt_2890_);
lean_dec_ref(v_toMonadExceptOf_2887_);
lean_dec(v___x_2886_);
lean_dec(v_inst_2885_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2963_);
v___x_2966_ = v___x_2925_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2923_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2963_);
v___x_2966_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
lean_object* v___x_2968_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_2966_);
v___x_2968_ = v___x_2921_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2966_);
v___x_2968_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2970_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v___x_2968_);
v___x_2970_ = v___x_2917_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_fst_2915_);
lean_ctor_set(v_reuseFailAlloc_2979_, 1, v___x_2968_);
v___x_2970_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2972_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2970_);
v___x_2972_ = v___x_2913_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v_fst_2911_);
lean_ctor_set(v_reuseFailAlloc_2978_, 1, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
lean_object* v___x_2974_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_2972_);
v___x_2974_ = v___x_2909_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_fst_2907_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
v___x_2976_ = lean_apply_2(v_toPure_2880_, lean_box(0), v___x_2975_);
v___y_2932_ = v___x_2976_;
goto v___jp_2931_;
}
}
}
}
}
}
else
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3102_; 
lean_inc(v_stop_2958_);
lean_inc(v_start_2957_);
lean_inc_ref(v_array_2956_);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_fst_2923_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; lean_object* v_unused_3104_; lean_object* v_unused_3105_; 
v_unused_3103_ = lean_ctor_get(v_fst_2923_, 2);
lean_dec(v_unused_3103_);
v_unused_3104_ = lean_ctor_get(v_fst_2923_, 1);
lean_dec(v_unused_3104_);
v_unused_3105_ = lean_ctor_get(v_fst_2923_, 0);
lean_dec(v_unused_3105_);
v___x_2983_ = v_fst_2923_;
v_isShared_2984_ = v_isSharedCheck_3102_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v_fst_2923_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3102_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_array_2985_; lean_object* v_start_2986_; lean_object* v_stop_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v_array_2985_ = lean_ctor_get(v_fst_2919_, 0);
v_start_2986_ = lean_ctor_get(v_fst_2919_, 1);
v_stop_2987_ = lean_ctor_get(v_fst_2919_, 2);
v___x_2988_ = lean_array_fget(v_array_2956_, v_start_2957_);
v___x_2989_ = lean_nat_add(v_start_2957_, v___x_2960_);
lean_dec(v_start_2957_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 1, v___x_2989_);
v___x_2991_ = v___x_2983_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_array_2956_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3101_, 2, v_stop_2958_);
v___x_2991_ = v_reuseFailAlloc_3101_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
uint8_t v___x_2992_; 
v___x_2992_ = lean_nat_dec_lt(v_start_2986_, v_stop_2987_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2994_; 
lean_dec(v___x_2988_);
lean_dec(v___x_2959_);
lean_dec(v_next_2896_);
lean_dec(v_numDiscrEqs_2895_);
lean_dec_ref(v_inst_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec(v_fst_2892_);
lean_dec(v___f_2891_);
lean_dec(v_onAlt_2890_);
lean_dec_ref(v_toMonadExceptOf_2887_);
lean_dec(v___x_2886_);
lean_dec(v_inst_2885_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2963_);
lean_ctor_set(v___x_2925_, 0, v___x_2991_);
v___x_2994_ = v___x_2925_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_2963_);
v___x_2994_ = v_reuseFailAlloc_3009_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2996_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_2994_);
v___x_2996_ = v___x_2921_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_fst_2919_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v___x_2994_);
v___x_2996_ = v_reuseFailAlloc_3008_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
lean_object* v___x_2998_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v___x_2996_);
v___x_2998_ = v___x_2917_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_fst_2915_);
lean_ctor_set(v_reuseFailAlloc_3007_, 1, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_3007_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_3000_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_2998_);
v___x_3000_ = v___x_2913_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_fst_2911_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3002_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_3000_);
v___x_3002_ = v___x_2909_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_fst_2907_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v___x_3002_);
v___x_3004_ = lean_apply_2(v_toPure_2880_, lean_box(0), v___x_3003_);
v___y_2932_ = v___x_3004_;
goto v___jp_2931_;
}
}
}
}
}
}
else
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3097_; 
lean_inc(v_stop_2987_);
lean_inc(v_start_2986_);
lean_inc_ref(v_array_2985_);
v_isSharedCheck_3097_ = !lean_is_exclusive(v_fst_2919_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; lean_object* v_unused_3099_; lean_object* v_unused_3100_; 
v_unused_3098_ = lean_ctor_get(v_fst_2919_, 2);
lean_dec(v_unused_3098_);
v_unused_3099_ = lean_ctor_get(v_fst_2919_, 1);
lean_dec(v_unused_3099_);
v_unused_3100_ = lean_ctor_get(v_fst_2919_, 0);
lean_dec(v_unused_3100_);
v___x_3011_ = v_fst_2919_;
v_isShared_3012_ = v_isSharedCheck_3097_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v_fst_2919_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3097_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v_array_3013_; lean_object* v_start_3014_; lean_object* v_stop_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v_array_3013_ = lean_ctor_get(v_fst_2915_, 0);
v_start_3014_ = lean_ctor_get(v_fst_2915_, 1);
v_stop_3015_ = lean_ctor_get(v_fst_2915_, 2);
v___x_3016_ = lean_array_fget(v_array_2985_, v_start_2986_);
v___x_3017_ = lean_nat_add(v_start_2986_, v___x_2960_);
lean_dec(v_start_2986_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v___x_3017_);
v___x_3019_ = v___x_3011_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_array_2985_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3096_, 2, v_stop_2987_);
v___x_3019_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_nat_dec_lt(v_start_3014_, v_stop_3015_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3022_; 
lean_dec(v___x_3016_);
lean_dec(v___x_2988_);
lean_dec(v___x_2959_);
lean_dec(v_next_2896_);
lean_dec(v_numDiscrEqs_2895_);
lean_dec_ref(v_inst_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec(v_fst_2892_);
lean_dec(v___f_2891_);
lean_dec(v_onAlt_2890_);
lean_dec_ref(v_toMonadExceptOf_2887_);
lean_dec(v___x_2886_);
lean_dec(v_inst_2885_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2963_);
lean_ctor_set(v___x_2925_, 0, v___x_2991_);
v___x_3022_ = v___x_2925_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_2963_);
v___x_3022_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
lean_object* v___x_3024_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_3022_);
lean_ctor_set(v___x_2921_, 0, v___x_3019_);
v___x_3024_ = v___x_2921_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3022_);
v___x_3024_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3026_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v___x_3024_);
v___x_3026_ = v___x_2917_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_fst_2915_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_3026_);
v___x_3028_ = v___x_2913_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_fst_2911_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_3028_);
v___x_3030_ = v___x_2909_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_fst_2907_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
v___x_3032_ = lean_apply_2(v_toPure_2880_, lean_box(0), v___x_3031_);
v___y_2932_ = v___x_3032_;
goto v___jp_2931_;
}
}
}
}
}
}
else
{
lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3092_; 
lean_inc(v_stop_3015_);
lean_inc(v_start_3014_);
lean_inc_ref(v_array_3013_);
v_isSharedCheck_3092_ = !lean_is_exclusive(v_fst_2915_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; lean_object* v_unused_3094_; lean_object* v_unused_3095_; 
v_unused_3093_ = lean_ctor_get(v_fst_2915_, 2);
lean_dec(v_unused_3093_);
v_unused_3094_ = lean_ctor_get(v_fst_2915_, 1);
lean_dec(v_unused_3094_);
v_unused_3095_ = lean_ctor_get(v_fst_2915_, 0);
lean_dec(v_unused_3095_);
v___x_3039_ = v_fst_2915_;
v_isShared_3040_ = v_isSharedCheck_3092_;
goto v_resetjp_3038_;
}
else
{
lean_dec(v_fst_2915_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3092_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_array_3041_; lean_object* v_start_3042_; lean_object* v_stop_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3047_; 
v_array_3041_ = lean_ctor_get(v_fst_2911_, 0);
v_start_3042_ = lean_ctor_get(v_fst_2911_, 1);
v_stop_3043_ = lean_ctor_get(v_fst_2911_, 2);
v___x_3044_ = lean_array_fget(v_array_3013_, v_start_3014_);
v___x_3045_ = lean_nat_add(v_start_3014_, v___x_2960_);
lean_dec(v_start_3014_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 1, v___x_3045_);
v___x_3047_ = v___x_3039_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_array_3013_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_stop_3015_);
v___x_3047_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_nat_dec_lt(v_start_3042_, v_stop_3043_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3050_; 
lean_dec(v___x_3044_);
lean_dec(v___x_3016_);
lean_dec(v___x_2988_);
lean_dec(v___x_2959_);
lean_dec(v_next_2896_);
lean_dec(v_numDiscrEqs_2895_);
lean_dec_ref(v_inst_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec(v_fst_2892_);
lean_dec(v___f_2891_);
lean_dec(v_onAlt_2890_);
lean_dec_ref(v_toMonadExceptOf_2887_);
lean_dec(v___x_2886_);
lean_dec(v_inst_2885_);
if (v_isShared_2926_ == 0)
{
lean_ctor_set(v___x_2925_, 1, v___x_2963_);
lean_ctor_set(v___x_2925_, 0, v___x_2991_);
v___x_3050_ = v___x_2925_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_2963_);
v___x_3050_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3052_; 
if (v_isShared_2922_ == 0)
{
lean_ctor_set(v___x_2921_, 1, v___x_3050_);
lean_ctor_set(v___x_2921_, 0, v___x_3019_);
v___x_3052_ = v___x_2921_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3019_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v___x_3050_);
v___x_3052_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3054_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 1, v___x_3052_);
lean_ctor_set(v___x_2917_, 0, v___x_3047_);
v___x_3054_ = v___x_2917_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3063_, 1, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3056_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 1, v___x_3054_);
v___x_3056_ = v___x_2913_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_fst_2911_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3058_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 1, v___x_3056_);
v___x_3058_ = v___x_2909_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_fst_2907_);
lean_ctor_set(v_reuseFailAlloc_3061_, 1, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
v___x_3060_ = lean_apply_2(v_toPure_2880_, lean_box(0), v___x_3059_);
v___y_2932_ = v___x_3060_;
goto v___jp_2931_;
}
}
}
}
}
}
else
{
lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3087_; 
lean_inc(v_stop_3043_);
lean_inc(v_start_3042_);
lean_inc_ref(v_array_3041_);
lean_del_object(v___x_2925_);
lean_del_object(v___x_2921_);
lean_del_object(v___x_2917_);
lean_del_object(v___x_2913_);
lean_del_object(v___x_2909_);
v_isSharedCheck_3087_ = !lean_is_exclusive(v_fst_2911_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; lean_object* v_unused_3089_; lean_object* v_unused_3090_; 
v_unused_3088_ = lean_ctor_get(v_fst_2911_, 2);
lean_dec(v_unused_3088_);
v_unused_3089_ = lean_ctor_get(v_fst_2911_, 1);
lean_dec(v_unused_3089_);
v_unused_3090_ = lean_ctor_get(v_fst_2911_, 0);
lean_dec(v_unused_3090_);
v___x_3067_ = v_fst_2911_;
v_isShared_3068_ = v_isSharedCheck_3087_;
goto v_resetjp_3066_;
}
else
{
lean_dec(v_fst_2911_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3087_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v_numOverlaps_3069_; uint8_t v_hasUnitThunk_3070_; uint8_t v___x_3071_; 
v_numOverlaps_3069_ = lean_ctor_get(v___x_3044_, 1);
v_hasUnitThunk_3070_ = lean_ctor_get_uint8(v___x_3044_, sizeof(void*)*2);
v___x_3071_ = lean_nat_dec_eq(v_numOverlaps_3069_, v___x_2883_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_del_object(v___x_3067_);
lean_dec_ref(v___x_3047_);
lean_dec(v___x_3044_);
lean_dec(v_stop_3043_);
lean_dec(v_start_3042_);
lean_dec_ref(v_array_3041_);
lean_dec_ref(v___x_3019_);
lean_dec(v___x_3016_);
lean_dec_ref(v___x_2991_);
lean_dec(v___x_2988_);
lean_dec_ref(v___x_2963_);
lean_dec(v___x_2959_);
lean_dec(v_fst_2907_);
lean_dec(v_next_2896_);
lean_dec(v_numDiscrEqs_2895_);
lean_dec_ref(v_inst_2894_);
lean_dec_ref(v_inst_2893_);
lean_dec(v_fst_2892_);
lean_dec(v___f_2891_);
lean_dec(v_onAlt_2890_);
lean_dec_ref(v_toMonadExceptOf_2887_);
lean_dec(v___x_2886_);
lean_dec(v_inst_2885_);
lean_dec(v_toPure_2880_);
v___x_3072_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_3073_ = l_panic___redArg(v___x_2884_, v___x_3072_);
v___y_2932_ = v___x_3073_;
goto v___jp_2931_;
}
else
{
lean_object* v___f_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
lean_inc(v_inst_2885_);
lean_inc_n(v_toPure_2880_, 2);
lean_inc(v___x_3016_);
v___f_3074_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_3074_, 0, v___x_3016_);
lean_closure_set(v___f_3074_, 1, v_toPure_2880_);
lean_closure_set(v___f_3074_, 2, v_inst_2885_);
v___x_3075_ = lean_array_fget_borrowed(v_array_3041_, v_start_3042_);
v___x_3076_ = lean_box(v___x_2888_);
v___x_3077_ = lean_box(v_useSplitter_2889_);
v___x_3078_ = lean_box(v_hasUnitThunk_3070_);
lean_inc_ref(v_inst_2894_);
lean_inc_ref(v_inst_2893_);
lean_inc(v___x_3075_);
lean_inc(v_toBind_2881_);
v___f_3079_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 22, 20);
lean_closure_set(v___f_3079_, 0, v___x_3016_);
lean_closure_set(v___f_3079_, 1, v___x_2886_);
lean_closure_set(v___f_3079_, 2, v_toMonadExceptOf_2887_);
lean_closure_set(v___f_3079_, 3, v___x_3076_);
lean_closure_set(v___f_3079_, 4, v___x_3077_);
lean_closure_set(v___f_3079_, 5, v_inst_2885_);
lean_closure_set(v___f_3079_, 6, v_onAlt_2890_);
lean_closure_set(v___f_3079_, 7, v_next_2896_);
lean_closure_set(v___f_3079_, 8, v_toBind_2881_);
lean_closure_set(v___f_3079_, 9, v___x_3075_);
lean_closure_set(v___f_3079_, 10, v___f_2891_);
lean_closure_set(v___f_3079_, 11, v_fst_2892_);
lean_closure_set(v___f_3079_, 12, v_inst_2893_);
lean_closure_set(v___f_3079_, 13, v_inst_2894_);
lean_closure_set(v___f_3079_, 14, v_numDiscrEqs_2895_);
lean_closure_set(v___f_3079_, 15, v___f_3074_);
lean_closure_set(v___f_3079_, 16, v___x_3078_);
lean_closure_set(v___f_3079_, 17, v_toPure_2880_);
lean_closure_set(v___f_3079_, 18, v___x_2960_);
lean_closure_set(v___f_3079_, 19, v___x_2959_);
v___x_3080_ = lean_nat_add(v_start_3042_, v___x_2960_);
lean_dec(v_start_3042_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 1, v___x_3080_);
v___x_3082_ = v___x_3067_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_array_3041_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_stop_3043_);
v___x_3082_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___f_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___f_3083_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3083_, 0, v_fst_2907_);
lean_closure_set(v___f_3083_, 1, v___x_2991_);
lean_closure_set(v___f_3083_, 2, v___x_2963_);
lean_closure_set(v___f_3083_, 3, v___x_3019_);
lean_closure_set(v___f_3083_, 4, v___x_3047_);
lean_closure_set(v___f_3083_, 5, v___x_3082_);
lean_closure_set(v___f_3083_, 6, v_toPure_2880_);
v___x_3084_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2894_, v_inst_2893_, v___x_2988_, v___x_3044_, v___f_3079_);
lean_inc(v_toBind_2881_);
v___x_3085_ = lean_apply_4(v_toBind_2881_, lean_box(0), lean_box(0), v___x_3084_, v___f_3083_);
v___y_2932_ = v___x_3085_;
goto v___jp_2931_;
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
v___jp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
lean_inc(v_toBind_2881_);
v___x_2933_ = lean_apply_4(v_toBind_2881_, lean_box(0), lean_box(0), v___y_2932_, v___f_2882_);
v___x_2934_ = lean_apply_4(v_toBind_2881_, lean_box(0), lean_box(0), v___x_2933_, v___f_2930_);
return v___x_2934_;
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
lean_object* v___x_3121_ = _args[0];
lean_object* v_toPure_3122_ = _args[1];
lean_object* v_toBind_3123_ = _args[2];
lean_object* v___f_3124_ = _args[3];
lean_object* v___x_3125_ = _args[4];
lean_object* v___x_3126_ = _args[5];
lean_object* v_inst_3127_ = _args[6];
lean_object* v___x_3128_ = _args[7];
lean_object* v_toMonadExceptOf_3129_ = _args[8];
lean_object* v___x_3130_ = _args[9];
lean_object* v_useSplitter_3131_ = _args[10];
lean_object* v_onAlt_3132_ = _args[11];
lean_object* v___f_3133_ = _args[12];
lean_object* v_fst_3134_ = _args[13];
lean_object* v_inst_3135_ = _args[14];
lean_object* v_inst_3136_ = _args[15];
lean_object* v_numDiscrEqs_3137_ = _args[16];
lean_object* v_next_3138_ = _args[17];
lean_object* v_acc_3139_ = _args[18];
lean_object* v_h_3140_ = _args[19];
lean_object* v_G_3141_ = _args[20];
_start:
{
uint8_t v___x_13725__boxed_3142_; uint8_t v_useSplitter_boxed_3143_; lean_object* v_res_3144_; 
v___x_13725__boxed_3142_ = lean_unbox(v___x_3130_);
v_useSplitter_boxed_3143_ = lean_unbox(v_useSplitter_3131_);
v_res_3144_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3121_, v_toPure_3122_, v_toBind_3123_, v___f_3124_, v___x_3125_, v___x_3126_, v_inst_3127_, v___x_3128_, v_toMonadExceptOf_3129_, v___x_13725__boxed_3142_, v_useSplitter_boxed_3143_, v_onAlt_3132_, v___f_3133_, v_fst_3134_, v_inst_3135_, v_inst_3136_, v_numDiscrEqs_3137_, v_next_3138_, v_acc_3139_, v_h_3140_, v_G_3141_);
lean_dec(v___x_3126_);
lean_dec(v___x_3125_);
lean_dec(v___x_3121_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3145_, lean_object* v_numParams_3146_, lean_object* v_numDiscrs_3147_, lean_object* v_altInfos_3148_, lean_object* v_uElimPos_x3f_3149_, lean_object* v_snd_3150_, lean_object* v_overlaps_3151_, lean_object* v_splitterName_3152_, lean_object* v_matcherLevels_3153_, lean_object* v_params_x27_3154_, lean_object* v_fst_3155_, lean_object* v_discrs_x27_3156_, lean_object* v_fst_3157_, lean_object* v_toPure_3158_, lean_object* v_____do__lift_3159_){
_start:
{
lean_object* v_remaining_x27_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v_remaining_x27_3160_ = l_Array_append___redArg(v_fst_3145_, v_____do__lift_3159_);
v___x_3161_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3161_, 0, v_numParams_3146_);
lean_ctor_set(v___x_3161_, 1, v_numDiscrs_3147_);
lean_ctor_set(v___x_3161_, 2, v_altInfos_3148_);
lean_ctor_set(v___x_3161_, 3, v_uElimPos_x3f_3149_);
lean_ctor_set(v___x_3161_, 4, v_snd_3150_);
lean_ctor_set(v___x_3161_, 5, v_overlaps_3151_);
v___x_3162_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
lean_ctor_set(v___x_3162_, 1, v_splitterName_3152_);
lean_ctor_set(v___x_3162_, 2, v_matcherLevels_3153_);
lean_ctor_set(v___x_3162_, 3, v_params_x27_3154_);
lean_ctor_set(v___x_3162_, 4, v_fst_3155_);
lean_ctor_set(v___x_3162_, 5, v_discrs_x27_3156_);
lean_ctor_set(v___x_3162_, 6, v_fst_3157_);
lean_ctor_set(v___x_3162_, 7, v_remaining_x27_3160_);
v___x_3163_ = lean_apply_2(v_toPure_3158_, lean_box(0), v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3164_, lean_object* v_numParams_3165_, lean_object* v_numDiscrs_3166_, lean_object* v_altInfos_3167_, lean_object* v_uElimPos_x3f_3168_, lean_object* v_snd_3169_, lean_object* v_overlaps_3170_, lean_object* v_splitterName_3171_, lean_object* v_matcherLevels_3172_, lean_object* v_params_x27_3173_, lean_object* v_fst_3174_, lean_object* v_discrs_x27_3175_, lean_object* v_fst_3176_, lean_object* v_toPure_3177_, lean_object* v_____do__lift_3178_){
_start:
{
lean_object* v_res_3179_; 
v_res_3179_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3164_, v_numParams_3165_, v_numDiscrs_3166_, v_altInfos_3167_, v_uElimPos_x3f_3168_, v_snd_3169_, v_overlaps_3170_, v_splitterName_3171_, v_matcherLevels_3172_, v_params_x27_3173_, v_fst_3174_, v_discrs_x27_3175_, v_fst_3176_, v_toPure_3177_, v_____do__lift_3178_);
lean_dec_ref(v_____do__lift_3178_);
return v_res_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3180_, lean_object* v_numParams_3181_, lean_object* v_numDiscrs_3182_, lean_object* v_altInfos_3183_, lean_object* v_uElimPos_x3f_3184_, lean_object* v_snd_3185_, lean_object* v_overlaps_3186_, lean_object* v_splitterName_3187_, lean_object* v_matcherLevels_3188_, lean_object* v_params_x27_3189_, lean_object* v_fst_3190_, lean_object* v_discrs_x27_3191_, lean_object* v_toPure_3192_, lean_object* v_onRemaining_3193_, lean_object* v_remaining_3194_, lean_object* v_toBind_3195_, lean_object* v_____s_3196_){
_start:
{
lean_object* v_fst_3197_; lean_object* v___f_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_fst_3197_ = lean_ctor_get(v_____s_3196_, 0);
lean_inc(v_fst_3197_);
lean_dec_ref(v_____s_3196_);
v___f_3198_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3198_, 0, v_fst_3180_);
lean_closure_set(v___f_3198_, 1, v_numParams_3181_);
lean_closure_set(v___f_3198_, 2, v_numDiscrs_3182_);
lean_closure_set(v___f_3198_, 3, v_altInfos_3183_);
lean_closure_set(v___f_3198_, 4, v_uElimPos_x3f_3184_);
lean_closure_set(v___f_3198_, 5, v_snd_3185_);
lean_closure_set(v___f_3198_, 6, v_overlaps_3186_);
lean_closure_set(v___f_3198_, 7, v_splitterName_3187_);
lean_closure_set(v___f_3198_, 8, v_matcherLevels_3188_);
lean_closure_set(v___f_3198_, 9, v_params_x27_3189_);
lean_closure_set(v___f_3198_, 10, v_fst_3190_);
lean_closure_set(v___f_3198_, 11, v_discrs_x27_3191_);
lean_closure_set(v___f_3198_, 12, v_fst_3197_);
lean_closure_set(v___f_3198_, 13, v_toPure_3192_);
v___x_3199_ = lean_apply_1(v_onRemaining_3193_, v_remaining_3194_);
v___x_3200_ = lean_apply_4(v_toBind_3195_, lean_box(0), lean_box(0), v___x_3199_, v___f_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3201_ = _args[0];
lean_object* v_numParams_3202_ = _args[1];
lean_object* v_numDiscrs_3203_ = _args[2];
lean_object* v_altInfos_3204_ = _args[3];
lean_object* v_uElimPos_x3f_3205_ = _args[4];
lean_object* v_snd_3206_ = _args[5];
lean_object* v_overlaps_3207_ = _args[6];
lean_object* v_splitterName_3208_ = _args[7];
lean_object* v_matcherLevels_3209_ = _args[8];
lean_object* v_params_x27_3210_ = _args[9];
lean_object* v_fst_3211_ = _args[10];
lean_object* v_discrs_x27_3212_ = _args[11];
lean_object* v_toPure_3213_ = _args[12];
lean_object* v_onRemaining_3214_ = _args[13];
lean_object* v_remaining_3215_ = _args[14];
lean_object* v_toBind_3216_ = _args[15];
lean_object* v_____s_3217_ = _args[16];
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3201_, v_numParams_3202_, v_numDiscrs_3203_, v_altInfos_3204_, v_uElimPos_x3f_3205_, v_snd_3206_, v_overlaps_3207_, v_splitterName_3208_, v_matcherLevels_3209_, v_params_x27_3210_, v_fst_3211_, v_discrs_x27_3212_, v_toPure_3213_, v_onRemaining_3214_, v_remaining_3215_, v_toBind_3216_, v_____s_3217_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3219_, lean_object* v_fst_3220_, lean_object* v_numParams_3221_, lean_object* v_numDiscrs_3222_, lean_object* v_altInfos_3223_, lean_object* v_uElimPos_x3f_3224_, lean_object* v_snd_3225_, lean_object* v_overlaps_3226_, lean_object* v_splitterName_3227_, lean_object* v_matcherLevels_3228_, lean_object* v_params_x27_3229_, lean_object* v_fst_3230_, lean_object* v_discrs_x27_3231_, lean_object* v_toPure_3232_, lean_object* v_onRemaining_3233_, lean_object* v_remaining_3234_, lean_object* v_toBind_3235_, lean_object* v_origAltTypes_3236_, lean_object* v_alts_3237_, lean_object* v___x_3238_, lean_object* v___x_3239_, lean_object* v_remaining_x27_3240_, lean_object* v___f_3241_, lean_object* v_altTypes_3242_){
_start:
{
lean_object* v_altInfos_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v_altInfos_3243_ = lean_ctor_get(v_splitterMatchInfo_3219_, 2);
lean_inc_ref(v_altInfos_3243_);
lean_dec_ref(v_splitterMatchInfo_3219_);
lean_inc(v_toBind_3235_);
lean_inc_ref(v_altInfos_3223_);
v___f_3244_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3244_, 0, v_fst_3220_);
lean_closure_set(v___f_3244_, 1, v_numParams_3221_);
lean_closure_set(v___f_3244_, 2, v_numDiscrs_3222_);
lean_closure_set(v___f_3244_, 3, v_altInfos_3223_);
lean_closure_set(v___f_3244_, 4, v_uElimPos_x3f_3224_);
lean_closure_set(v___f_3244_, 5, v_snd_3225_);
lean_closure_set(v___f_3244_, 6, v_overlaps_3226_);
lean_closure_set(v___f_3244_, 7, v_splitterName_3227_);
lean_closure_set(v___f_3244_, 8, v_matcherLevels_3228_);
lean_closure_set(v___f_3244_, 9, v_params_x27_3229_);
lean_closure_set(v___f_3244_, 10, v_fst_3230_);
lean_closure_set(v___f_3244_, 11, v_discrs_x27_3231_);
lean_closure_set(v___f_3244_, 12, v_toPure_3232_);
lean_closure_set(v___f_3244_, 13, v_onRemaining_3233_);
lean_closure_set(v___f_3244_, 14, v_remaining_3234_);
lean_closure_set(v___f_3244_, 15, v_toBind_3235_);
v___x_3245_ = lean_array_get_size(v_altInfos_3223_);
v___x_3246_ = lean_array_get_size(v_altInfos_3243_);
v___x_3247_ = lean_array_get_size(v_origAltTypes_3236_);
v___x_3248_ = lean_array_get_size(v_altTypes_3242_);
lean_inc_n(v___x_3238_, 5);
v___x_3249_ = l_Array_toSubarray___redArg(v_alts_3237_, v___x_3238_, v___x_3239_);
v___x_3250_ = l_Array_toSubarray___redArg(v_altInfos_3223_, v___x_3238_, v___x_3245_);
v___x_3251_ = l_Array_toSubarray___redArg(v_altInfos_3243_, v___x_3238_, v___x_3246_);
v___x_3252_ = l_Array_toSubarray___redArg(v_origAltTypes_3236_, v___x_3238_, v___x_3247_);
v___x_3253_ = l_Array_toSubarray___redArg(v_altTypes_3242_, v___x_3238_, v___x_3248_);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3252_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3251_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3250_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3249_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3258_, 0, v_remaining_x27_3240_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___x_3259_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3241_, v___x_3238_, v___x_3258_, lean_box(0));
v___x_3260_ = lean_apply_4(v_toBind_3235_, lean_box(0), lean_box(0), v___x_3259_, v___f_3244_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3261_ = _args[0];
lean_object* v_fst_3262_ = _args[1];
lean_object* v_numParams_3263_ = _args[2];
lean_object* v_numDiscrs_3264_ = _args[3];
lean_object* v_altInfos_3265_ = _args[4];
lean_object* v_uElimPos_x3f_3266_ = _args[5];
lean_object* v_snd_3267_ = _args[6];
lean_object* v_overlaps_3268_ = _args[7];
lean_object* v_splitterName_3269_ = _args[8];
lean_object* v_matcherLevels_3270_ = _args[9];
lean_object* v_params_x27_3271_ = _args[10];
lean_object* v_fst_3272_ = _args[11];
lean_object* v_discrs_x27_3273_ = _args[12];
lean_object* v_toPure_3274_ = _args[13];
lean_object* v_onRemaining_3275_ = _args[14];
lean_object* v_remaining_3276_ = _args[15];
lean_object* v_toBind_3277_ = _args[16];
lean_object* v_origAltTypes_3278_ = _args[17];
lean_object* v_alts_3279_ = _args[18];
lean_object* v___x_3280_ = _args[19];
lean_object* v___x_3281_ = _args[20];
lean_object* v_remaining_x27_3282_ = _args[21];
lean_object* v___f_3283_ = _args[22];
lean_object* v_altTypes_3284_ = _args[23];
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3261_, v_fst_3262_, v_numParams_3263_, v_numDiscrs_3264_, v_altInfos_3265_, v_uElimPos_x3f_3266_, v_snd_3267_, v_overlaps_3268_, v_splitterName_3269_, v_matcherLevels_3270_, v_params_x27_3271_, v_fst_3272_, v_discrs_x27_3273_, v_toPure_3274_, v_onRemaining_3275_, v_remaining_3276_, v_toBind_3277_, v_origAltTypes_3278_, v_alts_3279_, v___x_3280_, v___x_3281_, v_remaining_x27_3282_, v___f_3283_, v_altTypes_3284_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3286_, lean_object* v_aux2_3287_, lean_object* v_inst_3288_, lean_object* v_toBind_3289_, lean_object* v___f_3290_, lean_object* v_____r_3291_){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3292_, 0, v___x_3286_);
lean_closure_set(v___x_3292_, 1, v_aux2_3287_);
v___x_3293_ = lean_apply_2(v_inst_3288_, lean_box(0), v___x_3292_);
v___x_3294_ = lean_apply_4(v_toBind_3289_, lean_box(0), lean_box(0), v___x_3293_, v___f_3290_);
return v___x_3294_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3296_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3297_ = l_Lean_stringToMessageData(v___x_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3298_, lean_object* v_params_x27_3299_, lean_object* v_fst_3300_, lean_object* v_discrs_x27_3301_, lean_object* v_fst_3302_, lean_object* v_numParams_3303_, lean_object* v_numDiscrs_3304_, lean_object* v_altInfos_3305_, lean_object* v_uElimPos_x3f_3306_, lean_object* v_snd_3307_, lean_object* v_overlaps_3308_, lean_object* v_matcherLevels_3309_, lean_object* v_toPure_3310_, lean_object* v_onRemaining_3311_, lean_object* v_remaining_3312_, lean_object* v_toBind_3313_, lean_object* v_origAltTypes_3314_, lean_object* v_alts_3315_, lean_object* v___x_3316_, lean_object* v___x_3317_, lean_object* v_remaining_x27_3318_, lean_object* v___f_3319_, lean_object* v_inst_3320_, lean_object* v___x_3321_, uint8_t v___x_3322_, lean_object* v_liftWith_3323_, lean_object* v_restoreM_3324_, lean_object* v_matchEqns_3325_){
_start:
{
lean_object* v_splitterName_3326_; lean_object* v_splitterMatchInfo_3327_; lean_object* v___x_3328_; lean_object* v_aux2_3329_; lean_object* v_aux2_3330_; lean_object* v_aux2_3331_; lean_object* v___x_3332_; lean_object* v___f_3333_; lean_object* v___f_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___f_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_splitterName_3326_ = lean_ctor_get(v_matchEqns_3325_, 1);
lean_inc_n(v_splitterName_3326_, 2);
v_splitterMatchInfo_3327_ = lean_ctor_get(v_matchEqns_3325_, 2);
lean_inc_ref(v_splitterMatchInfo_3327_);
lean_dec_ref(v_matchEqns_3325_);
v___x_3328_ = l_Lean_mkConst(v_splitterName_3326_, v___x_3298_);
v_aux2_3329_ = l_Lean_mkAppN(v___x_3328_, v_params_x27_3299_);
lean_inc_ref(v_fst_3300_);
v_aux2_3330_ = l_Lean_Expr_app___override(v_aux2_3329_, v_fst_3300_);
v_aux2_3331_ = l_Lean_mkAppN(v_aux2_3330_, v_discrs_x27_3301_);
lean_inc_ref_n(v_aux2_3331_, 2);
v___x_3332_ = l_Lean_indentExpr(v_aux2_3331_);
lean_inc(v___x_3317_);
lean_inc_n(v_toBind_3313_, 3);
v___f_3333_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3333_, 0, v_splitterMatchInfo_3327_);
lean_closure_set(v___f_3333_, 1, v_fst_3302_);
lean_closure_set(v___f_3333_, 2, v_numParams_3303_);
lean_closure_set(v___f_3333_, 3, v_numDiscrs_3304_);
lean_closure_set(v___f_3333_, 4, v_altInfos_3305_);
lean_closure_set(v___f_3333_, 5, v_uElimPos_x3f_3306_);
lean_closure_set(v___f_3333_, 6, v_snd_3307_);
lean_closure_set(v___f_3333_, 7, v_overlaps_3308_);
lean_closure_set(v___f_3333_, 8, v_splitterName_3326_);
lean_closure_set(v___f_3333_, 9, v_matcherLevels_3309_);
lean_closure_set(v___f_3333_, 10, v_params_x27_3299_);
lean_closure_set(v___f_3333_, 11, v_fst_3300_);
lean_closure_set(v___f_3333_, 12, v_discrs_x27_3301_);
lean_closure_set(v___f_3333_, 13, v_toPure_3310_);
lean_closure_set(v___f_3333_, 14, v_onRemaining_3311_);
lean_closure_set(v___f_3333_, 15, v_remaining_3312_);
lean_closure_set(v___f_3333_, 16, v_toBind_3313_);
lean_closure_set(v___f_3333_, 17, v_origAltTypes_3314_);
lean_closure_set(v___f_3333_, 18, v_alts_3315_);
lean_closure_set(v___f_3333_, 19, v___x_3316_);
lean_closure_set(v___f_3333_, 20, v___x_3317_);
lean_closure_set(v___f_3333_, 21, v_remaining_x27_3318_);
lean_closure_set(v___f_3333_, 22, v___f_3319_);
lean_inc(v_inst_3320_);
v___f_3334_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3334_, 0, v___x_3317_);
lean_closure_set(v___f_3334_, 1, v_aux2_3331_);
lean_closure_set(v___f_3334_, 2, v_inst_3320_);
lean_closure_set(v___f_3334_, 3, v_toBind_3313_);
lean_closure_set(v___f_3334_, 4, v___f_3333_);
v___x_3335_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___x_3332_);
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3336_);
lean_ctor_set(v___x_3337_, 1, v___x_3321_);
v___f_3338_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3338_, 0, v___x_3337_);
v___x_3339_ = lean_box(v___x_3322_);
v___x_3340_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3340_, 0, v_aux2_3331_);
lean_closure_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = lean_apply_2(v_inst_3320_, lean_box(0), v___x_3340_);
v___f_3342_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3342_, 0, v___x_3341_);
lean_closure_set(v___f_3342_, 1, v___f_3338_);
v___x_3343_ = lean_apply_2(v_liftWith_3323_, lean_box(0), v___f_3342_);
v___x_3344_ = lean_apply_1(v_restoreM_3324_, lean_box(0));
v___x_3345_ = lean_apply_4(v_toBind_3313_, lean_box(0), lean_box(0), v___x_3343_, v___x_3344_);
v___x_3346_ = lean_apply_4(v_toBind_3313_, lean_box(0), lean_box(0), v___x_3345_, v___f_3334_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3347_ = _args[0];
lean_object* v_params_x27_3348_ = _args[1];
lean_object* v_fst_3349_ = _args[2];
lean_object* v_discrs_x27_3350_ = _args[3];
lean_object* v_fst_3351_ = _args[4];
lean_object* v_numParams_3352_ = _args[5];
lean_object* v_numDiscrs_3353_ = _args[6];
lean_object* v_altInfos_3354_ = _args[7];
lean_object* v_uElimPos_x3f_3355_ = _args[8];
lean_object* v_snd_3356_ = _args[9];
lean_object* v_overlaps_3357_ = _args[10];
lean_object* v_matcherLevels_3358_ = _args[11];
lean_object* v_toPure_3359_ = _args[12];
lean_object* v_onRemaining_3360_ = _args[13];
lean_object* v_remaining_3361_ = _args[14];
lean_object* v_toBind_3362_ = _args[15];
lean_object* v_origAltTypes_3363_ = _args[16];
lean_object* v_alts_3364_ = _args[17];
lean_object* v___x_3365_ = _args[18];
lean_object* v___x_3366_ = _args[19];
lean_object* v_remaining_x27_3367_ = _args[20];
lean_object* v___f_3368_ = _args[21];
lean_object* v_inst_3369_ = _args[22];
lean_object* v___x_3370_ = _args[23];
lean_object* v___x_3371_ = _args[24];
lean_object* v_liftWith_3372_ = _args[25];
lean_object* v_restoreM_3373_ = _args[26];
lean_object* v_matchEqns_3374_ = _args[27];
_start:
{
uint8_t v___x_14251__boxed_3375_; lean_object* v_res_3376_; 
v___x_14251__boxed_3375_ = lean_unbox(v___x_3371_);
v_res_3376_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3347_, v_params_x27_3348_, v_fst_3349_, v_discrs_x27_3350_, v_fst_3351_, v_numParams_3352_, v_numDiscrs_3353_, v_altInfos_3354_, v_uElimPos_x3f_3355_, v_snd_3356_, v_overlaps_3357_, v_matcherLevels_3358_, v_toPure_3359_, v_onRemaining_3360_, v_remaining_3361_, v_toBind_3362_, v_origAltTypes_3363_, v_alts_3364_, v___x_3365_, v___x_3366_, v_remaining_x27_3367_, v___f_3368_, v_inst_3369_, v___x_3370_, v___x_14251__boxed_3375_, v_liftWith_3372_, v_restoreM_3373_, v_matchEqns_3374_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3377_, lean_object* v_params_x27_3378_, lean_object* v_fst_3379_, lean_object* v_discrs_x27_3380_, lean_object* v_fst_3381_, lean_object* v_numParams_3382_, lean_object* v_numDiscrs_3383_, lean_object* v_altInfos_3384_, lean_object* v_uElimPos_x3f_3385_, lean_object* v_snd_3386_, lean_object* v_overlaps_3387_, lean_object* v_matcherLevels_3388_, lean_object* v_toPure_3389_, lean_object* v_onRemaining_3390_, lean_object* v_remaining_3391_, lean_object* v_toBind_3392_, lean_object* v_alts_3393_, lean_object* v___x_3394_, lean_object* v___x_3395_, lean_object* v_remaining_x27_3396_, lean_object* v___f_3397_, lean_object* v_inst_3398_, lean_object* v___x_3399_, uint8_t v___x_3400_, lean_object* v_liftWith_3401_, lean_object* v_restoreM_3402_, lean_object* v_matcherName_3403_, lean_object* v_origAltTypes_3404_){
_start:
{
lean_object* v___x_3405_; lean_object* v___f_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3405_ = lean_box(v___x_3400_);
lean_inc(v_inst_3398_);
lean_inc(v_toBind_3392_);
v___f_3406_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3406_, 0, v___x_3377_);
lean_closure_set(v___f_3406_, 1, v_params_x27_3378_);
lean_closure_set(v___f_3406_, 2, v_fst_3379_);
lean_closure_set(v___f_3406_, 3, v_discrs_x27_3380_);
lean_closure_set(v___f_3406_, 4, v_fst_3381_);
lean_closure_set(v___f_3406_, 5, v_numParams_3382_);
lean_closure_set(v___f_3406_, 6, v_numDiscrs_3383_);
lean_closure_set(v___f_3406_, 7, v_altInfos_3384_);
lean_closure_set(v___f_3406_, 8, v_uElimPos_x3f_3385_);
lean_closure_set(v___f_3406_, 9, v_snd_3386_);
lean_closure_set(v___f_3406_, 10, v_overlaps_3387_);
lean_closure_set(v___f_3406_, 11, v_matcherLevels_3388_);
lean_closure_set(v___f_3406_, 12, v_toPure_3389_);
lean_closure_set(v___f_3406_, 13, v_onRemaining_3390_);
lean_closure_set(v___f_3406_, 14, v_remaining_3391_);
lean_closure_set(v___f_3406_, 15, v_toBind_3392_);
lean_closure_set(v___f_3406_, 16, v_origAltTypes_3404_);
lean_closure_set(v___f_3406_, 17, v_alts_3393_);
lean_closure_set(v___f_3406_, 18, v___x_3394_);
lean_closure_set(v___f_3406_, 19, v___x_3395_);
lean_closure_set(v___f_3406_, 20, v_remaining_x27_3396_);
lean_closure_set(v___f_3406_, 21, v___f_3397_);
lean_closure_set(v___f_3406_, 22, v_inst_3398_);
lean_closure_set(v___f_3406_, 23, v___x_3399_);
lean_closure_set(v___f_3406_, 24, v___x_3405_);
lean_closure_set(v___f_3406_, 25, v_liftWith_3401_);
lean_closure_set(v___f_3406_, 26, v_restoreM_3402_);
v___x_3407_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3407_, 0, v_matcherName_3403_);
v___x_3408_ = lean_apply_2(v_inst_3398_, lean_box(0), v___x_3407_);
v___x_3409_ = lean_apply_4(v_toBind_3392_, lean_box(0), lean_box(0), v___x_3408_, v___f_3406_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3410_ = _args[0];
lean_object* v_params_x27_3411_ = _args[1];
lean_object* v_fst_3412_ = _args[2];
lean_object* v_discrs_x27_3413_ = _args[3];
lean_object* v_fst_3414_ = _args[4];
lean_object* v_numParams_3415_ = _args[5];
lean_object* v_numDiscrs_3416_ = _args[6];
lean_object* v_altInfos_3417_ = _args[7];
lean_object* v_uElimPos_x3f_3418_ = _args[8];
lean_object* v_snd_3419_ = _args[9];
lean_object* v_overlaps_3420_ = _args[10];
lean_object* v_matcherLevels_3421_ = _args[11];
lean_object* v_toPure_3422_ = _args[12];
lean_object* v_onRemaining_3423_ = _args[13];
lean_object* v_remaining_3424_ = _args[14];
lean_object* v_toBind_3425_ = _args[15];
lean_object* v_alts_3426_ = _args[16];
lean_object* v___x_3427_ = _args[17];
lean_object* v___x_3428_ = _args[18];
lean_object* v_remaining_x27_3429_ = _args[19];
lean_object* v___f_3430_ = _args[20];
lean_object* v_inst_3431_ = _args[21];
lean_object* v___x_3432_ = _args[22];
lean_object* v___x_3433_ = _args[23];
lean_object* v_liftWith_3434_ = _args[24];
lean_object* v_restoreM_3435_ = _args[25];
lean_object* v_matcherName_3436_ = _args[26];
lean_object* v_origAltTypes_3437_ = _args[27];
_start:
{
uint8_t v___x_14313__boxed_3438_; lean_object* v_res_3439_; 
v___x_14313__boxed_3438_ = lean_unbox(v___x_3433_);
v_res_3439_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3410_, v_params_x27_3411_, v_fst_3412_, v_discrs_x27_3413_, v_fst_3414_, v_numParams_3415_, v_numDiscrs_3416_, v_altInfos_3417_, v_uElimPos_x3f_3418_, v_snd_3419_, v_overlaps_3420_, v_matcherLevels_3421_, v_toPure_3422_, v_onRemaining_3423_, v_remaining_3424_, v_toBind_3425_, v_alts_3426_, v___x_3427_, v___x_3428_, v_remaining_x27_3429_, v___f_3430_, v_inst_3431_, v___x_3432_, v___x_14313__boxed_3438_, v_liftWith_3434_, v_restoreM_3435_, v_matcherName_3436_, v_origAltTypes_3437_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3440_, lean_object* v_toPure_3441_, lean_object* v_toBind_3442_, lean_object* v___f_3443_, lean_object* v___x_3444_, lean_object* v___x_3445_, lean_object* v_inst_3446_, lean_object* v___x_3447_, lean_object* v_toMonadExceptOf_3448_, uint8_t v___x_3449_, uint8_t v_useSplitter_3450_, lean_object* v_onAlt_3451_, lean_object* v___f_3452_, lean_object* v_fst_3453_, lean_object* v_inst_3454_, lean_object* v_inst_3455_, lean_object* v_numDiscrEqs_3456_, lean_object* v___x_3457_, lean_object* v_params_x27_3458_, lean_object* v_fst_3459_, lean_object* v_discrs_x27_3460_, lean_object* v_fst_3461_, lean_object* v_numParams_3462_, lean_object* v_numDiscrs_3463_, lean_object* v_altInfos_3464_, lean_object* v_uElimPos_x3f_3465_, lean_object* v_snd_3466_, lean_object* v_overlaps_3467_, lean_object* v_matcherLevels_3468_, lean_object* v_onRemaining_3469_, lean_object* v_remaining_3470_, lean_object* v_remaining_x27_3471_, lean_object* v___x_3472_, uint8_t v___x_3473_, lean_object* v_liftWith_3474_, lean_object* v_restoreM_3475_, lean_object* v_matcherName_3476_, lean_object* v_aux1_3477_, lean_object* v_____r_3478_){
_start:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___f_3482_; lean_object* v___x_3483_; lean_object* v___f_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
v___x_3479_ = lean_array_get_size(v_alts_3440_);
v___x_3480_ = lean_box(v___x_3449_);
v___x_3481_ = lean_box(v_useSplitter_3450_);
lean_inc_n(v_inst_3446_, 2);
lean_inc(v___x_3444_);
lean_inc_n(v_toBind_3442_, 2);
lean_inc(v_toPure_3441_);
v___f_3482_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 21, 17);
lean_closure_set(v___f_3482_, 0, v___x_3479_);
lean_closure_set(v___f_3482_, 1, v_toPure_3441_);
lean_closure_set(v___f_3482_, 2, v_toBind_3442_);
lean_closure_set(v___f_3482_, 3, v___f_3443_);
lean_closure_set(v___f_3482_, 4, v___x_3444_);
lean_closure_set(v___f_3482_, 5, v___x_3445_);
lean_closure_set(v___f_3482_, 6, v_inst_3446_);
lean_closure_set(v___f_3482_, 7, v___x_3447_);
lean_closure_set(v___f_3482_, 8, v_toMonadExceptOf_3448_);
lean_closure_set(v___f_3482_, 9, v___x_3480_);
lean_closure_set(v___f_3482_, 10, v___x_3481_);
lean_closure_set(v___f_3482_, 11, v_onAlt_3451_);
lean_closure_set(v___f_3482_, 12, v___f_3452_);
lean_closure_set(v___f_3482_, 13, v_fst_3453_);
lean_closure_set(v___f_3482_, 14, v_inst_3454_);
lean_closure_set(v___f_3482_, 15, v_inst_3455_);
lean_closure_set(v___f_3482_, 16, v_numDiscrEqs_3456_);
v___x_3483_ = lean_box(v___x_3473_);
v___f_3484_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 28, 27);
lean_closure_set(v___f_3484_, 0, v___x_3457_);
lean_closure_set(v___f_3484_, 1, v_params_x27_3458_);
lean_closure_set(v___f_3484_, 2, v_fst_3459_);
lean_closure_set(v___f_3484_, 3, v_discrs_x27_3460_);
lean_closure_set(v___f_3484_, 4, v_fst_3461_);
lean_closure_set(v___f_3484_, 5, v_numParams_3462_);
lean_closure_set(v___f_3484_, 6, v_numDiscrs_3463_);
lean_closure_set(v___f_3484_, 7, v_altInfos_3464_);
lean_closure_set(v___f_3484_, 8, v_uElimPos_x3f_3465_);
lean_closure_set(v___f_3484_, 9, v_snd_3466_);
lean_closure_set(v___f_3484_, 10, v_overlaps_3467_);
lean_closure_set(v___f_3484_, 11, v_matcherLevels_3468_);
lean_closure_set(v___f_3484_, 12, v_toPure_3441_);
lean_closure_set(v___f_3484_, 13, v_onRemaining_3469_);
lean_closure_set(v___f_3484_, 14, v_remaining_3470_);
lean_closure_set(v___f_3484_, 15, v_toBind_3442_);
lean_closure_set(v___f_3484_, 16, v_alts_3440_);
lean_closure_set(v___f_3484_, 17, v___x_3444_);
lean_closure_set(v___f_3484_, 18, v___x_3479_);
lean_closure_set(v___f_3484_, 19, v_remaining_x27_3471_);
lean_closure_set(v___f_3484_, 20, v___f_3482_);
lean_closure_set(v___f_3484_, 21, v_inst_3446_);
lean_closure_set(v___f_3484_, 22, v___x_3472_);
lean_closure_set(v___f_3484_, 23, v___x_3483_);
lean_closure_set(v___f_3484_, 24, v_liftWith_3474_);
lean_closure_set(v___f_3484_, 25, v_restoreM_3475_);
lean_closure_set(v___f_3484_, 26, v_matcherName_3476_);
v___x_3485_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3485_, 0, v___x_3479_);
lean_closure_set(v___x_3485_, 1, v_aux1_3477_);
v___x_3486_ = lean_apply_2(v_inst_3446_, lean_box(0), v___x_3485_);
v___x_3487_ = lean_apply_4(v_toBind_3442_, lean_box(0), lean_box(0), v___x_3486_, v___f_3484_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3488_ = _args[0];
lean_object* v_toPure_3489_ = _args[1];
lean_object* v_toBind_3490_ = _args[2];
lean_object* v___f_3491_ = _args[3];
lean_object* v___x_3492_ = _args[4];
lean_object* v___x_3493_ = _args[5];
lean_object* v_inst_3494_ = _args[6];
lean_object* v___x_3495_ = _args[7];
lean_object* v_toMonadExceptOf_3496_ = _args[8];
lean_object* v___x_3497_ = _args[9];
lean_object* v_useSplitter_3498_ = _args[10];
lean_object* v_onAlt_3499_ = _args[11];
lean_object* v___f_3500_ = _args[12];
lean_object* v_fst_3501_ = _args[13];
lean_object* v_inst_3502_ = _args[14];
lean_object* v_inst_3503_ = _args[15];
lean_object* v_numDiscrEqs_3504_ = _args[16];
lean_object* v___x_3505_ = _args[17];
lean_object* v_params_x27_3506_ = _args[18];
lean_object* v_fst_3507_ = _args[19];
lean_object* v_discrs_x27_3508_ = _args[20];
lean_object* v_fst_3509_ = _args[21];
lean_object* v_numParams_3510_ = _args[22];
lean_object* v_numDiscrs_3511_ = _args[23];
lean_object* v_altInfos_3512_ = _args[24];
lean_object* v_uElimPos_x3f_3513_ = _args[25];
lean_object* v_snd_3514_ = _args[26];
lean_object* v_overlaps_3515_ = _args[27];
lean_object* v_matcherLevels_3516_ = _args[28];
lean_object* v_onRemaining_3517_ = _args[29];
lean_object* v_remaining_3518_ = _args[30];
lean_object* v_remaining_x27_3519_ = _args[31];
lean_object* v___x_3520_ = _args[32];
lean_object* v___x_3521_ = _args[33];
lean_object* v_liftWith_3522_ = _args[34];
lean_object* v_restoreM_3523_ = _args[35];
lean_object* v_matcherName_3524_ = _args[36];
lean_object* v_aux1_3525_ = _args[37];
lean_object* v_____r_3526_ = _args[38];
_start:
{
uint8_t v___x_14347__boxed_3527_; uint8_t v_useSplitter_boxed_3528_; uint8_t v___x_14355__boxed_3529_; lean_object* v_res_3530_; 
v___x_14347__boxed_3527_ = lean_unbox(v___x_3497_);
v_useSplitter_boxed_3528_ = lean_unbox(v_useSplitter_3498_);
v___x_14355__boxed_3529_ = lean_unbox(v___x_3521_);
v_res_3530_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3488_, v_toPure_3489_, v_toBind_3490_, v___f_3491_, v___x_3492_, v___x_3493_, v_inst_3494_, v___x_3495_, v_toMonadExceptOf_3496_, v___x_14347__boxed_3527_, v_useSplitter_boxed_3528_, v_onAlt_3499_, v___f_3500_, v_fst_3501_, v_inst_3502_, v_inst_3503_, v_numDiscrEqs_3504_, v___x_3505_, v_params_x27_3506_, v_fst_3507_, v_discrs_x27_3508_, v_fst_3509_, v_numParams_3510_, v_numDiscrs_3511_, v_altInfos_3512_, v_uElimPos_x3f_3513_, v_snd_3514_, v_overlaps_3515_, v_matcherLevels_3516_, v_onRemaining_3517_, v_remaining_3518_, v_remaining_x27_3519_, v___x_3520_, v___x_14355__boxed_3529_, v_liftWith_3522_, v_restoreM_3523_, v_matcherName_3524_, v_aux1_3525_, v_____r_3526_);
return v_res_3530_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4));
v___x_3539_ = l_Lean_stringToMessageData(v___x_3538_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v_numParams_3540_, lean_object* v_numDiscrs_3541_, lean_object* v_altInfos_3542_, lean_object* v_uElimPos_x3f_3543_, lean_object* v_snd_3544_, lean_object* v_overlaps_3545_, lean_object* v_matcherName_3546_, lean_object* v_matcherLevels_3547_, lean_object* v_params_x27_3548_, lean_object* v_fst_3549_, lean_object* v_discrs_x27_3550_, lean_object* v_toPure_3551_, lean_object* v_onRemaining_3552_, lean_object* v_remaining_3553_, lean_object* v_toBind_3554_, lean_object* v_inst_3555_, lean_object* v_alts_3556_, lean_object* v___f_3557_, uint8_t v___x_3558_, lean_object* v_inst_3559_, lean_object* v_remaining_x27_3560_, lean_object* v_onAlt_3561_, lean_object* v_inst_3562_, lean_object* v___f_3563_, lean_object* v_matcherApp_3564_, lean_object* v___x_3565_, uint8_t v_useSplitter_3566_, uint8_t v_isCasesOn_3567_, lean_object* v___f_3568_, lean_object* v___x_3569_, lean_object* v___x_3570_, lean_object* v_toMonadExceptOf_3571_, lean_object* v___f_3572_, lean_object* v_numDiscrEqs_3573_, lean_object* v_____s_3574_){
_start:
{
lean_object* v_snd_3575_; lean_object* v_fst_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3642_; 
v_snd_3575_ = lean_ctor_get(v_____s_3574_, 1);
v_fst_3576_ = lean_ctor_get(v_____s_3574_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_____s_3574_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3578_ = v_____s_3574_;
v_isShared_3579_ = v_isSharedCheck_3642_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_snd_3575_);
lean_inc(v_fst_3576_);
lean_dec(v_____s_3574_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3642_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v_fst_3580_; lean_object* v___x_3582_; uint8_t v_isShared_3583_; uint8_t v_isSharedCheck_3640_; 
v_fst_3580_ = lean_ctor_get(v_snd_3575_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_snd_3575_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v_snd_3575_, 1);
lean_dec(v_unused_3641_);
v___x_3582_ = v_snd_3575_;
v_isShared_3583_ = v_isSharedCheck_3640_;
goto v_resetjp_3581_;
}
else
{
lean_inc(v_fst_3580_);
lean_dec(v_snd_3575_);
v___x_3582_ = lean_box(0);
v_isShared_3583_ = v_isSharedCheck_3640_;
goto v_resetjp_3581_;
}
v_resetjp_3581_:
{
lean_object* v___f_3584_; 
lean_inc(v_toBind_3554_);
lean_inc_ref(v_remaining_3553_);
lean_inc(v_onRemaining_3552_);
lean_inc(v_toPure_3551_);
lean_inc_ref(v_discrs_x27_3550_);
lean_inc_ref(v_fst_3549_);
lean_inc_ref(v_params_x27_3548_);
lean_inc_ref(v_matcherLevels_3547_);
lean_inc(v_matcherName_3546_);
lean_inc_ref(v_overlaps_3545_);
lean_inc_ref(v_snd_3544_);
lean_inc(v_uElimPos_x3f_3543_);
lean_inc_ref(v_altInfos_3542_);
lean_inc(v_numDiscrs_3541_);
lean_inc(v_numParams_3540_);
lean_inc(v_fst_3576_);
v___f_3584_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3584_, 0, v_fst_3576_);
lean_closure_set(v___f_3584_, 1, v_numParams_3540_);
lean_closure_set(v___f_3584_, 2, v_numDiscrs_3541_);
lean_closure_set(v___f_3584_, 3, v_altInfos_3542_);
lean_closure_set(v___f_3584_, 4, v_uElimPos_x3f_3543_);
lean_closure_set(v___f_3584_, 5, v_snd_3544_);
lean_closure_set(v___f_3584_, 6, v_overlaps_3545_);
lean_closure_set(v___f_3584_, 7, v_matcherName_3546_);
lean_closure_set(v___f_3584_, 8, v_matcherLevels_3547_);
lean_closure_set(v___f_3584_, 9, v_params_x27_3548_);
lean_closure_set(v___f_3584_, 10, v_fst_3549_);
lean_closure_set(v___f_3584_, 11, v_discrs_x27_3550_);
lean_closure_set(v___f_3584_, 12, v_toPure_3551_);
lean_closure_set(v___f_3584_, 13, v_onRemaining_3552_);
lean_closure_set(v___f_3584_, 14, v_remaining_3553_);
lean_closure_set(v___f_3584_, 15, v_toBind_3554_);
if (v_useSplitter_3566_ == 0)
{
lean_del_object(v___x_3578_);
lean_dec(v_fst_3576_);
lean_dec(v_numDiscrEqs_3573_);
lean_dec(v___f_3572_);
lean_dec_ref(v_toMonadExceptOf_3571_);
lean_dec(v___x_3570_);
lean_dec(v___x_3569_);
lean_dec(v___f_3568_);
lean_dec_ref(v_remaining_3553_);
lean_dec(v_onRemaining_3552_);
lean_dec_ref(v_overlaps_3545_);
lean_dec_ref(v_snd_3544_);
lean_dec(v_uElimPos_x3f_3543_);
lean_dec_ref(v_altInfos_3542_);
lean_dec(v_numDiscrs_3541_);
lean_dec(v_numParams_3540_);
goto v___jp_3585_;
}
else
{
if (v_isCasesOn_3567_ == 0)
{
lean_object* v_liftWith_3612_; lean_object* v_restoreM_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v_aux1_3616_; lean_object* v_aux1_3617_; lean_object* v_aux1_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec_ref(v___f_3584_);
lean_del_object(v___x_3582_);
lean_dec_ref(v_matcherApp_3564_);
lean_dec(v___f_3563_);
lean_dec(v___f_3557_);
v_liftWith_3612_ = lean_ctor_get(v_inst_3555_, 0);
lean_inc(v_liftWith_3612_);
v_restoreM_3613_ = lean_ctor_get(v_inst_3555_, 1);
lean_inc(v_restoreM_3613_);
lean_inc_ref(v_matcherLevels_3547_);
v___x_3614_ = lean_array_to_list(v_matcherLevels_3547_);
lean_inc(v___x_3614_);
lean_inc(v_matcherName_3546_);
v___x_3615_ = l_Lean_mkConst(v_matcherName_3546_, v___x_3614_);
v_aux1_3616_ = l_Lean_mkAppN(v___x_3615_, v_params_x27_3548_);
lean_inc_ref(v_fst_3549_);
v_aux1_3617_ = l_Lean_Expr_app___override(v_aux1_3616_, v_fst_3549_);
v_aux1_3618_ = l_Lean_mkAppN(v_aux1_3617_, v_discrs_x27_3550_);
lean_inc_ref(v_aux1_3618_);
v___x_3619_ = l_Lean_indentExpr(v_aux1_3618_);
v___x_3620_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
if (v_isShared_3579_ == 0)
{
lean_ctor_set_tag(v___x_3578_, 7);
lean_ctor_set(v___x_3578_, 1, v___x_3619_);
lean_ctor_set(v___x_3578_, 0, v___x_3620_);
v___x_3622_ = v___x_3578_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3620_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v___x_3619_);
v___x_3622_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___f_3625_; uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___f_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3623_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___f_3625_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3625_, 0, v___x_3624_);
v___x_3626_ = 0;
v___x_3627_ = lean_box(v___x_3558_);
v___x_3628_ = lean_box(v_useSplitter_3566_);
v___x_3629_ = lean_box(v___x_3626_);
lean_inc_ref(v_aux1_3618_);
lean_inc(v_restoreM_3613_);
lean_inc(v_liftWith_3612_);
lean_inc(v_inst_3559_);
lean_inc_n(v_toBind_3554_, 2);
v___f_3630_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 39, 38);
lean_closure_set(v___f_3630_, 0, v_alts_3556_);
lean_closure_set(v___f_3630_, 1, v_toPure_3551_);
lean_closure_set(v___f_3630_, 2, v_toBind_3554_);
lean_closure_set(v___f_3630_, 3, v___f_3568_);
lean_closure_set(v___f_3630_, 4, v___x_3565_);
lean_closure_set(v___f_3630_, 5, v___x_3569_);
lean_closure_set(v___f_3630_, 6, v_inst_3559_);
lean_closure_set(v___f_3630_, 7, v___x_3570_);
lean_closure_set(v___f_3630_, 8, v_toMonadExceptOf_3571_);
lean_closure_set(v___f_3630_, 9, v___x_3627_);
lean_closure_set(v___f_3630_, 10, v___x_3628_);
lean_closure_set(v___f_3630_, 11, v_onAlt_3561_);
lean_closure_set(v___f_3630_, 12, v___f_3572_);
lean_closure_set(v___f_3630_, 13, v_fst_3580_);
lean_closure_set(v___f_3630_, 14, v_inst_3555_);
lean_closure_set(v___f_3630_, 15, v_inst_3562_);
lean_closure_set(v___f_3630_, 16, v_numDiscrEqs_3573_);
lean_closure_set(v___f_3630_, 17, v___x_3614_);
lean_closure_set(v___f_3630_, 18, v_params_x27_3548_);
lean_closure_set(v___f_3630_, 19, v_fst_3549_);
lean_closure_set(v___f_3630_, 20, v_discrs_x27_3550_);
lean_closure_set(v___f_3630_, 21, v_fst_3576_);
lean_closure_set(v___f_3630_, 22, v_numParams_3540_);
lean_closure_set(v___f_3630_, 23, v_numDiscrs_3541_);
lean_closure_set(v___f_3630_, 24, v_altInfos_3542_);
lean_closure_set(v___f_3630_, 25, v_uElimPos_x3f_3543_);
lean_closure_set(v___f_3630_, 26, v_snd_3544_);
lean_closure_set(v___f_3630_, 27, v_overlaps_3545_);
lean_closure_set(v___f_3630_, 28, v_matcherLevels_3547_);
lean_closure_set(v___f_3630_, 29, v_onRemaining_3552_);
lean_closure_set(v___f_3630_, 30, v_remaining_3553_);
lean_closure_set(v___f_3630_, 31, v_remaining_x27_3560_);
lean_closure_set(v___f_3630_, 32, v___x_3623_);
lean_closure_set(v___f_3630_, 33, v___x_3629_);
lean_closure_set(v___f_3630_, 34, v_liftWith_3612_);
lean_closure_set(v___f_3630_, 35, v_restoreM_3613_);
lean_closure_set(v___f_3630_, 36, v_matcherName_3546_);
lean_closure_set(v___f_3630_, 37, v_aux1_3618_);
v___x_3631_ = lean_box(v___x_3626_);
v___x_3632_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3632_, 0, v_aux1_3618_);
lean_closure_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_apply_2(v_inst_3559_, lean_box(0), v___x_3632_);
v___f_3634_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3634_, 0, v___x_3633_);
lean_closure_set(v___f_3634_, 1, v___f_3625_);
v___x_3635_ = lean_apply_2(v_liftWith_3612_, lean_box(0), v___f_3634_);
v___x_3636_ = lean_apply_1(v_restoreM_3613_, lean_box(0));
v___x_3637_ = lean_apply_4(v_toBind_3554_, lean_box(0), lean_box(0), v___x_3635_, v___x_3636_);
v___x_3638_ = lean_apply_4(v_toBind_3554_, lean_box(0), lean_box(0), v___x_3637_, v___f_3630_);
return v___x_3638_;
}
}
else
{
lean_del_object(v___x_3578_);
lean_dec(v_fst_3576_);
lean_dec(v_numDiscrEqs_3573_);
lean_dec(v___f_3572_);
lean_dec_ref(v_toMonadExceptOf_3571_);
lean_dec(v___x_3570_);
lean_dec(v___x_3569_);
lean_dec(v___f_3568_);
lean_dec_ref(v_remaining_3553_);
lean_dec(v_onRemaining_3552_);
lean_dec_ref(v_overlaps_3545_);
lean_dec_ref(v_snd_3544_);
lean_dec(v_uElimPos_x3f_3543_);
lean_dec_ref(v_altInfos_3542_);
lean_dec(v_numDiscrs_3541_);
lean_dec(v_numParams_3540_);
goto v___jp_3585_;
}
}
v___jp_3585_:
{
lean_object* v_liftWith_3586_; lean_object* v_restoreM_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v_aux_3590_; lean_object* v_aux_3591_; lean_object* v_aux_3592_; lean_object* v___x_3593_; uint8_t v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___f_3597_; lean_object* v___x_3598_; lean_object* v___x_3600_; 
v_liftWith_3586_ = lean_ctor_get(v_inst_3555_, 0);
lean_inc(v_liftWith_3586_);
v_restoreM_3587_ = lean_ctor_get(v_inst_3555_, 1);
lean_inc(v_restoreM_3587_);
v___x_3588_ = lean_array_to_list(v_matcherLevels_3547_);
v___x_3589_ = l_Lean_mkConst(v_matcherName_3546_, v___x_3588_);
v_aux_3590_ = l_Lean_mkAppN(v___x_3589_, v_params_x27_3548_);
lean_dec_ref(v_params_x27_3548_);
v_aux_3591_ = l_Lean_Expr_app___override(v_aux_3590_, v_fst_3549_);
v_aux_3592_ = l_Lean_mkAppN(v_aux_3591_, v_discrs_x27_3550_);
lean_dec_ref(v_discrs_x27_3550_);
lean_inc_ref_n(v_aux_3592_, 2);
v___x_3593_ = l_Lean_indentExpr(v_aux_3592_);
v___x_3594_ = 1;
v___x_3595_ = lean_box(v___x_3558_);
v___x_3596_ = lean_box(v___x_3594_);
lean_inc(v_inst_3559_);
lean_inc(v_toBind_3554_);
v___f_3597_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3597_, 0, v_alts_3556_);
lean_closure_set(v___f_3597_, 1, v_toPure_3551_);
lean_closure_set(v___f_3597_, 2, v_toBind_3554_);
lean_closure_set(v___f_3597_, 3, v___f_3557_);
lean_closure_set(v___f_3597_, 4, v___x_3595_);
lean_closure_set(v___f_3597_, 5, v___x_3596_);
lean_closure_set(v___f_3597_, 6, v_inst_3559_);
lean_closure_set(v___f_3597_, 7, v_remaining_x27_3560_);
lean_closure_set(v___f_3597_, 8, v_onAlt_3561_);
lean_closure_set(v___f_3597_, 9, v_inst_3555_);
lean_closure_set(v___f_3597_, 10, v_inst_3562_);
lean_closure_set(v___f_3597_, 11, v___f_3563_);
lean_closure_set(v___f_3597_, 12, v_fst_3580_);
lean_closure_set(v___f_3597_, 13, v_matcherApp_3564_);
lean_closure_set(v___f_3597_, 14, v___x_3565_);
lean_closure_set(v___f_3597_, 15, v___f_3584_);
lean_closure_set(v___f_3597_, 16, v_aux_3592_);
v___x_3598_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
if (v_isShared_3583_ == 0)
{
lean_ctor_set_tag(v___x_3582_, 7);
lean_ctor_set(v___x_3582_, 1, v___x_3593_);
lean_ctor_set(v___x_3582_, 0, v___x_3598_);
v___x_3600_ = v___x_3582_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3598_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v___x_3593_);
v___x_3600_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___f_3601_; uint8_t v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___f_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___f_3601_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3601_, 0, v___x_3600_);
v___x_3602_ = 0;
v___x_3603_ = lean_box(v___x_3602_);
v___x_3604_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3604_, 0, v_aux_3592_);
lean_closure_set(v___x_3604_, 1, v___x_3603_);
v___x_3605_ = lean_apply_2(v_inst_3559_, lean_box(0), v___x_3604_);
v___f_3606_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3606_, 0, v___x_3605_);
lean_closure_set(v___f_3606_, 1, v___f_3601_);
v___x_3607_ = lean_apply_2(v_liftWith_3586_, lean_box(0), v___f_3606_);
v___x_3608_ = lean_apply_1(v_restoreM_3587_, lean_box(0));
lean_inc(v_toBind_3554_);
v___x_3609_ = lean_apply_4(v_toBind_3554_, lean_box(0), lean_box(0), v___x_3607_, v___x_3608_);
v___x_3610_ = lean_apply_4(v_toBind_3554_, lean_box(0), lean_box(0), v___x_3609_, v___f_3597_);
return v___x_3610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v_numParams_3643_ = _args[0];
lean_object* v_numDiscrs_3644_ = _args[1];
lean_object* v_altInfos_3645_ = _args[2];
lean_object* v_uElimPos_x3f_3646_ = _args[3];
lean_object* v_snd_3647_ = _args[4];
lean_object* v_overlaps_3648_ = _args[5];
lean_object* v_matcherName_3649_ = _args[6];
lean_object* v_matcherLevels_3650_ = _args[7];
lean_object* v_params_x27_3651_ = _args[8];
lean_object* v_fst_3652_ = _args[9];
lean_object* v_discrs_x27_3653_ = _args[10];
lean_object* v_toPure_3654_ = _args[11];
lean_object* v_onRemaining_3655_ = _args[12];
lean_object* v_remaining_3656_ = _args[13];
lean_object* v_toBind_3657_ = _args[14];
lean_object* v_inst_3658_ = _args[15];
lean_object* v_alts_3659_ = _args[16];
lean_object* v___f_3660_ = _args[17];
lean_object* v___x_3661_ = _args[18];
lean_object* v_inst_3662_ = _args[19];
lean_object* v_remaining_x27_3663_ = _args[20];
lean_object* v_onAlt_3664_ = _args[21];
lean_object* v_inst_3665_ = _args[22];
lean_object* v___f_3666_ = _args[23];
lean_object* v_matcherApp_3667_ = _args[24];
lean_object* v___x_3668_ = _args[25];
lean_object* v_useSplitter_3669_ = _args[26];
lean_object* v_isCasesOn_3670_ = _args[27];
lean_object* v___f_3671_ = _args[28];
lean_object* v___x_3672_ = _args[29];
lean_object* v___x_3673_ = _args[30];
lean_object* v_toMonadExceptOf_3674_ = _args[31];
lean_object* v___f_3675_ = _args[32];
lean_object* v_numDiscrEqs_3676_ = _args[33];
lean_object* v_____s_3677_ = _args[34];
_start:
{
uint8_t v___x_14427__boxed_3678_; uint8_t v_useSplitter_boxed_3679_; uint8_t v_isCasesOn_boxed_3680_; lean_object* v_res_3681_; 
v___x_14427__boxed_3678_ = lean_unbox(v___x_3661_);
v_useSplitter_boxed_3679_ = lean_unbox(v_useSplitter_3669_);
v_isCasesOn_boxed_3680_ = lean_unbox(v_isCasesOn_3670_);
v_res_3681_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3643_, v_numDiscrs_3644_, v_altInfos_3645_, v_uElimPos_x3f_3646_, v_snd_3647_, v_overlaps_3648_, v_matcherName_3649_, v_matcherLevels_3650_, v_params_x27_3651_, v_fst_3652_, v_discrs_x27_3653_, v_toPure_3654_, v_onRemaining_3655_, v_remaining_3656_, v_toBind_3657_, v_inst_3658_, v_alts_3659_, v___f_3660_, v___x_14427__boxed_3678_, v_inst_3662_, v_remaining_x27_3663_, v_onAlt_3664_, v_inst_3665_, v___f_3666_, v_matcherApp_3667_, v___x_3668_, v_useSplitter_boxed_3679_, v_isCasesOn_boxed_3680_, v___f_3671_, v___x_3672_, v___x_3673_, v_toMonadExceptOf_3674_, v___f_3675_, v_numDiscrEqs_3676_, v_____s_3677_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3682_, lean_object* v_numDiscrs_3683_, lean_object* v_altInfos_3684_, lean_object* v_uElimPos_x3f_3685_, lean_object* v_snd_3686_, lean_object* v_overlaps_3687_, lean_object* v_matcherName_3688_, lean_object* v_params_x27_3689_, lean_object* v_fst_3690_, lean_object* v_discrs_x27_3691_, lean_object* v_toPure_3692_, lean_object* v_onRemaining_3693_, lean_object* v_remaining_3694_, lean_object* v_toBind_3695_, lean_object* v_inst_3696_, lean_object* v_alts_3697_, lean_object* v___f_3698_, uint8_t v___x_3699_, lean_object* v_inst_3700_, lean_object* v_onAlt_3701_, lean_object* v_inst_3702_, lean_object* v___f_3703_, lean_object* v_matcherApp_3704_, uint8_t v_useSplitter_3705_, uint8_t v_isCasesOn_3706_, lean_object* v___f_3707_, lean_object* v___x_3708_, lean_object* v___x_3709_, lean_object* v_toMonadExceptOf_3710_, lean_object* v___f_3711_, lean_object* v_numDiscrEqs_3712_, lean_object* v_fst_3713_, lean_object* v___f_3714_, lean_object* v_matcherLevels_3715_){
_start:
{
lean_object* v___x_3716_; lean_object* v_remaining_x27_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___f_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; size_t v_sz_3728_; size_t v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3716_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3717_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3718_ = lean_box(v___x_3699_);
v___x_3719_ = lean_box(v_useSplitter_3705_);
v___x_3720_ = lean_box(v_isCasesOn_3706_);
lean_inc_ref(v_inst_3702_);
lean_inc(v_toBind_3695_);
lean_inc_ref(v_discrs_x27_3691_);
v___f_3721_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 35, 34);
lean_closure_set(v___f_3721_, 0, v_numParams_3682_);
lean_closure_set(v___f_3721_, 1, v_numDiscrs_3683_);
lean_closure_set(v___f_3721_, 2, v_altInfos_3684_);
lean_closure_set(v___f_3721_, 3, v_uElimPos_x3f_3685_);
lean_closure_set(v___f_3721_, 4, v_snd_3686_);
lean_closure_set(v___f_3721_, 5, v_overlaps_3687_);
lean_closure_set(v___f_3721_, 6, v_matcherName_3688_);
lean_closure_set(v___f_3721_, 7, v_matcherLevels_3715_);
lean_closure_set(v___f_3721_, 8, v_params_x27_3689_);
lean_closure_set(v___f_3721_, 9, v_fst_3690_);
lean_closure_set(v___f_3721_, 10, v_discrs_x27_3691_);
lean_closure_set(v___f_3721_, 11, v_toPure_3692_);
lean_closure_set(v___f_3721_, 12, v_onRemaining_3693_);
lean_closure_set(v___f_3721_, 13, v_remaining_3694_);
lean_closure_set(v___f_3721_, 14, v_toBind_3695_);
lean_closure_set(v___f_3721_, 15, v_inst_3696_);
lean_closure_set(v___f_3721_, 16, v_alts_3697_);
lean_closure_set(v___f_3721_, 17, v___f_3698_);
lean_closure_set(v___f_3721_, 18, v___x_3718_);
lean_closure_set(v___f_3721_, 19, v_inst_3700_);
lean_closure_set(v___f_3721_, 20, v_remaining_x27_3717_);
lean_closure_set(v___f_3721_, 21, v_onAlt_3701_);
lean_closure_set(v___f_3721_, 22, v_inst_3702_);
lean_closure_set(v___f_3721_, 23, v___f_3703_);
lean_closure_set(v___f_3721_, 24, v_matcherApp_3704_);
lean_closure_set(v___f_3721_, 25, v___x_3716_);
lean_closure_set(v___f_3721_, 26, v___x_3719_);
lean_closure_set(v___f_3721_, 27, v___x_3720_);
lean_closure_set(v___f_3721_, 28, v___f_3707_);
lean_closure_set(v___f_3721_, 29, v___x_3708_);
lean_closure_set(v___f_3721_, 30, v___x_3709_);
lean_closure_set(v___f_3721_, 31, v_toMonadExceptOf_3710_);
lean_closure_set(v___f_3721_, 32, v___f_3711_);
lean_closure_set(v___f_3721_, 33, v_numDiscrEqs_3712_);
v___x_3722_ = l_Array_reverse___redArg(v_fst_3713_);
v___x_3723_ = lean_array_get_size(v___x_3722_);
v___x_3724_ = l_Array_toSubarray___redArg(v___x_3722_, v___x_3716_, v___x_3723_);
v___x_3725_ = l_Array_reverse___redArg(v_discrs_x27_3691_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3716_);
lean_ctor_set(v___x_3726_, 1, v___x_3724_);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v_remaining_x27_3717_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v_sz_3728_ = lean_array_size(v___x_3725_);
v___x_3729_ = ((size_t)0ULL);
v___x_3730_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3702_, v___x_3725_, v___f_3714_, v_sz_3728_, v___x_3729_, v___x_3727_);
v___x_3731_ = lean_apply_4(v_toBind_3695_, lean_box(0), lean_box(0), v___x_3730_, v___f_3721_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3732_ = _args[0];
lean_object* v_numDiscrs_3733_ = _args[1];
lean_object* v_altInfos_3734_ = _args[2];
lean_object* v_uElimPos_x3f_3735_ = _args[3];
lean_object* v_snd_3736_ = _args[4];
lean_object* v_overlaps_3737_ = _args[5];
lean_object* v_matcherName_3738_ = _args[6];
lean_object* v_params_x27_3739_ = _args[7];
lean_object* v_fst_3740_ = _args[8];
lean_object* v_discrs_x27_3741_ = _args[9];
lean_object* v_toPure_3742_ = _args[10];
lean_object* v_onRemaining_3743_ = _args[11];
lean_object* v_remaining_3744_ = _args[12];
lean_object* v_toBind_3745_ = _args[13];
lean_object* v_inst_3746_ = _args[14];
lean_object* v_alts_3747_ = _args[15];
lean_object* v___f_3748_ = _args[16];
lean_object* v___x_3749_ = _args[17];
lean_object* v_inst_3750_ = _args[18];
lean_object* v_onAlt_3751_ = _args[19];
lean_object* v_inst_3752_ = _args[20];
lean_object* v___f_3753_ = _args[21];
lean_object* v_matcherApp_3754_ = _args[22];
lean_object* v_useSplitter_3755_ = _args[23];
lean_object* v_isCasesOn_3756_ = _args[24];
lean_object* v___f_3757_ = _args[25];
lean_object* v___x_3758_ = _args[26];
lean_object* v___x_3759_ = _args[27];
lean_object* v_toMonadExceptOf_3760_ = _args[28];
lean_object* v___f_3761_ = _args[29];
lean_object* v_numDiscrEqs_3762_ = _args[30];
lean_object* v_fst_3763_ = _args[31];
lean_object* v___f_3764_ = _args[32];
lean_object* v_matcherLevels_3765_ = _args[33];
_start:
{
uint8_t v___x_14589__boxed_3766_; uint8_t v_useSplitter_boxed_3767_; uint8_t v_isCasesOn_boxed_3768_; lean_object* v_res_3769_; 
v___x_14589__boxed_3766_ = lean_unbox(v___x_3749_);
v_useSplitter_boxed_3767_ = lean_unbox(v_useSplitter_3755_);
v_isCasesOn_boxed_3768_ = lean_unbox(v_isCasesOn_3756_);
v_res_3769_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3732_, v_numDiscrs_3733_, v_altInfos_3734_, v_uElimPos_x3f_3735_, v_snd_3736_, v_overlaps_3737_, v_matcherName_3738_, v_params_x27_3739_, v_fst_3740_, v_discrs_x27_3741_, v_toPure_3742_, v_onRemaining_3743_, v_remaining_3744_, v_toBind_3745_, v_inst_3746_, v_alts_3747_, v___f_3748_, v___x_14589__boxed_3766_, v_inst_3750_, v_onAlt_3751_, v_inst_3752_, v___f_3753_, v_matcherApp_3754_, v_useSplitter_boxed_3767_, v_isCasesOn_boxed_3768_, v___f_3757_, v___x_3758_, v___x_3759_, v_toMonadExceptOf_3760_, v___f_3761_, v_numDiscrEqs_3762_, v_fst_3763_, v___f_3764_, v_matcherLevels_3765_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v___f_3770_, lean_object* v_matcherLevels_3771_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_apply_1(v___f_3770_, v_matcherLevels_3771_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3773_, lean_object* v_matcherName_3774_, lean_object* v_params_x27_3775_, lean_object* v_discrs_x27_3776_, lean_object* v_toPure_3777_, lean_object* v_onRemaining_3778_, lean_object* v_remaining_3779_, lean_object* v_toBind_3780_, lean_object* v_inst_3781_, lean_object* v_alts_3782_, lean_object* v___f_3783_, uint8_t v___x_3784_, lean_object* v_inst_3785_, lean_object* v_onAlt_3786_, lean_object* v_inst_3787_, lean_object* v___f_3788_, lean_object* v_matcherApp_3789_, uint8_t v_useSplitter_3790_, uint8_t v_isCasesOn_3791_, lean_object* v___f_3792_, lean_object* v___x_3793_, lean_object* v___x_3794_, lean_object* v_toMonadExceptOf_3795_, lean_object* v___f_3796_, lean_object* v_numDiscrEqs_3797_, lean_object* v___f_3798_, lean_object* v_matcherLevels_3799_, lean_object* v_____x_3800_){
_start:
{
lean_object* v_snd_3801_; lean_object* v_snd_3802_; lean_object* v_fst_3803_; lean_object* v_fst_3804_; lean_object* v_fst_3805_; lean_object* v_snd_3806_; lean_object* v_numParams_3807_; lean_object* v_numDiscrs_3808_; lean_object* v_altInfos_3809_; lean_object* v_uElimPos_x3f_3810_; lean_object* v_overlaps_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___f_3815_; 
v_snd_3801_ = lean_ctor_get(v_____x_3800_, 1);
lean_inc(v_snd_3801_);
v_snd_3802_ = lean_ctor_get(v_snd_3801_, 1);
lean_inc(v_snd_3802_);
v_fst_3803_ = lean_ctor_get(v_____x_3800_, 0);
lean_inc(v_fst_3803_);
lean_dec_ref(v_____x_3800_);
v_fst_3804_ = lean_ctor_get(v_snd_3801_, 0);
lean_inc(v_fst_3804_);
lean_dec(v_snd_3801_);
v_fst_3805_ = lean_ctor_get(v_snd_3802_, 0);
lean_inc(v_fst_3805_);
v_snd_3806_ = lean_ctor_get(v_snd_3802_, 1);
lean_inc(v_snd_3806_);
lean_dec(v_snd_3802_);
v_numParams_3807_ = lean_ctor_get(v_toMatcherInfo_3773_, 0);
lean_inc(v_numParams_3807_);
v_numDiscrs_3808_ = lean_ctor_get(v_toMatcherInfo_3773_, 1);
lean_inc(v_numDiscrs_3808_);
v_altInfos_3809_ = lean_ctor_get(v_toMatcherInfo_3773_, 2);
lean_inc_ref(v_altInfos_3809_);
v_uElimPos_x3f_3810_ = lean_ctor_get(v_toMatcherInfo_3773_, 3);
lean_inc_n(v_uElimPos_x3f_3810_, 2);
v_overlaps_3811_ = lean_ctor_get(v_toMatcherInfo_3773_, 5);
lean_inc_ref(v_overlaps_3811_);
lean_dec_ref(v_toMatcherInfo_3773_);
v___x_3812_ = lean_box(v___x_3784_);
v___x_3813_ = lean_box(v_useSplitter_3790_);
v___x_3814_ = lean_box(v_isCasesOn_3791_);
lean_inc(v_toBind_3780_);
lean_inc(v_toPure_3777_);
v___f_3815_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 34, 33);
lean_closure_set(v___f_3815_, 0, v_numParams_3807_);
lean_closure_set(v___f_3815_, 1, v_numDiscrs_3808_);
lean_closure_set(v___f_3815_, 2, v_altInfos_3809_);
lean_closure_set(v___f_3815_, 3, v_uElimPos_x3f_3810_);
lean_closure_set(v___f_3815_, 4, v_snd_3806_);
lean_closure_set(v___f_3815_, 5, v_overlaps_3811_);
lean_closure_set(v___f_3815_, 6, v_matcherName_3774_);
lean_closure_set(v___f_3815_, 7, v_params_x27_3775_);
lean_closure_set(v___f_3815_, 8, v_fst_3803_);
lean_closure_set(v___f_3815_, 9, v_discrs_x27_3776_);
lean_closure_set(v___f_3815_, 10, v_toPure_3777_);
lean_closure_set(v___f_3815_, 11, v_onRemaining_3778_);
lean_closure_set(v___f_3815_, 12, v_remaining_3779_);
lean_closure_set(v___f_3815_, 13, v_toBind_3780_);
lean_closure_set(v___f_3815_, 14, v_inst_3781_);
lean_closure_set(v___f_3815_, 15, v_alts_3782_);
lean_closure_set(v___f_3815_, 16, v___f_3783_);
lean_closure_set(v___f_3815_, 17, v___x_3812_);
lean_closure_set(v___f_3815_, 18, v_inst_3785_);
lean_closure_set(v___f_3815_, 19, v_onAlt_3786_);
lean_closure_set(v___f_3815_, 20, v_inst_3787_);
lean_closure_set(v___f_3815_, 21, v___f_3788_);
lean_closure_set(v___f_3815_, 22, v_matcherApp_3789_);
lean_closure_set(v___f_3815_, 23, v___x_3813_);
lean_closure_set(v___f_3815_, 24, v___x_3814_);
lean_closure_set(v___f_3815_, 25, v___f_3792_);
lean_closure_set(v___f_3815_, 26, v___x_3793_);
lean_closure_set(v___f_3815_, 27, v___x_3794_);
lean_closure_set(v___f_3815_, 28, v_toMonadExceptOf_3795_);
lean_closure_set(v___f_3815_, 29, v___f_3796_);
lean_closure_set(v___f_3815_, 30, v_numDiscrEqs_3797_);
lean_closure_set(v___f_3815_, 31, v_fst_3805_);
lean_closure_set(v___f_3815_, 32, v___f_3798_);
if (lean_obj_tag(v_uElimPos_x3f_3810_) == 0)
{
lean_object* v___f_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_dec(v_fst_3804_);
v___f_3816_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3816_, 0, v___f_3815_);
v___x_3817_ = lean_apply_2(v_toPure_3777_, lean_box(0), v_matcherLevels_3799_);
v___x_3818_ = lean_apply_4(v_toBind_3780_, lean_box(0), lean_box(0), v___x_3817_, v___f_3816_);
return v___x_3818_;
}
else
{
lean_object* v_val_3819_; lean_object* v___f_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_val_3819_ = lean_ctor_get(v_uElimPos_x3f_3810_, 0);
lean_inc(v_val_3819_);
lean_dec_ref_known(v_uElimPos_x3f_3810_, 1);
v___f_3820_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3820_, 0, v___f_3815_);
v___x_3821_ = lean_array_set(v_matcherLevels_3799_, v_val_3819_, v_fst_3804_);
lean_dec(v_val_3819_);
v___x_3822_ = lean_apply_2(v_toPure_3777_, lean_box(0), v___x_3821_);
v___x_3823_ = lean_apply_4(v_toBind_3780_, lean_box(0), lean_box(0), v___x_3822_, v___f_3820_);
return v___x_3823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3824_ = _args[0];
lean_object* v_matcherName_3825_ = _args[1];
lean_object* v_params_x27_3826_ = _args[2];
lean_object* v_discrs_x27_3827_ = _args[3];
lean_object* v_toPure_3828_ = _args[4];
lean_object* v_onRemaining_3829_ = _args[5];
lean_object* v_remaining_3830_ = _args[6];
lean_object* v_toBind_3831_ = _args[7];
lean_object* v_inst_3832_ = _args[8];
lean_object* v_alts_3833_ = _args[9];
lean_object* v___f_3834_ = _args[10];
lean_object* v___x_3835_ = _args[11];
lean_object* v_inst_3836_ = _args[12];
lean_object* v_onAlt_3837_ = _args[13];
lean_object* v_inst_3838_ = _args[14];
lean_object* v___f_3839_ = _args[15];
lean_object* v_matcherApp_3840_ = _args[16];
lean_object* v_useSplitter_3841_ = _args[17];
lean_object* v_isCasesOn_3842_ = _args[18];
lean_object* v___f_3843_ = _args[19];
lean_object* v___x_3844_ = _args[20];
lean_object* v___x_3845_ = _args[21];
lean_object* v_toMonadExceptOf_3846_ = _args[22];
lean_object* v___f_3847_ = _args[23];
lean_object* v_numDiscrEqs_3848_ = _args[24];
lean_object* v___f_3849_ = _args[25];
lean_object* v_matcherLevels_3850_ = _args[26];
lean_object* v_____x_3851_ = _args[27];
_start:
{
uint8_t v___x_14661__boxed_3852_; uint8_t v_useSplitter_boxed_3853_; uint8_t v_isCasesOn_boxed_3854_; lean_object* v_res_3855_; 
v___x_14661__boxed_3852_ = lean_unbox(v___x_3835_);
v_useSplitter_boxed_3853_ = lean_unbox(v_useSplitter_3841_);
v_isCasesOn_boxed_3854_ = lean_unbox(v_isCasesOn_3842_);
v_res_3855_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3824_, v_matcherName_3825_, v_params_x27_3826_, v_discrs_x27_3827_, v_toPure_3828_, v_onRemaining_3829_, v_remaining_3830_, v_toBind_3831_, v_inst_3832_, v_alts_3833_, v___f_3834_, v___x_14661__boxed_3852_, v_inst_3836_, v_onAlt_3837_, v_inst_3838_, v___f_3839_, v_matcherApp_3840_, v_useSplitter_boxed_3853_, v_isCasesOn_boxed_3854_, v___f_3843_, v___x_3844_, v___x_3845_, v_toMonadExceptOf_3846_, v___f_3847_, v_numDiscrEqs_3848_, v___f_3849_, v_matcherLevels_3850_, v_____x_3851_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3856_, lean_object* v_inst_3857_, lean_object* v_toBind_3858_, lean_object* v_toMatcherInfo_3859_, lean_object* v_inst_3860_, lean_object* v___f_3861_, lean_object* v_onMotive_3862_, lean_object* v_discrs_3863_, lean_object* v_inst_3864_, lean_object* v_matcherName_3865_, lean_object* v_params_x27_3866_, lean_object* v_onRemaining_3867_, lean_object* v_remaining_3868_, lean_object* v_inst_3869_, lean_object* v_alts_3870_, lean_object* v___f_3871_, lean_object* v_onAlt_3872_, lean_object* v___f_3873_, lean_object* v_matcherApp_3874_, uint8_t v_useSplitter_3875_, uint8_t v_isCasesOn_3876_, lean_object* v___f_3877_, lean_object* v___x_3878_, lean_object* v___x_3879_, lean_object* v_toMonadExceptOf_3880_, lean_object* v___f_3881_, lean_object* v_numDiscrEqs_3882_, lean_object* v___f_3883_, lean_object* v_matcherLevels_3884_, lean_object* v_motive_3885_, lean_object* v_discrs_x27_3886_){
_start:
{
lean_object* v___f_3887_; uint8_t v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___f_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
lean_inc_ref_n(v_inst_3860_, 2);
lean_inc_ref(v_discrs_x27_3886_);
lean_inc_ref(v_toMatcherInfo_3859_);
lean_inc_n(v_toBind_3858_, 2);
lean_inc(v_inst_3857_);
lean_inc(v_toPure_3856_);
v___f_3887_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3887_, 0, v_toPure_3856_);
lean_closure_set(v___f_3887_, 1, v_inst_3857_);
lean_closure_set(v___f_3887_, 2, v_toBind_3858_);
lean_closure_set(v___f_3887_, 3, v_toMatcherInfo_3859_);
lean_closure_set(v___f_3887_, 4, v_discrs_x27_3886_);
lean_closure_set(v___f_3887_, 5, v_inst_3860_);
lean_closure_set(v___f_3887_, 6, v___f_3861_);
lean_closure_set(v___f_3887_, 7, v_onMotive_3862_);
lean_closure_set(v___f_3887_, 8, v_discrs_3863_);
lean_closure_set(v___f_3887_, 9, v_inst_3864_);
v___x_3888_ = 0;
v___x_3889_ = lean_box(v___x_3888_);
v___x_3890_ = lean_box(v_useSplitter_3875_);
v___x_3891_ = lean_box(v_isCasesOn_3876_);
lean_inc_ref(v_inst_3869_);
v___f_3892_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 28, 27);
lean_closure_set(v___f_3892_, 0, v_toMatcherInfo_3859_);
lean_closure_set(v___f_3892_, 1, v_matcherName_3865_);
lean_closure_set(v___f_3892_, 2, v_params_x27_3866_);
lean_closure_set(v___f_3892_, 3, v_discrs_x27_3886_);
lean_closure_set(v___f_3892_, 4, v_toPure_3856_);
lean_closure_set(v___f_3892_, 5, v_onRemaining_3867_);
lean_closure_set(v___f_3892_, 6, v_remaining_3868_);
lean_closure_set(v___f_3892_, 7, v_toBind_3858_);
lean_closure_set(v___f_3892_, 8, v_inst_3869_);
lean_closure_set(v___f_3892_, 9, v_alts_3870_);
lean_closure_set(v___f_3892_, 10, v___f_3871_);
lean_closure_set(v___f_3892_, 11, v___x_3889_);
lean_closure_set(v___f_3892_, 12, v_inst_3857_);
lean_closure_set(v___f_3892_, 13, v_onAlt_3872_);
lean_closure_set(v___f_3892_, 14, v_inst_3860_);
lean_closure_set(v___f_3892_, 15, v___f_3873_);
lean_closure_set(v___f_3892_, 16, v_matcherApp_3874_);
lean_closure_set(v___f_3892_, 17, v___x_3890_);
lean_closure_set(v___f_3892_, 18, v___x_3891_);
lean_closure_set(v___f_3892_, 19, v___f_3877_);
lean_closure_set(v___f_3892_, 20, v___x_3878_);
lean_closure_set(v___f_3892_, 21, v___x_3879_);
lean_closure_set(v___f_3892_, 22, v_toMonadExceptOf_3880_);
lean_closure_set(v___f_3892_, 23, v___f_3881_);
lean_closure_set(v___f_3892_, 24, v_numDiscrEqs_3882_);
lean_closure_set(v___f_3892_, 25, v___f_3883_);
lean_closure_set(v___f_3892_, 26, v_matcherLevels_3884_);
v___x_3893_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3869_, v_inst_3860_, v_motive_3885_, v___f_3887_, v___x_3888_);
v___x_3894_ = lean_apply_4(v_toBind_3858_, lean_box(0), lean_box(0), v___x_3893_, v___f_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3895_ = _args[0];
lean_object* v_inst_3896_ = _args[1];
lean_object* v_toBind_3897_ = _args[2];
lean_object* v_toMatcherInfo_3898_ = _args[3];
lean_object* v_inst_3899_ = _args[4];
lean_object* v___f_3900_ = _args[5];
lean_object* v_onMotive_3901_ = _args[6];
lean_object* v_discrs_3902_ = _args[7];
lean_object* v_inst_3903_ = _args[8];
lean_object* v_matcherName_3904_ = _args[9];
lean_object* v_params_x27_3905_ = _args[10];
lean_object* v_onRemaining_3906_ = _args[11];
lean_object* v_remaining_3907_ = _args[12];
lean_object* v_inst_3908_ = _args[13];
lean_object* v_alts_3909_ = _args[14];
lean_object* v___f_3910_ = _args[15];
lean_object* v_onAlt_3911_ = _args[16];
lean_object* v___f_3912_ = _args[17];
lean_object* v_matcherApp_3913_ = _args[18];
lean_object* v_useSplitter_3914_ = _args[19];
lean_object* v_isCasesOn_3915_ = _args[20];
lean_object* v___f_3916_ = _args[21];
lean_object* v___x_3917_ = _args[22];
lean_object* v___x_3918_ = _args[23];
lean_object* v_toMonadExceptOf_3919_ = _args[24];
lean_object* v___f_3920_ = _args[25];
lean_object* v_numDiscrEqs_3921_ = _args[26];
lean_object* v___f_3922_ = _args[27];
lean_object* v_matcherLevels_3923_ = _args[28];
lean_object* v_motive_3924_ = _args[29];
lean_object* v_discrs_x27_3925_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3926_; uint8_t v_isCasesOn_boxed_3927_; lean_object* v_res_3928_; 
v_useSplitter_boxed_3926_ = lean_unbox(v_useSplitter_3914_);
v_isCasesOn_boxed_3927_ = lean_unbox(v_isCasesOn_3915_);
v_res_3928_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3895_, v_inst_3896_, v_toBind_3897_, v_toMatcherInfo_3898_, v_inst_3899_, v___f_3900_, v_onMotive_3901_, v_discrs_3902_, v_inst_3903_, v_matcherName_3904_, v_params_x27_3905_, v_onRemaining_3906_, v_remaining_3907_, v_inst_3908_, v_alts_3909_, v___f_3910_, v_onAlt_3911_, v___f_3912_, v_matcherApp_3913_, v_useSplitter_boxed_3926_, v_isCasesOn_boxed_3927_, v___f_3916_, v___x_3917_, v___x_3918_, v_toMonadExceptOf_3919_, v___f_3920_, v_numDiscrEqs_3921_, v___f_3922_, v_matcherLevels_3923_, v_motive_3924_, v_discrs_x27_3925_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3929_, lean_object* v_inst_3930_, lean_object* v_toBind_3931_, lean_object* v_toMatcherInfo_3932_, lean_object* v_inst_3933_, lean_object* v___f_3934_, lean_object* v_onMotive_3935_, lean_object* v_discrs_3936_, lean_object* v_inst_3937_, lean_object* v_matcherName_3938_, lean_object* v_onRemaining_3939_, lean_object* v_remaining_3940_, lean_object* v_inst_3941_, lean_object* v_alts_3942_, lean_object* v___f_3943_, lean_object* v_onAlt_3944_, lean_object* v___f_3945_, lean_object* v_matcherApp_3946_, uint8_t v_useSplitter_3947_, uint8_t v_isCasesOn_3948_, lean_object* v___f_3949_, lean_object* v___x_3950_, lean_object* v___x_3951_, lean_object* v_toMonadExceptOf_3952_, lean_object* v___f_3953_, lean_object* v_numDiscrEqs_3954_, lean_object* v___f_3955_, lean_object* v_matcherLevels_3956_, lean_object* v_motive_3957_, lean_object* v_onParams_3958_, lean_object* v_params_x27_3959_){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___f_3962_; size_t v_sz_3963_; size_t v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3960_ = lean_box(v_useSplitter_3947_);
v___x_3961_ = lean_box(v_isCasesOn_3948_);
lean_inc_ref(v_discrs_3936_);
lean_inc_ref(v_inst_3933_);
lean_inc(v_toBind_3931_);
v___f_3962_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 31, 30);
lean_closure_set(v___f_3962_, 0, v_toPure_3929_);
lean_closure_set(v___f_3962_, 1, v_inst_3930_);
lean_closure_set(v___f_3962_, 2, v_toBind_3931_);
lean_closure_set(v___f_3962_, 3, v_toMatcherInfo_3932_);
lean_closure_set(v___f_3962_, 4, v_inst_3933_);
lean_closure_set(v___f_3962_, 5, v___f_3934_);
lean_closure_set(v___f_3962_, 6, v_onMotive_3935_);
lean_closure_set(v___f_3962_, 7, v_discrs_3936_);
lean_closure_set(v___f_3962_, 8, v_inst_3937_);
lean_closure_set(v___f_3962_, 9, v_matcherName_3938_);
lean_closure_set(v___f_3962_, 10, v_params_x27_3959_);
lean_closure_set(v___f_3962_, 11, v_onRemaining_3939_);
lean_closure_set(v___f_3962_, 12, v_remaining_3940_);
lean_closure_set(v___f_3962_, 13, v_inst_3941_);
lean_closure_set(v___f_3962_, 14, v_alts_3942_);
lean_closure_set(v___f_3962_, 15, v___f_3943_);
lean_closure_set(v___f_3962_, 16, v_onAlt_3944_);
lean_closure_set(v___f_3962_, 17, v___f_3945_);
lean_closure_set(v___f_3962_, 18, v_matcherApp_3946_);
lean_closure_set(v___f_3962_, 19, v___x_3960_);
lean_closure_set(v___f_3962_, 20, v___x_3961_);
lean_closure_set(v___f_3962_, 21, v___f_3949_);
lean_closure_set(v___f_3962_, 22, v___x_3950_);
lean_closure_set(v___f_3962_, 23, v___x_3951_);
lean_closure_set(v___f_3962_, 24, v_toMonadExceptOf_3952_);
lean_closure_set(v___f_3962_, 25, v___f_3953_);
lean_closure_set(v___f_3962_, 26, v_numDiscrEqs_3954_);
lean_closure_set(v___f_3962_, 27, v___f_3955_);
lean_closure_set(v___f_3962_, 28, v_matcherLevels_3956_);
lean_closure_set(v___f_3962_, 29, v_motive_3957_);
v_sz_3963_ = lean_array_size(v_discrs_3936_);
v___x_3964_ = ((size_t)0ULL);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3933_, v_onParams_3958_, v_sz_3963_, v___x_3964_, v_discrs_3936_);
v___x_3966_ = lean_apply_4(v_toBind_3931_, lean_box(0), lean_box(0), v___x_3965_, v___f_3962_);
return v___x_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3967_ = _args[0];
lean_object* v_inst_3968_ = _args[1];
lean_object* v_toBind_3969_ = _args[2];
lean_object* v_toMatcherInfo_3970_ = _args[3];
lean_object* v_inst_3971_ = _args[4];
lean_object* v___f_3972_ = _args[5];
lean_object* v_onMotive_3973_ = _args[6];
lean_object* v_discrs_3974_ = _args[7];
lean_object* v_inst_3975_ = _args[8];
lean_object* v_matcherName_3976_ = _args[9];
lean_object* v_onRemaining_3977_ = _args[10];
lean_object* v_remaining_3978_ = _args[11];
lean_object* v_inst_3979_ = _args[12];
lean_object* v_alts_3980_ = _args[13];
lean_object* v___f_3981_ = _args[14];
lean_object* v_onAlt_3982_ = _args[15];
lean_object* v___f_3983_ = _args[16];
lean_object* v_matcherApp_3984_ = _args[17];
lean_object* v_useSplitter_3985_ = _args[18];
lean_object* v_isCasesOn_3986_ = _args[19];
lean_object* v___f_3987_ = _args[20];
lean_object* v___x_3988_ = _args[21];
lean_object* v___x_3989_ = _args[22];
lean_object* v_toMonadExceptOf_3990_ = _args[23];
lean_object* v___f_3991_ = _args[24];
lean_object* v_numDiscrEqs_3992_ = _args[25];
lean_object* v___f_3993_ = _args[26];
lean_object* v_matcherLevels_3994_ = _args[27];
lean_object* v_motive_3995_ = _args[28];
lean_object* v_onParams_3996_ = _args[29];
lean_object* v_params_x27_3997_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3998_; uint8_t v_isCasesOn_boxed_3999_; lean_object* v_res_4000_; 
v_useSplitter_boxed_3998_ = lean_unbox(v_useSplitter_3985_);
v_isCasesOn_boxed_3999_ = lean_unbox(v_isCasesOn_3986_);
v_res_4000_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3967_, v_inst_3968_, v_toBind_3969_, v_toMatcherInfo_3970_, v_inst_3971_, v___f_3972_, v_onMotive_3973_, v_discrs_3974_, v_inst_3975_, v_matcherName_3976_, v_onRemaining_3977_, v_remaining_3978_, v_inst_3979_, v_alts_3980_, v___f_3981_, v_onAlt_3982_, v___f_3983_, v_matcherApp_3984_, v_useSplitter_boxed_3998_, v_isCasesOn_boxed_3999_, v___f_3987_, v___x_3988_, v___x_3989_, v_toMonadExceptOf_3990_, v___f_3991_, v_numDiscrEqs_3992_, v___f_3993_, v_matcherLevels_3994_, v_motive_3995_, v_onParams_3996_, v_params_x27_3997_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_4001_, lean_object* v_inst_4002_, lean_object* v_toBind_4003_, lean_object* v_toMatcherInfo_4004_, lean_object* v_inst_4005_, lean_object* v___f_4006_, lean_object* v_onMotive_4007_, lean_object* v_discrs_4008_, lean_object* v_inst_4009_, lean_object* v_matcherName_4010_, lean_object* v_onRemaining_4011_, lean_object* v_remaining_4012_, lean_object* v_inst_4013_, lean_object* v_alts_4014_, lean_object* v___f_4015_, lean_object* v_onAlt_4016_, lean_object* v___f_4017_, lean_object* v_matcherApp_4018_, uint8_t v_useSplitter_4019_, uint8_t v_isCasesOn_4020_, lean_object* v___f_4021_, lean_object* v___x_4022_, lean_object* v___x_4023_, lean_object* v_toMonadExceptOf_4024_, lean_object* v___f_4025_, lean_object* v___f_4026_, lean_object* v_matcherLevels_4027_, lean_object* v_motive_4028_, lean_object* v_onParams_4029_, lean_object* v_params_4030_, lean_object* v_numDiscrEqs_4031_){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___f_4034_; size_t v_sz_4035_; size_t v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4032_ = lean_box(v_useSplitter_4019_);
v___x_4033_ = lean_box(v_isCasesOn_4020_);
lean_inc(v_onParams_4029_);
lean_inc_ref(v_inst_4005_);
lean_inc(v_toBind_4003_);
v___f_4034_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 31, 30);
lean_closure_set(v___f_4034_, 0, v_toPure_4001_);
lean_closure_set(v___f_4034_, 1, v_inst_4002_);
lean_closure_set(v___f_4034_, 2, v_toBind_4003_);
lean_closure_set(v___f_4034_, 3, v_toMatcherInfo_4004_);
lean_closure_set(v___f_4034_, 4, v_inst_4005_);
lean_closure_set(v___f_4034_, 5, v___f_4006_);
lean_closure_set(v___f_4034_, 6, v_onMotive_4007_);
lean_closure_set(v___f_4034_, 7, v_discrs_4008_);
lean_closure_set(v___f_4034_, 8, v_inst_4009_);
lean_closure_set(v___f_4034_, 9, v_matcherName_4010_);
lean_closure_set(v___f_4034_, 10, v_onRemaining_4011_);
lean_closure_set(v___f_4034_, 11, v_remaining_4012_);
lean_closure_set(v___f_4034_, 12, v_inst_4013_);
lean_closure_set(v___f_4034_, 13, v_alts_4014_);
lean_closure_set(v___f_4034_, 14, v___f_4015_);
lean_closure_set(v___f_4034_, 15, v_onAlt_4016_);
lean_closure_set(v___f_4034_, 16, v___f_4017_);
lean_closure_set(v___f_4034_, 17, v_matcherApp_4018_);
lean_closure_set(v___f_4034_, 18, v___x_4032_);
lean_closure_set(v___f_4034_, 19, v___x_4033_);
lean_closure_set(v___f_4034_, 20, v___f_4021_);
lean_closure_set(v___f_4034_, 21, v___x_4022_);
lean_closure_set(v___f_4034_, 22, v___x_4023_);
lean_closure_set(v___f_4034_, 23, v_toMonadExceptOf_4024_);
lean_closure_set(v___f_4034_, 24, v___f_4025_);
lean_closure_set(v___f_4034_, 25, v_numDiscrEqs_4031_);
lean_closure_set(v___f_4034_, 26, v___f_4026_);
lean_closure_set(v___f_4034_, 27, v_matcherLevels_4027_);
lean_closure_set(v___f_4034_, 28, v_motive_4028_);
lean_closure_set(v___f_4034_, 29, v_onParams_4029_);
v_sz_4035_ = lean_array_size(v_params_4030_);
v___x_4036_ = ((size_t)0ULL);
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4005_, v_onParams_4029_, v_sz_4035_, v___x_4036_, v_params_4030_);
v___x_4038_ = lean_apply_4(v_toBind_4003_, lean_box(0), lean_box(0), v___x_4037_, v___f_4034_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4039_ = _args[0];
lean_object* v_inst_4040_ = _args[1];
lean_object* v_toBind_4041_ = _args[2];
lean_object* v_toMatcherInfo_4042_ = _args[3];
lean_object* v_inst_4043_ = _args[4];
lean_object* v___f_4044_ = _args[5];
lean_object* v_onMotive_4045_ = _args[6];
lean_object* v_discrs_4046_ = _args[7];
lean_object* v_inst_4047_ = _args[8];
lean_object* v_matcherName_4048_ = _args[9];
lean_object* v_onRemaining_4049_ = _args[10];
lean_object* v_remaining_4050_ = _args[11];
lean_object* v_inst_4051_ = _args[12];
lean_object* v_alts_4052_ = _args[13];
lean_object* v___f_4053_ = _args[14];
lean_object* v_onAlt_4054_ = _args[15];
lean_object* v___f_4055_ = _args[16];
lean_object* v_matcherApp_4056_ = _args[17];
lean_object* v_useSplitter_4057_ = _args[18];
lean_object* v_isCasesOn_4058_ = _args[19];
lean_object* v___f_4059_ = _args[20];
lean_object* v___x_4060_ = _args[21];
lean_object* v___x_4061_ = _args[22];
lean_object* v_toMonadExceptOf_4062_ = _args[23];
lean_object* v___f_4063_ = _args[24];
lean_object* v___f_4064_ = _args[25];
lean_object* v_matcherLevels_4065_ = _args[26];
lean_object* v_motive_4066_ = _args[27];
lean_object* v_onParams_4067_ = _args[28];
lean_object* v_params_4068_ = _args[29];
lean_object* v_numDiscrEqs_4069_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4070_; uint8_t v_isCasesOn_boxed_4071_; lean_object* v_res_4072_; 
v_useSplitter_boxed_4070_ = lean_unbox(v_useSplitter_4057_);
v_isCasesOn_boxed_4071_ = lean_unbox(v_isCasesOn_4058_);
v_res_4072_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4039_, v_inst_4040_, v_toBind_4041_, v_toMatcherInfo_4042_, v_inst_4043_, v___f_4044_, v_onMotive_4045_, v_discrs_4046_, v_inst_4047_, v_matcherName_4048_, v_onRemaining_4049_, v_remaining_4050_, v_inst_4051_, v_alts_4052_, v___f_4053_, v_onAlt_4054_, v___f_4055_, v_matcherApp_4056_, v_useSplitter_boxed_4070_, v_isCasesOn_boxed_4071_, v___f_4059_, v___x_4060_, v___x_4061_, v_toMonadExceptOf_4062_, v___f_4063_, v___f_4064_, v_matcherLevels_4065_, v_motive_4066_, v_onParams_4067_, v_params_4068_, v_numDiscrEqs_4069_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4073_, lean_object* v_numDiscrEqs_4074_){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_apply_1(v___f_4073_, v_numDiscrEqs_4074_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4081_ = l_Lean_stringToMessageData(v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4082_, lean_object* v_inst_4083_, lean_object* v_inst_4084_, lean_object* v_toBind_4085_, lean_object* v___f_4086_, lean_object* v_toPure_4087_, lean_object* v___f_4088_, lean_object* v_____do__lift_4089_){
_start:
{
if (lean_obj_tag(v_____do__lift_4089_) == 0)
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; 
lean_dec(v___f_4088_);
lean_dec(v_toPure_4087_);
v___x_4090_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4091_ = l_Lean_MessageData_ofName(v_matcherName_4082_);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4092_);
lean_ctor_set(v___x_4094_, 1, v___x_4093_);
v___x_4095_ = l_Lean_throwError___redArg(v_inst_4083_, v_inst_4084_, v___x_4094_);
v___x_4096_ = lean_apply_4(v_toBind_4085_, lean_box(0), lean_box(0), v___x_4095_, v___f_4086_);
return v___x_4096_;
}
else
{
lean_object* v_val_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
lean_dec(v___f_4086_);
lean_dec_ref(v_inst_4084_);
lean_dec_ref(v_inst_4083_);
lean_dec(v_matcherName_4082_);
v_val_4097_ = lean_ctor_get(v_____do__lift_4089_, 0);
v___x_4098_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4097_);
v___x_4099_ = lean_apply_2(v_toPure_4087_, lean_box(0), v___x_4098_);
v___x_4100_ = lean_apply_4(v_toBind_4085_, lean_box(0), lean_box(0), v___x_4099_, v___f_4088_);
return v___x_4100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4101_, lean_object* v_inst_4102_, lean_object* v_inst_4103_, lean_object* v_toBind_4104_, lean_object* v___f_4105_, lean_object* v_toPure_4106_, lean_object* v___f_4107_, lean_object* v_____do__lift_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4101_, v_inst_4102_, v_inst_4103_, v_toBind_4104_, v___f_4105_, v_toPure_4106_, v___f_4107_, v_____do__lift_4108_);
lean_dec(v_____do__lift_4108_);
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4110_, lean_object* v_toPure_4111_, lean_object* v_inst_4112_, lean_object* v_toBind_4113_, lean_object* v_inst_4114_, lean_object* v___f_4115_, lean_object* v_onMotive_4116_, lean_object* v_inst_4117_, lean_object* v_onRemaining_4118_, lean_object* v_inst_4119_, lean_object* v___f_4120_, lean_object* v_onAlt_4121_, lean_object* v___f_4122_, uint8_t v_useSplitter_4123_, lean_object* v___f_4124_, lean_object* v___x_4125_, lean_object* v___x_4126_, lean_object* v_toMonadExceptOf_4127_, lean_object* v___f_4128_, lean_object* v___f_4129_, lean_object* v_onParams_4130_, lean_object* v_inst_4131_, lean_object* v_____do__lift_4132_){
_start:
{
lean_object* v_toMatcherInfo_4133_; lean_object* v_matcherName_4134_; lean_object* v_matcherLevels_4135_; lean_object* v_params_4136_; lean_object* v_motive_4137_; lean_object* v_discrs_4138_; lean_object* v_alts_4139_; lean_object* v_remaining_4140_; uint8_t v_isCasesOn_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___f_4144_; 
v_toMatcherInfo_4133_ = lean_ctor_get(v_matcherApp_4110_, 0);
lean_inc_ref(v_toMatcherInfo_4133_);
v_matcherName_4134_ = lean_ctor_get(v_matcherApp_4110_, 1);
lean_inc_n(v_matcherName_4134_, 3);
v_matcherLevels_4135_ = lean_ctor_get(v_matcherApp_4110_, 2);
lean_inc_ref(v_matcherLevels_4135_);
v_params_4136_ = lean_ctor_get(v_matcherApp_4110_, 3);
lean_inc_ref(v_params_4136_);
v_motive_4137_ = lean_ctor_get(v_matcherApp_4110_, 4);
lean_inc_ref(v_motive_4137_);
v_discrs_4138_ = lean_ctor_get(v_matcherApp_4110_, 5);
lean_inc_ref(v_discrs_4138_);
v_alts_4139_ = lean_ctor_get(v_matcherApp_4110_, 6);
lean_inc_ref(v_alts_4139_);
v_remaining_4140_ = lean_ctor_get(v_matcherApp_4110_, 7);
lean_inc_ref(v_remaining_4140_);
v_isCasesOn_4141_ = l_Lean_isCasesOnRecursor(v_____do__lift_4132_, v_matcherName_4134_);
v___x_4142_ = lean_box(v_useSplitter_4123_);
v___x_4143_ = lean_box(v_isCasesOn_4141_);
lean_inc_ref(v_inst_4117_);
lean_inc_ref(v_inst_4114_);
lean_inc(v_toBind_4113_);
lean_inc(v_toPure_4111_);
v___f_4144_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 31, 30);
lean_closure_set(v___f_4144_, 0, v_toPure_4111_);
lean_closure_set(v___f_4144_, 1, v_inst_4112_);
lean_closure_set(v___f_4144_, 2, v_toBind_4113_);
lean_closure_set(v___f_4144_, 3, v_toMatcherInfo_4133_);
lean_closure_set(v___f_4144_, 4, v_inst_4114_);
lean_closure_set(v___f_4144_, 5, v___f_4115_);
lean_closure_set(v___f_4144_, 6, v_onMotive_4116_);
lean_closure_set(v___f_4144_, 7, v_discrs_4138_);
lean_closure_set(v___f_4144_, 8, v_inst_4117_);
lean_closure_set(v___f_4144_, 9, v_matcherName_4134_);
lean_closure_set(v___f_4144_, 10, v_onRemaining_4118_);
lean_closure_set(v___f_4144_, 11, v_remaining_4140_);
lean_closure_set(v___f_4144_, 12, v_inst_4119_);
lean_closure_set(v___f_4144_, 13, v_alts_4139_);
lean_closure_set(v___f_4144_, 14, v___f_4120_);
lean_closure_set(v___f_4144_, 15, v_onAlt_4121_);
lean_closure_set(v___f_4144_, 16, v___f_4122_);
lean_closure_set(v___f_4144_, 17, v_matcherApp_4110_);
lean_closure_set(v___f_4144_, 18, v___x_4142_);
lean_closure_set(v___f_4144_, 19, v___x_4143_);
lean_closure_set(v___f_4144_, 20, v___f_4124_);
lean_closure_set(v___f_4144_, 21, v___x_4125_);
lean_closure_set(v___f_4144_, 22, v___x_4126_);
lean_closure_set(v___f_4144_, 23, v_toMonadExceptOf_4127_);
lean_closure_set(v___f_4144_, 24, v___f_4128_);
lean_closure_set(v___f_4144_, 25, v___f_4129_);
lean_closure_set(v___f_4144_, 26, v_matcherLevels_4135_);
lean_closure_set(v___f_4144_, 27, v_motive_4137_);
lean_closure_set(v___f_4144_, 28, v_onParams_4130_);
lean_closure_set(v___f_4144_, 29, v_params_4136_);
if (v_isCasesOn_4141_ == 0)
{
lean_object* v___f_4145_; lean_object* v___f_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___f_4145_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4145_, 0, v___f_4144_);
lean_inc_ref(v___f_4145_);
lean_inc(v_toBind_4113_);
lean_inc_ref(v_inst_4114_);
lean_inc(v_matcherName_4134_);
v___f_4146_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4146_, 0, v_matcherName_4134_);
lean_closure_set(v___f_4146_, 1, v_inst_4114_);
lean_closure_set(v___f_4146_, 2, v_inst_4117_);
lean_closure_set(v___f_4146_, 3, v_toBind_4113_);
lean_closure_set(v___f_4146_, 4, v___f_4145_);
lean_closure_set(v___f_4146_, 5, v_toPure_4111_);
lean_closure_set(v___f_4146_, 6, v___f_4145_);
v___x_4147_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4114_, v_inst_4131_, v_matcherName_4134_);
v___x_4148_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v___x_4147_, v___f_4146_);
return v___x_4148_;
}
else
{
lean_object* v___f_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
lean_dec(v_matcherName_4134_);
lean_dec_ref(v_inst_4131_);
lean_dec_ref(v_inst_4117_);
lean_dec_ref(v_inst_4114_);
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4149_, 0, v___f_4144_);
v___x_4150_ = lean_unsigned_to_nat(0u);
v___x_4151_ = lean_apply_2(v_toPure_4111_, lean_box(0), v___x_4150_);
v___x_4152_ = lean_apply_4(v_toBind_4113_, lean_box(0), lean_box(0), v___x_4151_, v___f_4149_);
return v___x_4152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4153_ = _args[0];
lean_object* v_toPure_4154_ = _args[1];
lean_object* v_inst_4155_ = _args[2];
lean_object* v_toBind_4156_ = _args[3];
lean_object* v_inst_4157_ = _args[4];
lean_object* v___f_4158_ = _args[5];
lean_object* v_onMotive_4159_ = _args[6];
lean_object* v_inst_4160_ = _args[7];
lean_object* v_onRemaining_4161_ = _args[8];
lean_object* v_inst_4162_ = _args[9];
lean_object* v___f_4163_ = _args[10];
lean_object* v_onAlt_4164_ = _args[11];
lean_object* v___f_4165_ = _args[12];
lean_object* v_useSplitter_4166_ = _args[13];
lean_object* v___f_4167_ = _args[14];
lean_object* v___x_4168_ = _args[15];
lean_object* v___x_4169_ = _args[16];
lean_object* v_toMonadExceptOf_4170_ = _args[17];
lean_object* v___f_4171_ = _args[18];
lean_object* v___f_4172_ = _args[19];
lean_object* v_onParams_4173_ = _args[20];
lean_object* v_inst_4174_ = _args[21];
lean_object* v_____do__lift_4175_ = _args[22];
_start:
{
uint8_t v_useSplitter_boxed_4176_; lean_object* v_res_4177_; 
v_useSplitter_boxed_4176_ = lean_unbox(v_useSplitter_4166_);
v_res_4177_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4153_, v_toPure_4154_, v_inst_4155_, v_toBind_4156_, v_inst_4157_, v___f_4158_, v_onMotive_4159_, v_inst_4160_, v_onRemaining_4161_, v_inst_4162_, v___f_4163_, v_onAlt_4164_, v___f_4165_, v_useSplitter_boxed_4176_, v___f_4167_, v___x_4168_, v___x_4169_, v_toMonadExceptOf_4170_, v___f_4171_, v___f_4172_, v_onParams_4173_, v_inst_4174_, v_____do__lift_4175_);
return v_res_4177_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_4178_; 
v___x_4178_ = l_Subarray_empty___redArg();
return v___x_4178_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4181_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1);
v___x_4182_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
lean_ctor_set(v___x_4183_, 1, v___x_4181_);
return v___x_4183_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3(void){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Array_instInhabited___redArg();
return v___x_4184_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4(void){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4185_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2);
v___x_4186_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
lean_ctor_set(v___x_4187_, 1, v___x_4185_);
return v___x_4187_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5(void){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4);
v___x_4189_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4188_);
return v___x_4190_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6(void){
_start:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4191_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5);
v___x_4192_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
lean_ctor_set(v___x_4193_, 1, v___x_4191_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4196_, lean_object* v_inst_4197_, lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_matcherApp_4201_, uint8_t v_useSplitter_4202_, uint8_t v_addEqualities_4203_, lean_object* v_onParams_4204_, lean_object* v_onMotive_4205_, lean_object* v_onAlt_4206_, lean_object* v_onRemaining_4207_){
_start:
{
lean_object* v_toApplicative_4208_; lean_object* v_toBind_4209_; lean_object* v_getEnv_4210_; lean_object* v_toPure_4211_; lean_object* v_toMonadExceptOf_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___f_4215_; lean_object* v___f_4216_; lean_object* v___f_4217_; lean_object* v___x_4218_; lean_object* v___f_4219_; lean_object* v___x_4220_; lean_object* v___f_4221_; lean_object* v___f_4222_; lean_object* v___f_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___f_4226_; lean_object* v___x_4227_; 
v_toApplicative_4208_ = lean_ctor_get(v_inst_4198_, 0);
v_toBind_4209_ = lean_ctor_get(v_inst_4198_, 1);
lean_inc_n(v_toBind_4209_, 4);
v_getEnv_4210_ = lean_ctor_get(v_inst_4200_, 0);
lean_inc(v_getEnv_4210_);
v_toPure_4211_ = lean_ctor_get(v_toApplicative_4208_, 1);
lean_inc_n(v_toPure_4211_, 5);
v_toMonadExceptOf_4212_ = lean_ctor_get(v_inst_4199_, 0);
lean_inc_ref(v_toMonadExceptOf_4212_);
v___x_4213_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
lean_inc_ref_n(v_inst_4198_, 4);
v___x_4214_ = l_instInhabitedOfMonad___redArg(v_inst_4198_, v___x_4213_);
lean_inc_ref(v_inst_4199_);
v___f_4215_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4215_, 0, v_inst_4198_);
lean_closure_set(v___f_4215_, 1, v_inst_4199_);
lean_inc_n(v_inst_4196_, 3);
v___f_4216_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4216_, 0, v_inst_4196_);
v___f_4217_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4217_, 0, v_inst_4198_);
lean_closure_set(v___f_4217_, 1, v___f_4216_);
v___x_4218_ = l_Lean_instInhabitedExpr;
v___f_4219_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 6, 3);
lean_closure_set(v___f_4219_, 0, v_toPure_4211_);
lean_closure_set(v___f_4219_, 1, v_inst_4196_);
lean_closure_set(v___f_4219_, 2, v_toBind_4209_);
v___x_4220_ = lean_box(v_addEqualities_4203_);
v___f_4221_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4221_, 0, v_toPure_4211_);
lean_closure_set(v___f_4221_, 1, v___x_4220_);
lean_closure_set(v___f_4221_, 2, v_inst_4196_);
lean_closure_set(v___f_4221_, 3, v_toBind_4209_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11), 2, 1);
lean_closure_set(v___f_4222_, 0, v_toPure_4211_);
v___f_4223_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 2, 1);
lean_closure_set(v___f_4223_, 0, v_toPure_4211_);
v___x_4224_ = l_instInhabitedOfMonad___redArg(v_inst_4198_, v___x_4218_);
v___x_4225_ = lean_box(v_useSplitter_4202_);
v___f_4226_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 23, 22);
lean_closure_set(v___f_4226_, 0, v_matcherApp_4201_);
lean_closure_set(v___f_4226_, 1, v_toPure_4211_);
lean_closure_set(v___f_4226_, 2, v_inst_4196_);
lean_closure_set(v___f_4226_, 3, v_toBind_4209_);
lean_closure_set(v___f_4226_, 4, v_inst_4198_);
lean_closure_set(v___f_4226_, 5, v___f_4221_);
lean_closure_set(v___f_4226_, 6, v_onMotive_4205_);
lean_closure_set(v___f_4226_, 7, v_inst_4199_);
lean_closure_set(v___f_4226_, 8, v_onRemaining_4207_);
lean_closure_set(v___f_4226_, 9, v_inst_4197_);
lean_closure_set(v___f_4226_, 10, v___f_4223_);
lean_closure_set(v___f_4226_, 11, v_onAlt_4206_);
lean_closure_set(v___f_4226_, 12, v___f_4217_);
lean_closure_set(v___f_4226_, 13, v___x_4225_);
lean_closure_set(v___f_4226_, 14, v___f_4222_);
lean_closure_set(v___f_4226_, 15, v___x_4214_);
lean_closure_set(v___f_4226_, 16, v___x_4224_);
lean_closure_set(v___f_4226_, 17, v_toMonadExceptOf_4212_);
lean_closure_set(v___f_4226_, 18, v___f_4215_);
lean_closure_set(v___f_4226_, 19, v___f_4219_);
lean_closure_set(v___f_4226_, 20, v_onParams_4204_);
lean_closure_set(v___f_4226_, 21, v_inst_4200_);
v___x_4227_ = lean_apply_4(v_toBind_4209_, lean_box(0), lean_box(0), v_getEnv_4210_, v___f_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4228_, lean_object* v_inst_4229_, lean_object* v_inst_4230_, lean_object* v_inst_4231_, lean_object* v_inst_4232_, lean_object* v_matcherApp_4233_, lean_object* v_useSplitter_4234_, lean_object* v_addEqualities_4235_, lean_object* v_onParams_4236_, lean_object* v_onMotive_4237_, lean_object* v_onAlt_4238_, lean_object* v_onRemaining_4239_){
_start:
{
uint8_t v_useSplitter_boxed_4240_; uint8_t v_addEqualities_boxed_4241_; lean_object* v_res_4242_; 
v_useSplitter_boxed_4240_ = lean_unbox(v_useSplitter_4234_);
v_addEqualities_boxed_4241_ = lean_unbox(v_addEqualities_4235_);
v_res_4242_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4228_, v_inst_4229_, v_inst_4230_, v_inst_4231_, v_inst_4232_, v_matcherApp_4233_, v_useSplitter_boxed_4240_, v_addEqualities_boxed_4241_, v_onParams_4236_, v_onMotive_4237_, v_onAlt_4238_, v_onRemaining_4239_);
return v_res_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4243_, lean_object* v_inst_4244_, lean_object* v_inst_4245_, lean_object* v_inst_4246_, lean_object* v_inst_4247_, lean_object* v_inst_4248_, lean_object* v_inst_4249_, lean_object* v_inst_4250_, lean_object* v_inst_4251_, lean_object* v_matcherApp_4252_, uint8_t v_useSplitter_4253_, uint8_t v_addEqualities_4254_, lean_object* v_onParams_4255_, lean_object* v_onMotive_4256_, lean_object* v_onAlt_4257_, lean_object* v_onRemaining_4258_){
_start:
{
lean_object* v___x_4259_; 
v___x_4259_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4244_, v_inst_4245_, v_inst_4246_, v_inst_4247_, v_inst_4248_, v_matcherApp_4252_, v_useSplitter_4253_, v_addEqualities_4254_, v_onParams_4255_, v_onMotive_4256_, v_onAlt_4257_, v_onRemaining_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_inst_4263_, lean_object* v_inst_4264_, lean_object* v_inst_4265_, lean_object* v_inst_4266_, lean_object* v_inst_4267_, lean_object* v_inst_4268_, lean_object* v_matcherApp_4269_, lean_object* v_useSplitter_4270_, lean_object* v_addEqualities_4271_, lean_object* v_onParams_4272_, lean_object* v_onMotive_4273_, lean_object* v_onAlt_4274_, lean_object* v_onRemaining_4275_){
_start:
{
uint8_t v_useSplitter_boxed_4276_; uint8_t v_addEqualities_boxed_4277_; lean_object* v_res_4278_; 
v_useSplitter_boxed_4276_ = lean_unbox(v_useSplitter_4270_);
v_addEqualities_boxed_4277_ = lean_unbox(v_addEqualities_4271_);
v_res_4278_ = l_Lean_Meta_MatcherApp_transform(v_n_4260_, v_inst_4261_, v_inst_4262_, v_inst_4263_, v_inst_4264_, v_inst_4265_, v_inst_4266_, v_inst_4267_, v_inst_4268_, v_matcherApp_4269_, v_useSplitter_boxed_4276_, v_addEqualities_boxed_4277_, v_onParams_4272_, v_onMotive_4273_, v_onAlt_4274_, v_onRemaining_4275_);
lean_dec_ref(v_inst_4268_);
lean_dec(v_inst_4267_);
lean_dec_ref(v_inst_4266_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_){
_start:
{
lean_object* v___x_4285_; 
v___x_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4285_, 0, v___y_4279_);
return v___x_4285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_){
_start:
{
lean_object* v___x_4299_; 
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___y_4293_);
return v___x_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
return v_res_4306_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4307_, lean_object* v_opt_4308_){
_start:
{
lean_object* v_name_4309_; lean_object* v_defValue_4310_; lean_object* v_map_4311_; lean_object* v___x_4312_; 
v_name_4309_ = lean_ctor_get(v_opt_4308_, 0);
v_defValue_4310_ = lean_ctor_get(v_opt_4308_, 1);
v_map_4311_ = lean_ctor_get(v_opts_4307_, 0);
v___x_4312_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4311_, v_name_4309_);
if (lean_obj_tag(v___x_4312_) == 0)
{
uint8_t v___x_4313_; 
v___x_4313_ = lean_unbox(v_defValue_4310_);
return v___x_4313_;
}
else
{
lean_object* v_val_4314_; 
v_val_4314_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_val_4314_);
lean_dec_ref_known(v___x_4312_, 1);
if (lean_obj_tag(v_val_4314_) == 1)
{
uint8_t v_v_4315_; 
v_v_4315_ = lean_ctor_get_uint8(v_val_4314_, 0);
lean_dec_ref_known(v_val_4314_, 0);
return v_v_4315_;
}
else
{
uint8_t v___x_4316_; 
lean_dec(v_val_4314_);
v___x_4316_ = lean_unbox(v_defValue_4310_);
return v___x_4316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4317_, lean_object* v_opt_4318_){
_start:
{
uint8_t v_res_4319_; lean_object* v_r_4320_; 
v_res_4319_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4317_, v_opt_4318_);
lean_dec_ref(v_opt_4318_);
lean_dec_ref(v_opts_4317_);
v_r_4320_ = lean_box(v_res_4319_);
return v_r_4320_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_4329_, lean_object* v_x_4330_){
_start:
{
if (lean_obj_tag(v_x_4330_) == 1)
{
lean_object* v_pre_4331_; 
v_pre_4331_ = lean_ctor_get(v_x_4330_, 0);
switch(lean_obj_tag(v_pre_4331_))
{
case 1:
{
lean_object* v_pre_4332_; 
v_pre_4332_ = lean_ctor_get(v_pre_4331_, 0);
switch(lean_obj_tag(v_pre_4332_))
{
case 0:
{
lean_object* v_str_4333_; lean_object* v_str_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; 
v_str_4333_ = lean_ctor_get(v_x_4330_, 1);
v_str_4334_ = lean_ctor_get(v_pre_4331_, 1);
v___x_4335_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4336_ = lean_string_dec_eq(v_str_4334_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; uint8_t v___x_4338_; 
v___x_4337_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4338_ = lean_string_dec_eq(v_str_4334_, v___x_4337_);
if (v___x_4338_ == 0)
{
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; uint8_t v___x_4340_; 
v___x_4339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4340_ = lean_string_dec_eq(v_str_4333_, v___x_4339_);
if (v___x_4340_ == 0)
{
return v___x_4340_;
}
else
{
return v_suppressElabErrors_4329_;
}
}
}
else
{
lean_object* v___x_4341_; uint8_t v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4342_ = lean_string_dec_eq(v_str_4333_, v___x_4341_);
if (v___x_4342_ == 0)
{
return v___x_4342_;
}
else
{
return v_suppressElabErrors_4329_;
}
}
}
case 1:
{
lean_object* v_pre_4343_; 
v_pre_4343_ = lean_ctor_get(v_pre_4332_, 0);
if (lean_obj_tag(v_pre_4343_) == 0)
{
lean_object* v_str_4344_; lean_object* v_str_4345_; lean_object* v_str_4346_; lean_object* v___x_4347_; uint8_t v___x_4348_; 
v_str_4344_ = lean_ctor_get(v_x_4330_, 1);
v_str_4345_ = lean_ctor_get(v_pre_4331_, 1);
v_str_4346_ = lean_ctor_get(v_pre_4332_, 1);
v___x_4347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4348_ = lean_string_dec_eq(v_str_4346_, v___x_4347_);
if (v___x_4348_ == 0)
{
return v___x_4348_;
}
else
{
lean_object* v___x_4349_; uint8_t v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4350_ = lean_string_dec_eq(v_str_4345_, v___x_4349_);
if (v___x_4350_ == 0)
{
return v___x_4350_;
}
else
{
lean_object* v___x_4351_; uint8_t v___x_4352_; 
v___x_4351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4352_ = lean_string_dec_eq(v_str_4344_, v___x_4351_);
if (v___x_4352_ == 0)
{
return v___x_4352_;
}
else
{
return v_suppressElabErrors_4329_;
}
}
}
}
else
{
uint8_t v___x_4353_; 
v___x_4353_ = 0;
return v___x_4353_;
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
case 0:
{
lean_object* v_str_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v_str_4355_ = lean_ctor_get(v_x_4330_, 1);
v___x_4356_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4357_ = lean_string_dec_eq(v_str_4355_, v___x_4356_);
if (v___x_4357_ == 0)
{
return v___x_4357_;
}
else
{
return v_suppressElabErrors_4329_;
}
}
default: 
{
uint8_t v___x_4358_; 
v___x_4358_ = 0;
return v___x_4358_;
}
}
}
else
{
uint8_t v___x_4359_; 
v___x_4359_ = 0;
return v___x_4359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_4360_, lean_object* v_x_4361_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4362_; uint8_t v_res_4363_; lean_object* v_r_4364_; 
v_suppressElabErrors_boxed_4362_ = lean_unbox(v_suppressElabErrors_4360_);
v_res_4363_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_4362_, v_x_4361_);
lean_dec(v_x_4361_);
v_r_4364_ = lean_box(v_res_4363_);
return v_r_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4366_, lean_object* v_msgData_4367_, uint8_t v_severity_4368_, uint8_t v_isSilent_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_){
_start:
{
lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; lean_object* v___y_4380_; uint8_t v___y_4381_; uint8_t v___y_4382_; lean_object* v_toCold_4383_; lean_object* v___y_4384_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; uint8_t v___y_4416_; uint8_t v___y_4417_; lean_object* v___y_4418_; uint8_t v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4440_; uint8_t v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4444_; uint8_t v___y_4445_; lean_object* v___y_4446_; uint8_t v___y_4450_; uint8_t v___y_4451_; uint8_t v___x_4461_; uint8_t v___y_4463_; uint8_t v___x_4469_; 
v___x_4461_ = 2;
v___x_4469_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4368_, v___x_4461_);
if (v___x_4469_ == 0)
{
v___y_4463_ = v___x_4469_;
goto v___jp_4462_;
}
else
{
uint8_t v___x_4470_; 
lean_inc_ref(v_msgData_4367_);
v___x_4470_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4367_);
if (v___x_4470_ == 0)
{
v___y_4463_ = v___x_4470_;
goto v___jp_4462_;
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_dec_ref(v_msgData_4367_);
v___x_4471_ = lean_box(0);
v___x_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
return v___x_4472_;
}
}
v___jp_4375_:
{
lean_object* v_currNamespace_4385_; lean_object* v_openDecls_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v_env_4391_; lean_object* v_nextMacroScope_4392_; lean_object* v_ngen_4393_; lean_object* v_auxDeclNGen_4394_; lean_object* v_traceState_4395_; lean_object* v_cache_4396_; lean_object* v_recordedDeps_4397_; lean_object* v_messages_4398_; lean_object* v_infoState_4399_; lean_object* v_snapshotTasks_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4411_; 
v_currNamespace_4385_ = lean_ctor_get(v_toCold_4383_, 4);
v_openDecls_4386_ = lean_ctor_get(v_toCold_4383_, 5);
lean_inc(v_openDecls_4386_);
lean_inc(v_currNamespace_4385_);
v___x_4387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4387_, 0, v_currNamespace_4385_);
lean_ctor_set(v___x_4387_, 1, v_openDecls_4386_);
v___x_4388_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4388_, 0, v___x_4387_);
lean_ctor_set(v___x_4388_, 1, v___y_4380_);
lean_inc_ref(v___y_4377_);
lean_inc_ref(v___y_4376_);
v___x_4389_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4389_, 0, v___y_4376_);
lean_ctor_set(v___x_4389_, 1, v___y_4379_);
lean_ctor_set(v___x_4389_, 2, v___y_4378_);
lean_ctor_set(v___x_4389_, 3, v___y_4377_);
lean_ctor_set(v___x_4389_, 4, v___x_4388_);
lean_ctor_set_uint8(v___x_4389_, sizeof(void*)*5, v___y_4381_);
lean_ctor_set_uint8(v___x_4389_, sizeof(void*)*5 + 1, v___y_4382_);
lean_ctor_set_uint8(v___x_4389_, sizeof(void*)*5 + 2, v_isSilent_4369_);
v___x_4390_ = lean_st_ref_take(v___y_4384_);
v_env_4391_ = lean_ctor_get(v___x_4390_, 0);
v_nextMacroScope_4392_ = lean_ctor_get(v___x_4390_, 1);
v_ngen_4393_ = lean_ctor_get(v___x_4390_, 2);
v_auxDeclNGen_4394_ = lean_ctor_get(v___x_4390_, 3);
v_traceState_4395_ = lean_ctor_get(v___x_4390_, 4);
v_cache_4396_ = lean_ctor_get(v___x_4390_, 5);
v_recordedDeps_4397_ = lean_ctor_get(v___x_4390_, 6);
v_messages_4398_ = lean_ctor_get(v___x_4390_, 7);
v_infoState_4399_ = lean_ctor_get(v___x_4390_, 8);
v_snapshotTasks_4400_ = lean_ctor_get(v___x_4390_, 9);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4402_ = v___x_4390_;
v_isShared_4403_ = v_isSharedCheck_4411_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_snapshotTasks_4400_);
lean_inc(v_infoState_4399_);
lean_inc(v_messages_4398_);
lean_inc(v_recordedDeps_4397_);
lean_inc(v_cache_4396_);
lean_inc(v_traceState_4395_);
lean_inc(v_auxDeclNGen_4394_);
lean_inc(v_ngen_4393_);
lean_inc(v_nextMacroScope_4392_);
lean_inc(v_env_4391_);
lean_dec(v___x_4390_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4411_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v___x_4404_ = lean_box(0);
v___x_4405_ = l_Lean_MessageLog_add(v___x_4389_, v_messages_4398_);
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 7, v___x_4405_);
v___x_4407_ = v___x_4402_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_env_4391_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_nextMacroScope_4392_);
lean_ctor_set(v_reuseFailAlloc_4410_, 2, v_ngen_4393_);
lean_ctor_set(v_reuseFailAlloc_4410_, 3, v_auxDeclNGen_4394_);
lean_ctor_set(v_reuseFailAlloc_4410_, 4, v_traceState_4395_);
lean_ctor_set(v_reuseFailAlloc_4410_, 5, v_cache_4396_);
lean_ctor_set(v_reuseFailAlloc_4410_, 6, v_recordedDeps_4397_);
lean_ctor_set(v_reuseFailAlloc_4410_, 7, v___x_4405_);
lean_ctor_set(v_reuseFailAlloc_4410_, 8, v_infoState_4399_);
lean_ctor_set(v_reuseFailAlloc_4410_, 9, v_snapshotTasks_4400_);
v___x_4407_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = lean_st_ref_put(v___y_4384_, v___x_4407_);
v___x_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4404_);
return v___x_4409_;
}
}
}
v___jp_4412_:
{
lean_object* v_fileName_4421_; lean_object* v_fileMap_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4438_; 
v_fileName_4421_ = lean_ctor_get(v___y_4415_, 0);
v_fileMap_4422_ = lean_ctor_get(v___y_4415_, 1);
v___x_4423_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4367_);
v___x_4424_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4423_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_);
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4427_ = v___x_4424_;
v_isShared_4428_ = v_isSharedCheck_4438_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4438_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
lean_inc_ref_n(v_fileMap_4422_, 2);
v___x_4429_ = l_Lean_FileMap_toPosition(v_fileMap_4422_, v___y_4418_);
lean_dec(v___y_4418_);
v___x_4430_ = l_Lean_FileMap_toPosition(v_fileMap_4422_, v___y_4420_);
lean_dec(v___y_4420_);
v___x_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4431_, 0, v___x_4430_);
v___x_4432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4416_ == 0)
{
lean_del_object(v___x_4427_);
lean_dec_ref(v___y_4414_);
v___y_4376_ = v_fileName_4421_;
v___y_4377_ = v___x_4432_;
v___y_4378_ = v___x_4431_;
v___y_4379_ = v___x_4429_;
v___y_4380_ = v_a_4425_;
v___y_4381_ = v___y_4417_;
v___y_4382_ = v___y_4419_;
v_toCold_4383_ = v___y_4413_;
v___y_4384_ = v___y_4373_;
goto v___jp_4375_;
}
else
{
uint8_t v___x_4433_; 
lean_inc(v_a_4425_);
v___x_4433_ = l_Lean_MessageData_hasTag(v___y_4414_, v_a_4425_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4434_; lean_object* v___x_4436_; 
lean_dec_ref_known(v___x_4431_, 1);
lean_dec_ref(v___x_4429_);
lean_dec(v_a_4425_);
v___x_4434_ = lean_box(0);
if (v_isShared_4428_ == 0)
{
lean_ctor_set(v___x_4427_, 0, v___x_4434_);
v___x_4436_ = v___x_4427_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___x_4434_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
else
{
lean_del_object(v___x_4427_);
v___y_4376_ = v_fileName_4421_;
v___y_4377_ = v___x_4432_;
v___y_4378_ = v___x_4431_;
v___y_4379_ = v___x_4429_;
v___y_4380_ = v_a_4425_;
v___y_4381_ = v___y_4417_;
v___y_4382_ = v___y_4419_;
v_toCold_4383_ = v___y_4413_;
v___y_4384_ = v___y_4373_;
goto v___jp_4375_;
}
}
}
}
v___jp_4439_:
{
lean_object* v___x_4447_; 
v___x_4447_ = l_Lean_Syntax_getTailPos_x3f(v___y_4443_, v___y_4444_);
lean_dec(v___y_4443_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_inc(v___y_4446_);
v___y_4413_ = v___y_4440_;
v___y_4414_ = v___y_4442_;
v___y_4415_ = v___y_4440_;
v___y_4416_ = v___y_4441_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4446_;
v___y_4419_ = v___y_4445_;
v___y_4420_ = v___y_4446_;
goto v___jp_4412_;
}
else
{
lean_object* v_val_4448_; 
v_val_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_val_4448_);
lean_dec_ref_known(v___x_4447_, 1);
v___y_4413_ = v___y_4440_;
v___y_4414_ = v___y_4442_;
v___y_4415_ = v___y_4440_;
v___y_4416_ = v___y_4441_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4446_;
v___y_4419_ = v___y_4445_;
v___y_4420_ = v_val_4448_;
goto v___jp_4412_;
}
}
v___jp_4449_:
{
lean_object* v_toCold_4452_; lean_object* v_ref_4453_; uint8_t v_suppressElabErrors_4454_; lean_object* v___x_4455_; lean_object* v___f_4456_; lean_object* v_ref_4457_; lean_object* v___x_4458_; 
v_toCold_4452_ = lean_ctor_get(v___y_4372_, 0);
v_ref_4453_ = lean_ctor_get(v___y_4372_, 2);
v_suppressElabErrors_4454_ = lean_ctor_get_uint8(v___y_4372_, sizeof(void*)*3 + 2);
v___x_4455_ = lean_box(v_suppressElabErrors_4454_);
v___f_4456_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4456_, 0, v___x_4455_);
v_ref_4457_ = l_Lean_replaceRef(v_ref_4366_, v_ref_4453_);
v___x_4458_ = l_Lean_Syntax_getPos_x3f(v_ref_4457_, v___y_4450_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_unsigned_to_nat(0u);
v___y_4440_ = v_toCold_4452_;
v___y_4441_ = v_suppressElabErrors_4454_;
v___y_4442_ = v___f_4456_;
v___y_4443_ = v_ref_4457_;
v___y_4444_ = v___y_4450_;
v___y_4445_ = v___y_4451_;
v___y_4446_ = v___x_4459_;
goto v___jp_4439_;
}
else
{
lean_object* v_val_4460_; 
v_val_4460_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_val_4460_);
lean_dec_ref_known(v___x_4458_, 1);
v___y_4440_ = v_toCold_4452_;
v___y_4441_ = v_suppressElabErrors_4454_;
v___y_4442_ = v___f_4456_;
v___y_4443_ = v_ref_4457_;
v___y_4444_ = v___y_4450_;
v___y_4445_ = v___y_4451_;
v___y_4446_ = v_val_4460_;
goto v___jp_4439_;
}
}
v___jp_4462_:
{
uint8_t v___x_4464_; uint8_t v___x_4465_; 
v___x_4464_ = 1;
v___x_4465_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4368_, v___x_4464_);
if (v___x_4465_ == 0)
{
v___y_4450_ = v___y_4463_;
v___y_4451_ = v_severity_4368_;
goto v___jp_4449_;
}
else
{
lean_object* v___x_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4466_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4372_);
v___x_4467_ = l_Lean_warningAsError;
v___x_4468_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v___x_4466_, v___x_4467_);
lean_dec_ref(v___x_4466_);
if (v___x_4468_ == 0)
{
v___y_4450_ = v___y_4463_;
v___y_4451_ = v_severity_4368_;
goto v___jp_4449_;
}
else
{
v___y_4450_ = v___y_4463_;
v___y_4451_ = v___x_4461_;
goto v___jp_4449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4473_, lean_object* v_msgData_4474_, lean_object* v_severity_4475_, lean_object* v_isSilent_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
uint8_t v_severity_boxed_4482_; uint8_t v_isSilent_boxed_4483_; lean_object* v_res_4484_; 
v_severity_boxed_4482_ = lean_unbox(v_severity_4475_);
v_isSilent_boxed_4483_ = lean_unbox(v_isSilent_4476_);
v_res_4484_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4473_, v_msgData_4474_, v_severity_boxed_4482_, v_isSilent_boxed_4483_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v_ref_4473_);
return v_res_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4485_, uint8_t v_severity_4486_, uint8_t v_isSilent_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_ref_4493_; lean_object* v___x_4494_; 
v_ref_4493_ = lean_ctor_get(v___y_4490_, 2);
v___x_4494_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4493_, v_msgData_4485_, v_severity_4486_, v_isSilent_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4495_, lean_object* v_severity_4496_, lean_object* v_isSilent_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
uint8_t v_severity_boxed_4503_; uint8_t v_isSilent_boxed_4504_; lean_object* v_res_4505_; 
v_severity_boxed_4503_ = lean_unbox(v_severity_4496_);
v_isSilent_boxed_4504_ = lean_unbox(v_isSilent_4497_);
v_res_4505_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4495_, v_severity_boxed_4503_, v_isSilent_boxed_4504_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
uint8_t v___x_4512_; uint8_t v___x_4513_; lean_object* v___x_4514_; 
v___x_4512_ = 0;
v___x_4513_ = 0;
v___x_4514_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4506_, v___x_4512_, v___x_4513_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
return v_res_4521_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4523_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4524_ = l_Lean_stringToMessageData(v___x_4523_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4525_, lean_object* v___altIdx_4526_, lean_object* v_expAltType_4527_, lean_object* v___altFVars_4528_, lean_object* v_alt_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v___x_4535_; 
lean_inc(v___y_4533_);
lean_inc_ref(v___y_4532_);
lean_inc(v___y_4531_);
lean_inc_ref(v___y_4530_);
lean_inc_ref(v_alt_4529_);
v___x_4535_ = lean_infer_type(v_alt_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v___x_4537_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v___x_4537_ = l_Lean_Meta_mkEq(v_expAltType_4527_, v_a_4536_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v___x_4539_ = lean_box(0);
v___x_4540_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4538_, v___x_4539_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4595_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4595_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4595_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4595_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4595_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4545_; lean_object* v___x_4546_; 
v___x_4545_ = l_Lean_Expr_mvarId_x21(v_a_4541_);
v___x_4546_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4545_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4546_) == 0)
{
lean_object* v_a_4547_; lean_object* v___x_4548_; 
v_a_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc_n(v_a_4547_, 2);
lean_dec_ref_known(v___x_4546_, 1);
v___x_4548_ = l_Lean_MVarId_refl(v_a_4547_, v___x_4525_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v___x_4549_; 
lean_dec_ref_known(v___x_4548_, 1);
lean_dec(v_a_4547_);
lean_del_object(v___x_4543_);
v___x_4549_ = l_Lean_Meta_mkEqMPR(v_a_4541_, v_alt_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
return v___x_4549_;
}
else
{
lean_object* v_a_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4586_; 
v_a_4550_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4552_ = v___x_4548_;
v_isShared_4553_ = v_isSharedCheck_4586_;
goto v_resetjp_4551_;
}
else
{
lean_inc(v_a_4550_);
lean_dec(v___x_4548_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4586_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
uint8_t v___x_4554_; 
v___x_4554_ = l_Lean_Exception_isInterrupt(v_a_4550_);
if (v___x_4554_ == 0)
{
uint8_t v___x_4555_; 
lean_inc(v_a_4550_);
v___x_4555_ = l_Lean_Exception_isRuntime(v_a_4550_);
if (v___x_4555_ == 0)
{
lean_object* v___x_4556_; lean_object* v___x_4558_; 
lean_del_object(v___x_4552_);
lean_dec(v_a_4550_);
v___x_4556_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4547_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set_tag(v___x_4543_, 1);
lean_ctor_set(v___x_4543_, 0, v_a_4547_);
v___x_4558_ = v___x_4543_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4579_; 
v_reuseFailAlloc_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4579_, 0, v_a_4547_);
v___x_4558_ = v_reuseFailAlloc_4579_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4559_, 0, v___x_4556_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
v___x_4560_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4559_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v___x_4561_; 
lean_dec_ref_known(v___x_4560_, 1);
v___x_4561_ = l_Lean_MVarId_admit(v_a_4547_, v___x_4525_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v___x_4562_; 
lean_dec_ref_known(v___x_4561_, 1);
v___x_4562_ = l_Lean_Meta_mkEqMPR(v_a_4541_, v_alt_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_);
return v___x_4562_;
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v_a_4541_);
lean_dec_ref(v_alt_4529_);
v_a_4563_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4561_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4561_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec(v_a_4547_);
lean_dec(v_a_4541_);
lean_dec_ref(v_alt_4529_);
v_a_4571_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4560_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4560_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
else
{
lean_object* v___x_4581_; 
lean_dec(v_a_4547_);
lean_del_object(v___x_4543_);
lean_dec(v_a_4541_);
lean_dec_ref(v_alt_4529_);
if (v_isShared_4553_ == 0)
{
v___x_4581_ = v___x_4552_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4550_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
else
{
lean_object* v___x_4584_; 
lean_dec(v_a_4547_);
lean_del_object(v___x_4543_);
lean_dec(v_a_4541_);
lean_dec_ref(v_alt_4529_);
if (v_isShared_4553_ == 0)
{
v___x_4584_ = v___x_4552_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4550_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
else
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
lean_del_object(v___x_4543_);
lean_dec(v_a_4541_);
lean_dec_ref(v_alt_4529_);
v_a_4587_ = lean_ctor_get(v___x_4546_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4589_ = v___x_4546_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4546_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4587_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4529_);
return v___x_4540_;
}
}
else
{
lean_dec_ref(v_alt_4529_);
return v___x_4537_;
}
}
else
{
lean_dec_ref(v_alt_4529_);
lean_dec_ref(v_expAltType_4527_);
return v___x_4535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4596_, lean_object* v___altIdx_4597_, lean_object* v_expAltType_4598_, lean_object* v___altFVars_4599_, lean_object* v_alt_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
uint8_t v___x_32543__boxed_4606_; lean_object* v_res_4607_; 
v___x_32543__boxed_4606_ = lean_unbox(v___x_4596_);
v_res_4607_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32543__boxed_4606_, v___altIdx_4597_, v_expAltType_4598_, v___altFVars_4599_, v_alt_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_);
lean_dec(v___y_4604_);
lean_dec_ref(v___y_4603_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec_ref(v___altFVars_4599_);
lean_dec(v___altIdx_4597_);
return v_res_4607_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4608_, lean_object* v_e_4609_){
_start:
{
uint8_t v___x_4610_; lean_object* v_d_4612_; lean_object* v_b_4613_; 
v___x_4610_ = l_Lean_Expr_hasFVar(v_e_4609_);
if (v___x_4610_ == 0)
{
return v___x_4610_;
}
else
{
switch(lean_obj_tag(v_e_4609_))
{
case 7:
{
lean_object* v_binderType_4616_; lean_object* v_body_4617_; 
v_binderType_4616_ = lean_ctor_get(v_e_4609_, 1);
v_body_4617_ = lean_ctor_get(v_e_4609_, 2);
v_d_4612_ = v_binderType_4616_;
v_b_4613_ = v_body_4617_;
goto v___jp_4611_;
}
case 6:
{
lean_object* v_binderType_4618_; lean_object* v_body_4619_; 
v_binderType_4618_ = lean_ctor_get(v_e_4609_, 1);
v_body_4619_ = lean_ctor_get(v_e_4609_, 2);
v_d_4612_ = v_binderType_4618_;
v_b_4613_ = v_body_4619_;
goto v___jp_4611_;
}
case 10:
{
lean_object* v_expr_4620_; 
v_expr_4620_ = lean_ctor_get(v_e_4609_, 1);
v_e_4609_ = v_expr_4620_;
goto _start;
}
case 8:
{
lean_object* v_type_4622_; lean_object* v_value_4623_; lean_object* v_body_4624_; uint8_t v___x_4625_; 
v_type_4622_ = lean_ctor_get(v_e_4609_, 1);
v_value_4623_ = lean_ctor_get(v_e_4609_, 2);
v_body_4624_ = lean_ctor_get(v_e_4609_, 3);
v___x_4625_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4608_, v_type_4622_);
if (v___x_4625_ == 0)
{
uint8_t v___x_4626_; 
v___x_4626_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4608_, v_value_4623_);
if (v___x_4626_ == 0)
{
v_e_4609_ = v_body_4624_;
goto _start;
}
else
{
return v___x_4610_;
}
}
else
{
return v___x_4610_;
}
}
case 5:
{
lean_object* v_fn_4628_; lean_object* v_arg_4629_; uint8_t v___x_4630_; 
v_fn_4628_ = lean_ctor_get(v_e_4609_, 0);
v_arg_4629_ = lean_ctor_get(v_e_4609_, 1);
v___x_4630_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4608_, v_fn_4628_);
if (v___x_4630_ == 0)
{
v_e_4609_ = v_arg_4629_;
goto _start;
}
else
{
return v___x_4610_;
}
}
case 11:
{
lean_object* v_struct_4632_; 
v_struct_4632_ = lean_ctor_get(v_e_4609_, 2);
v_e_4609_ = v_struct_4632_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; 
v_fvarId_4634_ = lean_ctor_get(v_e_4609_, 0);
v___x_4635_ = l_Lean_Expr_fvarId_x21(v___x_4608_);
v___x_4636_ = l_Lean_instBEqFVarId_beq(v_fvarId_4634_, v___x_4635_);
lean_dec(v___x_4635_);
return v___x_4636_;
}
default: 
{
uint8_t v___x_4637_; 
v___x_4637_ = 0;
return v___x_4637_;
}
}
}
v___jp_4611_:
{
uint8_t v___x_4614_; 
v___x_4614_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4608_, v_d_4612_);
if (v___x_4614_ == 0)
{
v_e_4609_ = v_b_4613_;
goto _start;
}
else
{
return v___x_4610_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4638_, lean_object* v_e_4639_){
_start:
{
uint8_t v_res_4640_; lean_object* v_r_4641_; 
v_res_4640_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4638_, v_e_4639_);
lean_dec_ref(v_e_4639_);
lean_dec_ref(v___x_4638_);
v_r_4641_ = lean_box(v_res_4640_);
return v_r_4641_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; 
v___x_4643_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4644_ = l_Lean_stringToMessageData(v___x_4643_);
return v___x_4644_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4647_ = l_Lean_stringToMessageData(v___x_4646_);
return v___x_4647_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4650_ = l_Lean_stringToMessageData(v___x_4649_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4651_, lean_object* v_termAlt_4652_, lean_object* v_a_4653_, lean_object* v_b_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_){
_start:
{
lean_object* v_array_4660_; lean_object* v_start_4661_; lean_object* v_stop_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4690_; 
v_array_4660_ = lean_ctor_get(v_a_4653_, 0);
v_start_4661_ = lean_ctor_get(v_a_4653_, 1);
v_stop_4662_ = lean_ctor_get(v_a_4653_, 2);
v_isSharedCheck_4690_ = !lean_is_exclusive(v_a_4653_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4664_ = v_a_4653_;
v_isShared_4665_ = v_isSharedCheck_4690_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_stop_4662_);
lean_inc(v_start_4661_);
lean_inc(v_array_4660_);
lean_dec(v_a_4653_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4690_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
uint8_t v___x_4666_; 
v___x_4666_ = lean_nat_dec_lt(v_start_4661_, v_stop_4662_);
if (v___x_4666_ == 0)
{
lean_object* v___x_4667_; 
lean_del_object(v___x_4664_);
lean_dec(v_stop_4662_);
lean_dec(v_start_4661_);
lean_dec_ref(v_array_4660_);
lean_dec_ref(v_termAlt_4652_);
lean_dec_ref(v_a_4651_);
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v_b_4654_);
return v___x_4667_;
}
else
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4668_ = lean_box(0);
v___x_4669_ = lean_unsigned_to_nat(1u);
v___x_4670_ = lean_nat_add(v_start_4661_, v___x_4669_);
lean_inc_ref(v_array_4660_);
if (v_isShared_4665_ == 0)
{
lean_ctor_set(v___x_4664_, 1, v___x_4670_);
v___x_4672_ = v___x_4664_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_array_4660_);
lean_ctor_set(v_reuseFailAlloc_4689_, 1, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4689_, 2, v_stop_4662_);
v___x_4672_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; uint8_t v___x_4674_; 
v___x_4673_ = lean_array_fget(v_array_4660_, v_start_4661_);
lean_dec(v_start_4661_);
lean_dec_ref(v_array_4660_);
v___x_4674_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4673_, v_a_4651_);
if (v___x_4674_ == 0)
{
lean_dec(v___x_4673_);
v_a_4653_ = v___x_4672_;
v_b_4654_ = v___x_4668_;
goto _start;
}
else
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4676_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4651_);
v___x_4677_ = l_Lean_MessageData_ofExpr(v_a_4651_);
v___x_4678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4676_);
lean_ctor_set(v___x_4678_, 1, v___x_4677_);
v___x_4679_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4678_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
lean_inc_ref(v_termAlt_4652_);
v___x_4681_ = l_Lean_MessageData_ofExpr(v_termAlt_4652_);
v___x_4682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4682_, 0, v___x_4680_);
lean_ctor_set(v___x_4682_, 1, v___x_4681_);
v___x_4683_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4684_, 0, v___x_4682_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = l_Lean_MessageData_ofExpr(v___x_4673_);
v___x_4686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4684_);
lean_ctor_set(v___x_4686_, 1, v___x_4685_);
v___x_4687_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4686_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_dec_ref_known(v___x_4687_, 1);
v_a_4653_ = v___x_4672_;
v_b_4654_ = v___x_4668_;
goto _start;
}
else
{
lean_dec_ref(v___x_4672_);
lean_dec_ref(v_termAlt_4652_);
lean_dec_ref(v_a_4651_);
return v___x_4687_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4691_, lean_object* v_termAlt_4692_, lean_object* v_a_4693_, lean_object* v_b_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
lean_object* v_res_4700_; 
v_res_4700_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4691_, v_termAlt_4692_, v_a_4693_, v_b_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
return v_res_4700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4701_, lean_object* v_v_4702_, uint8_t v___x_4703_, uint8_t v___x_4704_, uint8_t v___x_4705_, lean_object* v_xs_4706_, lean_object* v_termAltBody_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4713_ = lean_array_get_size(v_xs_4706_);
v___x_4714_ = lean_nat_sub(v___x_4713_, v_nExtra_4701_);
v___x_4715_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4714_);
lean_inc_ref(v_xs_4706_);
v___x_4716_ = l_Array_toSubarray___redArg(v_xs_4706_, v___x_4715_, v___x_4714_);
v___x_4717_ = l_Array_toSubarray___redArg(v_xs_4706_, v___x_4714_, v___x_4713_);
lean_inc(v___y_4711_);
lean_inc_ref(v___y_4710_);
lean_inc(v___y_4709_);
lean_inc_ref(v___y_4708_);
v___x_4718_ = lean_infer_type(v_termAltBody_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_object* v_a_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
lean_inc_n(v_a_4719_, 2);
lean_dec_ref_known(v___x_4718_, 1);
v___x_4720_ = lean_box(0);
v___x_4721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4719_, v_v_4702_, v___x_4717_, v___x_4720_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
lean_dec_ref_known(v___x_4721_, 1);
v___x_4722_ = l_Subarray_copy___redArg(v___x_4716_);
v___x_4723_ = l_Lean_Meta_mkLambdaFVars(v___x_4722_, v_a_4719_, v___x_4703_, v___x_4704_, v___x_4703_, v___x_4704_, v___x_4705_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
lean_dec_ref(v___x_4722_);
return v___x_4723_;
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
lean_dec(v_a_4719_);
lean_dec_ref(v___x_4716_);
v_a_4724_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4721_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4721_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
else
{
lean_dec_ref(v___x_4717_);
lean_dec_ref(v___x_4716_);
lean_dec(v_v_4702_);
return v___x_4718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4732_, lean_object* v_v_4733_, lean_object* v___x_4734_, lean_object* v___x_4735_, lean_object* v___x_4736_, lean_object* v_xs_4737_, lean_object* v_termAltBody_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_){
_start:
{
uint8_t v___x_32859__boxed_4744_; uint8_t v___x_32860__boxed_4745_; uint8_t v___x_32861__boxed_4746_; lean_object* v_res_4747_; 
v___x_32859__boxed_4744_ = lean_unbox(v___x_4734_);
v___x_32860__boxed_4745_ = lean_unbox(v___x_4735_);
v___x_32861__boxed_4746_ = lean_unbox(v___x_4736_);
v_res_4747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4732_, v_v_4733_, v___x_32859__boxed_4744_, v___x_32860__boxed_4745_, v___x_32861__boxed_4746_, v_xs_4737_, v_termAltBody_4738_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
lean_dec(v___y_4742_);
lean_dec_ref(v___y_4741_);
lean_dec(v___y_4740_);
lean_dec_ref(v___y_4739_);
lean_dec(v_nExtra_4732_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4748_, size_t v_sz_4749_, size_t v_i_4750_, lean_object* v_bs_4751_, lean_object* v___y_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_){
_start:
{
uint8_t v___x_4757_; 
v___x_4757_ = lean_usize_dec_lt(v_i_4750_, v_sz_4749_);
if (v___x_4757_ == 0)
{
lean_object* v___x_4758_; 
lean_dec(v_nExtra_4748_);
v___x_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4758_, 0, v_bs_4751_);
return v___x_4758_;
}
else
{
uint8_t v___x_4759_; uint8_t v___x_4760_; lean_object* v_v_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___f_4765_; lean_object* v___x_4766_; lean_object* v_bs_x27_4767_; lean_object* v___x_4768_; 
v___x_4759_ = 0;
v___x_4760_ = 1;
v_v_4761_ = lean_array_uget(v_bs_4751_, v_i_4750_);
v___x_4762_ = lean_box(v___x_4759_);
v___x_4763_ = lean_box(v___x_4757_);
v___x_4764_ = lean_box(v___x_4760_);
lean_inc(v_v_4761_);
lean_inc(v_nExtra_4748_);
v___f_4765_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4765_, 0, v_nExtra_4748_);
lean_closure_set(v___f_4765_, 1, v_v_4761_);
lean_closure_set(v___f_4765_, 2, v___x_4762_);
lean_closure_set(v___f_4765_, 3, v___x_4763_);
lean_closure_set(v___f_4765_, 4, v___x_4764_);
v___x_4766_ = lean_unsigned_to_nat(0u);
v_bs_x27_4767_ = lean_array_uset(v_bs_4751_, v_i_4750_, v___x_4766_);
v___x_4768_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4761_, v___f_4765_, v___x_4759_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
if (lean_obj_tag(v___x_4768_) == 0)
{
lean_object* v_a_4769_; size_t v___x_4770_; size_t v___x_4771_; lean_object* v___x_4772_; 
v_a_4769_ = lean_ctor_get(v___x_4768_, 0);
lean_inc(v_a_4769_);
lean_dec_ref_known(v___x_4768_, 1);
v___x_4770_ = ((size_t)1ULL);
v___x_4771_ = lean_usize_add(v_i_4750_, v___x_4770_);
v___x_4772_ = lean_array_uset(v_bs_x27_4767_, v_i_4750_, v_a_4769_);
v_i_4750_ = v___x_4771_;
v_bs_4751_ = v___x_4772_;
goto _start;
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_dec_ref(v_bs_x27_4767_);
lean_dec(v_nExtra_4748_);
v_a_4774_ = lean_ctor_get(v___x_4768_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4768_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4768_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4768_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4782_, lean_object* v_sz_4783_, lean_object* v_i_4784_, lean_object* v_bs_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_){
_start:
{
size_t v_sz_boxed_4791_; size_t v_i_boxed_4792_; lean_object* v_res_4793_; 
v_sz_boxed_4791_ = lean_unbox_usize(v_sz_4783_);
lean_dec(v_sz_4783_);
v_i_boxed_4792_ = lean_unbox_usize(v_i_4784_);
lean_dec(v_i_4784_);
v_res_4793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4782_, v_sz_boxed_4791_, v_i_boxed_4792_, v_bs_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_);
lean_dec(v___y_4789_);
lean_dec_ref(v___y_4788_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
return v_res_4793_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; 
v___x_4794_ = lean_box(0);
v___x_4795_ = l_Lean_Expr_sort___override(v___x_4794_);
return v___x_4795_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = lean_box(0);
v___x_4797_ = l_Lean_Level_succ___override(v___x_4796_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4798_, uint8_t v___x_4799_, uint8_t v___x_4800_, lean_object* v_alts_4801_, lean_object* v_toMatcherInfo_4802_, lean_object* v_matcherName_4803_, lean_object* v_params_4804_, lean_object* v_matcherLevels_4805_, lean_object* v_motiveArgs_4806_, lean_object* v_body_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v___x_4813_; 
lean_inc(v_nExtra_4798_);
v___x_4813_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4798_, v_body_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4813_) == 0)
{
lean_object* v_a_4814_; lean_object* v___x_4815_; uint8_t v___x_4816_; lean_object* v___x_4817_; 
v_a_4814_ = lean_ctor_get(v___x_4813_, 0);
lean_inc(v_a_4814_);
lean_dec_ref_known(v___x_4813_, 1);
v___x_4815_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4816_ = 1;
v___x_4817_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4806_, v___x_4815_, v___x_4799_, v___x_4800_, v___x_4799_, v___x_4800_, v___x_4816_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4817_) == 0)
{
lean_object* v_a_4818_; size_t v_sz_4819_; size_t v___x_4820_; lean_object* v___x_4821_; 
v_a_4818_ = lean_ctor_get(v___x_4817_, 0);
lean_inc(v_a_4818_);
lean_dec_ref_known(v___x_4817_, 1);
v_sz_4819_ = lean_array_size(v_alts_4801_);
v___x_4820_ = ((size_t)0ULL);
v___x_4821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4798_, v_sz_4819_, v___x_4820_, v_alts_4801_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v_matcherLevels_4824_; lean_object* v___y_4825_; lean_object* v___y_4826_; lean_object* v_uElimPos_x3f_4831_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4821_, 1);
v_uElimPos_x3f_4831_ = lean_ctor_get(v_toMatcherInfo_4802_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4831_) == 0)
{
v_matcherLevels_4824_ = v_matcherLevels_4805_;
v___y_4825_ = v___y_4810_;
v___y_4826_ = v___y_4811_;
goto v___jp_4823_;
}
else
{
lean_object* v_val_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v_val_4832_ = lean_ctor_get(v_uElimPos_x3f_4831_, 0);
v___x_4833_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4834_ = lean_array_set(v_matcherLevels_4805_, v_val_4832_, v___x_4833_);
v_matcherLevels_4824_ = v___x_4834_;
v___y_4825_ = v___y_4810_;
v___y_4826_ = v___y_4811_;
goto v___jp_4823_;
}
v___jp_4823_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4827_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4828_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4828_, 0, v_toMatcherInfo_4802_);
lean_ctor_set(v___x_4828_, 1, v_matcherName_4803_);
lean_ctor_set(v___x_4828_, 2, v_matcherLevels_4824_);
lean_ctor_set(v___x_4828_, 3, v_params_4804_);
lean_ctor_set(v___x_4828_, 4, v_a_4818_);
lean_ctor_set(v___x_4828_, 5, v_motiveArgs_4806_);
lean_ctor_set(v___x_4828_, 6, v_a_4822_);
lean_ctor_set(v___x_4828_, 7, v___x_4827_);
v___x_4829_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4828_);
v___x_4830_ = l_Lean_mkArrowN(v_a_4814_, v___x_4829_, v___y_4825_, v___y_4826_);
lean_dec(v_a_4814_);
return v___x_4830_;
}
}
else
{
lean_object* v_a_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4842_; 
lean_dec(v_a_4818_);
lean_dec(v_a_4814_);
lean_dec_ref(v_motiveArgs_4806_);
lean_dec_ref(v_matcherLevels_4805_);
lean_dec_ref(v_params_4804_);
lean_dec(v_matcherName_4803_);
lean_dec_ref(v_toMatcherInfo_4802_);
v_a_4835_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4842_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4842_ == 0)
{
v___x_4837_ = v___x_4821_;
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_a_4835_);
lean_dec(v___x_4821_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4842_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4840_; 
if (v_isShared_4838_ == 0)
{
v___x_4840_ = v___x_4837_;
goto v_reusejp_4839_;
}
else
{
lean_object* v_reuseFailAlloc_4841_; 
v_reuseFailAlloc_4841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4841_, 0, v_a_4835_);
v___x_4840_ = v_reuseFailAlloc_4841_;
goto v_reusejp_4839_;
}
v_reusejp_4839_:
{
return v___x_4840_;
}
}
}
}
else
{
lean_dec(v_a_4814_);
lean_dec_ref(v_motiveArgs_4806_);
lean_dec_ref(v_matcherLevels_4805_);
lean_dec_ref(v_params_4804_);
lean_dec(v_matcherName_4803_);
lean_dec_ref(v_toMatcherInfo_4802_);
lean_dec_ref(v_alts_4801_);
lean_dec(v_nExtra_4798_);
return v___x_4817_;
}
}
else
{
lean_object* v_a_4843_; lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4850_; 
lean_dec_ref(v_motiveArgs_4806_);
lean_dec_ref(v_matcherLevels_4805_);
lean_dec_ref(v_params_4804_);
lean_dec(v_matcherName_4803_);
lean_dec_ref(v_toMatcherInfo_4802_);
lean_dec_ref(v_alts_4801_);
lean_dec(v_nExtra_4798_);
v_a_4843_ = lean_ctor_get(v___x_4813_, 0);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4850_ == 0)
{
v___x_4845_ = v___x_4813_;
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
else
{
lean_inc(v_a_4843_);
lean_dec(v___x_4813_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4850_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
lean_object* v___x_4848_; 
if (v_isShared_4846_ == 0)
{
v___x_4848_ = v___x_4845_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_a_4843_);
v___x_4848_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4847_;
}
v_reusejp_4847_:
{
return v___x_4848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4851_, lean_object* v___x_4852_, lean_object* v___x_4853_, lean_object* v_alts_4854_, lean_object* v_toMatcherInfo_4855_, lean_object* v_matcherName_4856_, lean_object* v_params_4857_, lean_object* v_matcherLevels_4858_, lean_object* v_motiveArgs_4859_, lean_object* v_body_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_){
_start:
{
uint8_t v___x_32994__boxed_4866_; uint8_t v___x_32995__boxed_4867_; lean_object* v_res_4868_; 
v___x_32994__boxed_4866_ = lean_unbox(v___x_4852_);
v___x_32995__boxed_4867_ = lean_unbox(v___x_4853_);
v_res_4868_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4851_, v___x_32994__boxed_4866_, v___x_32995__boxed_4867_, v_alts_4854_, v_toMatcherInfo_4855_, v_matcherName_4856_, v_params_4857_, v_matcherLevels_4858_, v_motiveArgs_4859_, v_body_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_);
lean_dec(v___y_4864_);
lean_dec_ref(v___y_4863_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
return v_res_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4869_, lean_object* v_ys_4870_, lean_object* v_args_4871_, lean_object* v___mask_4872_, lean_object* v___bodyType_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v___x_4879_; 
lean_inc(v___y_4877_);
lean_inc_ref(v___y_4876_);
lean_inc(v___y_4875_);
lean_inc_ref(v___y_4874_);
v___x_4879_ = lean_apply_7(v_k_4869_, v_ys_4870_, v_args_4871_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, lean_box(0));
return v___x_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4880_, lean_object* v_ys_4881_, lean_object* v_args_4882_, lean_object* v___mask_4883_, lean_object* v___bodyType_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_){
_start:
{
lean_object* v_res_4890_; 
v_res_4890_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4880_, v_ys_4881_, v_args_4882_, v___mask_4883_, v___bodyType_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
lean_dec(v___y_4888_);
lean_dec_ref(v___y_4887_);
lean_dec(v___y_4886_);
lean_dec_ref(v___y_4885_);
lean_dec_ref(v___bodyType_4884_);
lean_dec_ref(v___mask_4883_);
return v_res_4890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4891_, lean_object* v_altInfo_4892_, lean_object* v_k_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v___f_4899_; lean_object* v___x_4900_; 
v___f_4899_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4899_, 0, v_k_4893_);
v___x_4900_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4891_, v_altInfo_4892_, v___f_4899_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_);
if (lean_obj_tag(v___x_4900_) == 0)
{
lean_object* v_a_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4908_; 
v_a_4901_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4908_ == 0)
{
v___x_4903_ = v___x_4900_;
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_a_4901_);
lean_dec(v___x_4900_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4908_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4906_; 
if (v_isShared_4904_ == 0)
{
v___x_4906_ = v___x_4903_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v_a_4901_);
v___x_4906_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
return v___x_4906_;
}
}
}
else
{
lean_object* v_a_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4916_; 
v_a_4909_ = lean_ctor_get(v___x_4900_, 0);
v_isSharedCheck_4916_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4916_ == 0)
{
v___x_4911_ = v___x_4900_;
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_a_4909_);
lean_dec(v___x_4900_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4916_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
lean_object* v___x_4914_; 
if (v_isShared_4912_ == 0)
{
v___x_4914_ = v___x_4911_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4909_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4917_, lean_object* v_altInfo_4918_, lean_object* v_k_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_){
_start:
{
lean_object* v_res_4925_; 
v_res_4925_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4917_, v_altInfo_4918_, v_k_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
lean_dec(v___y_4923_);
lean_dec_ref(v___y_4922_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
return v_res_4925_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4926_, lean_object* v___x_4927_, lean_object* v___f_4928_, lean_object* v_fst_4929_, lean_object* v___x_4930_, lean_object* v___x_4931_, lean_object* v___x_4932_, lean_object* v___x_4933_, lean_object* v___x_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v___x_4940_; 
v___x_4940_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4926_, v___x_4927_, v___f_4928_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4955_; 
v_a_4941_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4943_ = v___x_4940_;
v_isShared_4944_ = v_isSharedCheck_4955_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4940_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4955_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4953_; 
v___x_4945_ = lean_array_push(v_fst_4929_, v_a_4941_);
v___x_4946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4930_);
lean_ctor_set(v___x_4946_, 1, v___x_4931_);
v___x_4947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4947_, 0, v___x_4932_);
lean_ctor_set(v___x_4947_, 1, v___x_4946_);
v___x_4948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4933_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
v___x_4949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4949_, 0, v___x_4934_);
lean_ctor_set(v___x_4949_, 1, v___x_4948_);
v___x_4950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4945_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
if (v_isShared_4944_ == 0)
{
lean_ctor_set(v___x_4943_, 0, v___x_4951_);
v___x_4953_ = v___x_4943_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4951_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
else
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
lean_dec_ref(v___x_4934_);
lean_dec_ref(v___x_4933_);
lean_dec_ref(v___x_4932_);
lean_dec_ref(v___x_4931_);
lean_dec_ref(v___x_4930_);
lean_dec(v_fst_4929_);
v_a_4956_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4940_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4940_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4964_, lean_object* v___x_4965_, lean_object* v___f_4966_, lean_object* v_fst_4967_, lean_object* v___x_4968_, lean_object* v___x_4969_, lean_object* v___x_4970_, lean_object* v___x_4971_, lean_object* v___x_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
lean_object* v_res_4978_; 
v_res_4978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4964_, v___x_4965_, v___f_4966_, v_fst_4967_, v___x_4968_, v___x_4969_, v___x_4970_, v___x_4971_, v___x_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
return v_res_4978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_4979_, lean_object* v_ys_4980_, lean_object* v_ys2_4981_, lean_object* v_ys3_4982_, lean_object* v_onAlt_4983_, lean_object* v_a_4984_, uint8_t v___x_4985_, uint8_t v_useSplitter_4986_, lean_object* v___x_4987_, lean_object* v_ys4_4988_, lean_object* v_altType_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_, lean_object* v___y_4993_){
_start:
{
lean_object* v_a_4996_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
lean_inc_ref(v_args_4979_);
v___x_5005_ = l_Array_append___redArg(v_args_4979_, v_ys3_4982_);
v___x_5006_ = l_Lean_Meta_instantiateLambda(v___x_4987_, v___x_5005_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
lean_dec_ref(v___x_5005_);
if (lean_obj_tag(v___x_5006_) == 0)
{
lean_object* v_a_5007_; 
v_a_5007_ = lean_ctor_get(v___x_5006_, 0);
lean_inc(v_a_5007_);
lean_dec_ref_known(v___x_5006_, 1);
v_a_4996_ = v_a_5007_;
goto v___jp_4995_;
}
else
{
lean_object* v_a_5008_; uint8_t v___x_5009_; 
v_a_5008_ = lean_ctor_get(v___x_5006_, 0);
v___x_5009_ = l_Lean_Exception_isInterrupt(v_a_5008_);
if (v___x_5009_ == 0)
{
uint8_t v___x_5010_; 
lean_inc(v_a_5008_);
v___x_5010_ = l_Lean_Exception_isRuntime(v_a_5008_);
if (v___x_5010_ == 0)
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
lean_dec_ref_known(v___x_5006_, 1);
v___x_5011_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_5012_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5011_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v_a_5013_; 
v_a_5013_ = lean_ctor_get(v___x_5012_, 0);
lean_inc(v_a_5013_);
lean_dec_ref_known(v___x_5012_, 1);
v_a_4996_ = v_a_5013_;
goto v___jp_4995_;
}
else
{
lean_dec_ref(v_altType_4989_);
lean_dec_ref(v_ys4_4988_);
lean_dec(v_a_4984_);
lean_dec_ref(v_onAlt_4983_);
lean_dec_ref(v_ys3_4982_);
lean_dec_ref(v_ys2_4981_);
lean_dec_ref(v_ys_4980_);
lean_dec_ref(v_args_4979_);
return v___x_5012_;
}
}
else
{
lean_dec_ref(v_altType_4989_);
lean_dec_ref(v_ys4_4988_);
lean_dec(v_a_4984_);
lean_dec_ref(v_onAlt_4983_);
lean_dec_ref(v_ys3_4982_);
lean_dec_ref(v_ys2_4981_);
lean_dec_ref(v_ys_4980_);
lean_dec_ref(v_args_4979_);
return v___x_5006_;
}
}
else
{
lean_dec_ref(v_altType_4989_);
lean_dec_ref(v_ys4_4988_);
lean_dec(v_a_4984_);
lean_dec_ref(v_onAlt_4983_);
lean_dec_ref(v_ys3_4982_);
lean_dec_ref(v_ys2_4981_);
lean_dec_ref(v_ys_4980_);
lean_dec_ref(v_args_4979_);
return v___x_5006_;
}
}
v___jp_4995_:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; 
lean_inc_ref(v_ys4_4988_);
lean_inc_ref(v_ys3_4982_);
lean_inc_ref(v_ys2_4981_);
lean_inc_ref(v_ys_4980_);
v___x_4997_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4997_, 0, v_args_4979_);
lean_ctor_set(v___x_4997_, 1, v_ys_4980_);
lean_ctor_set(v___x_4997_, 2, v_ys2_4981_);
lean_ctor_set(v___x_4997_, 3, v_ys3_4982_);
lean_ctor_set(v___x_4997_, 4, v_ys4_4988_);
lean_inc(v___y_4993_);
lean_inc_ref(v___y_4992_);
lean_inc(v___y_4991_);
lean_inc_ref(v___y_4990_);
v___x_4998_ = lean_apply_9(v_onAlt_4983_, v_a_4984_, v_altType_4989_, v___x_4997_, v_a_4996_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, lean_box(0));
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; uint8_t v___x_5003_; lean_object* v___x_5004_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc(v_a_4999_);
lean_dec_ref_known(v___x_4998_, 1);
v___x_5000_ = l_Array_append___redArg(v_ys_4980_, v_ys2_4981_);
lean_dec_ref(v_ys2_4981_);
v___x_5001_ = l_Array_append___redArg(v___x_5000_, v_ys3_4982_);
lean_dec_ref(v_ys3_4982_);
v___x_5002_ = l_Array_append___redArg(v___x_5001_, v_ys4_4988_);
lean_dec_ref(v_ys4_4988_);
v___x_5003_ = 1;
v___x_5004_ = l_Lean_Meta_mkLambdaFVars(v___x_5002_, v_a_4999_, v___x_4985_, v_useSplitter_4986_, v___x_4985_, v_useSplitter_4986_, v___x_5003_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_);
lean_dec_ref(v___x_5002_);
return v___x_5004_;
}
else
{
lean_dec_ref(v_ys4_4988_);
lean_dec_ref(v_ys3_4982_);
lean_dec_ref(v_ys2_4981_);
lean_dec_ref(v_ys_4980_);
return v___x_4998_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5014_, lean_object* v_ys_5015_, lean_object* v_ys2_5016_, lean_object* v_ys3_5017_, lean_object* v_onAlt_5018_, lean_object* v_a_5019_, lean_object* v___x_5020_, lean_object* v_useSplitter_5021_, lean_object* v___x_5022_, lean_object* v_ys4_5023_, lean_object* v_altType_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
uint8_t v___x_33248__boxed_5030_; uint8_t v_useSplitter_boxed_5031_; lean_object* v_res_5032_; 
v___x_33248__boxed_5030_ = lean_unbox(v___x_5020_);
v_useSplitter_boxed_5031_ = lean_unbox(v_useSplitter_5021_);
v_res_5032_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5014_, v_ys_5015_, v_ys2_5016_, v_ys3_5017_, v_onAlt_5018_, v_a_5019_, v___x_33248__boxed_5030_, v_useSplitter_boxed_5031_, v___x_5022_, v_ys4_5023_, v_altType_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
lean_dec(v___y_5026_);
lean_dec_ref(v___y_5025_);
return v_res_5032_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5033_, lean_object* v_ys_5034_, lean_object* v_ys2_5035_, lean_object* v_onAlt_5036_, lean_object* v_a_5037_, uint8_t v___x_5038_, uint8_t v_useSplitter_5039_, lean_object* v___x_5040_, lean_object* v_extraEqualities_5041_, lean_object* v_ys3_5042_, lean_object* v_altType_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_, lean_object* v___y_5047_){
_start:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___f_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5049_ = lean_box(v___x_5038_);
v___x_5050_ = lean_box(v_useSplitter_5039_);
v___f_5051_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5051_, 0, v_args_5033_);
lean_closure_set(v___f_5051_, 1, v_ys_5034_);
lean_closure_set(v___f_5051_, 2, v_ys2_5035_);
lean_closure_set(v___f_5051_, 3, v_ys3_5042_);
lean_closure_set(v___f_5051_, 4, v_onAlt_5036_);
lean_closure_set(v___f_5051_, 5, v_a_5037_);
lean_closure_set(v___f_5051_, 6, v___x_5049_);
lean_closure_set(v___f_5051_, 7, v___x_5050_);
lean_closure_set(v___f_5051_, 8, v___x_5040_);
v___x_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5052_, 0, v_extraEqualities_5041_);
v___x_5053_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5043_, v___x_5052_, v___f_5051_, v___x_5038_, v___x_5038_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5054_, lean_object* v_ys_5055_, lean_object* v_ys2_5056_, lean_object* v_onAlt_5057_, lean_object* v_a_5058_, lean_object* v___x_5059_, lean_object* v_useSplitter_5060_, lean_object* v___x_5061_, lean_object* v_extraEqualities_5062_, lean_object* v_ys3_5063_, lean_object* v_altType_5064_, lean_object* v___y_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
uint8_t v___x_33310__boxed_5070_; uint8_t v_useSplitter_boxed_5071_; lean_object* v_res_5072_; 
v___x_33310__boxed_5070_ = lean_unbox(v___x_5059_);
v_useSplitter_boxed_5071_ = lean_unbox(v_useSplitter_5060_);
v_res_5072_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5054_, v_ys_5055_, v_ys2_5056_, v_onAlt_5057_, v_a_5058_, v___x_33310__boxed_5070_, v_useSplitter_boxed_5071_, v___x_5061_, v_extraEqualities_5062_, v_ys3_5063_, v_altType_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
lean_dec(v___y_5068_);
lean_dec_ref(v___y_5067_);
lean_dec(v___y_5066_);
lean_dec_ref(v___y_5065_);
return v_res_5072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5073_, lean_object* v_ys_5074_, lean_object* v_onAlt_5075_, lean_object* v_a_5076_, uint8_t v___x_5077_, uint8_t v_useSplitter_5078_, lean_object* v___x_5079_, lean_object* v_extraEqualities_5080_, lean_object* v_numDiscrEqs_5081_, lean_object* v_ys2_5082_, lean_object* v_altType_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___f_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; 
v___x_5089_ = lean_box(v___x_5077_);
v___x_5090_ = lean_box(v_useSplitter_5078_);
v___f_5091_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5091_, 0, v_args_5073_);
lean_closure_set(v___f_5091_, 1, v_ys_5074_);
lean_closure_set(v___f_5091_, 2, v_ys2_5082_);
lean_closure_set(v___f_5091_, 3, v_onAlt_5075_);
lean_closure_set(v___f_5091_, 4, v_a_5076_);
lean_closure_set(v___f_5091_, 5, v___x_5089_);
lean_closure_set(v___f_5091_, 6, v___x_5090_);
lean_closure_set(v___f_5091_, 7, v___x_5079_);
lean_closure_set(v___f_5091_, 8, v_extraEqualities_5080_);
v___x_5092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5092_, 0, v_numDiscrEqs_5081_);
v___x_5093_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5083_, v___x_5092_, v___f_5091_, v___x_5077_, v___x_5077_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_);
return v___x_5093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5094_, lean_object* v_ys_5095_, lean_object* v_onAlt_5096_, lean_object* v_a_5097_, lean_object* v___x_5098_, lean_object* v_useSplitter_5099_, lean_object* v___x_5100_, lean_object* v_extraEqualities_5101_, lean_object* v_numDiscrEqs_5102_, lean_object* v_ys2_5103_, lean_object* v_altType_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_){
_start:
{
uint8_t v___x_33341__boxed_5110_; uint8_t v_useSplitter_boxed_5111_; lean_object* v_res_5112_; 
v___x_33341__boxed_5110_ = lean_unbox(v___x_5098_);
v_useSplitter_boxed_5111_ = lean_unbox(v_useSplitter_5099_);
v_res_5112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5094_, v_ys_5095_, v_onAlt_5096_, v_a_5097_, v___x_33341__boxed_5110_, v_useSplitter_boxed_5111_, v___x_5100_, v_extraEqualities_5101_, v_numDiscrEqs_5102_, v_ys2_5103_, v_altType_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
lean_dec(v___y_5108_);
lean_dec_ref(v___y_5107_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
return v_res_5112_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0(void){
_start:
{
lean_object* v___x_5113_; 
v___x_5113_ = l_instMonadEIO___redArg();
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_){
_start:
{
lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v_toApplicative_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5187_; 
v___x_5124_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5125_ = l_StateRefT_x27_instMonad___redArg(v___x_5124_);
v_toApplicative_5126_ = lean_ctor_get(v___x_5125_, 0);
v_isSharedCheck_5187_ = !lean_is_exclusive(v___x_5125_);
if (v_isSharedCheck_5187_ == 0)
{
lean_object* v_unused_5188_; 
v_unused_5188_ = lean_ctor_get(v___x_5125_, 1);
lean_dec(v_unused_5188_);
v___x_5128_ = v___x_5125_;
v_isShared_5129_ = v_isSharedCheck_5187_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_toApplicative_5126_);
lean_dec(v___x_5125_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5187_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v_toFunctor_5130_; lean_object* v_toSeq_5131_; lean_object* v_toSeqLeft_5132_; lean_object* v_toSeqRight_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5185_; 
v_toFunctor_5130_ = lean_ctor_get(v_toApplicative_5126_, 0);
v_toSeq_5131_ = lean_ctor_get(v_toApplicative_5126_, 2);
v_toSeqLeft_5132_ = lean_ctor_get(v_toApplicative_5126_, 3);
v_toSeqRight_5133_ = lean_ctor_get(v_toApplicative_5126_, 4);
v_isSharedCheck_5185_ = !lean_is_exclusive(v_toApplicative_5126_);
if (v_isSharedCheck_5185_ == 0)
{
lean_object* v_unused_5186_; 
v_unused_5186_ = lean_ctor_get(v_toApplicative_5126_, 1);
lean_dec(v_unused_5186_);
v___x_5135_ = v_toApplicative_5126_;
v_isShared_5136_ = v_isSharedCheck_5185_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_toSeqRight_5133_);
lean_inc(v_toSeqLeft_5132_);
lean_inc(v_toSeq_5131_);
lean_inc(v_toFunctor_5130_);
lean_dec(v_toApplicative_5126_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5185_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___f_5137_; lean_object* v___f_5138_; lean_object* v___f_5139_; lean_object* v___f_5140_; lean_object* v___x_5141_; lean_object* v___f_5142_; lean_object* v___f_5143_; lean_object* v___f_5144_; lean_object* v___x_5146_; 
v___f_5137_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5138_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5130_);
v___f_5139_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5139_, 0, v_toFunctor_5130_);
v___f_5140_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5140_, 0, v_toFunctor_5130_);
v___x_5141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5141_, 0, v___f_5139_);
lean_ctor_set(v___x_5141_, 1, v___f_5140_);
v___f_5142_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5142_, 0, v_toSeqRight_5133_);
v___f_5143_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5143_, 0, v_toSeqLeft_5132_);
v___f_5144_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5144_, 0, v_toSeq_5131_);
if (v_isShared_5136_ == 0)
{
lean_ctor_set(v___x_5135_, 4, v___f_5142_);
lean_ctor_set(v___x_5135_, 3, v___f_5143_);
lean_ctor_set(v___x_5135_, 2, v___f_5144_);
lean_ctor_set(v___x_5135_, 1, v___f_5137_);
lean_ctor_set(v___x_5135_, 0, v___x_5141_);
v___x_5146_ = v___x_5135_;
goto v_reusejp_5145_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___x_5141_);
lean_ctor_set(v_reuseFailAlloc_5184_, 1, v___f_5137_);
lean_ctor_set(v_reuseFailAlloc_5184_, 2, v___f_5144_);
lean_ctor_set(v_reuseFailAlloc_5184_, 3, v___f_5143_);
lean_ctor_set(v_reuseFailAlloc_5184_, 4, v___f_5142_);
v___x_5146_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5145_;
}
v_reusejp_5145_:
{
lean_object* v___x_5148_; 
if (v_isShared_5129_ == 0)
{
lean_ctor_set(v___x_5128_, 1, v___f_5138_);
lean_ctor_set(v___x_5128_, 0, v___x_5146_);
v___x_5148_ = v___x_5128_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5146_);
lean_ctor_set(v_reuseFailAlloc_5183_, 1, v___f_5138_);
v___x_5148_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
lean_object* v___x_5149_; lean_object* v_toApplicative_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5181_; 
v___x_5149_ = l_StateRefT_x27_instMonad___redArg(v___x_5148_);
v_toApplicative_5150_ = lean_ctor_get(v___x_5149_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5149_);
if (v_isSharedCheck_5181_ == 0)
{
lean_object* v_unused_5182_; 
v_unused_5182_ = lean_ctor_get(v___x_5149_, 1);
lean_dec(v_unused_5182_);
v___x_5152_ = v___x_5149_;
v_isShared_5153_ = v_isSharedCheck_5181_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_toApplicative_5150_);
lean_dec(v___x_5149_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5181_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v_toFunctor_5154_; lean_object* v_toSeq_5155_; lean_object* v_toSeqLeft_5156_; lean_object* v_toSeqRight_5157_; lean_object* v___x_5159_; uint8_t v_isShared_5160_; uint8_t v_isSharedCheck_5179_; 
v_toFunctor_5154_ = lean_ctor_get(v_toApplicative_5150_, 0);
v_toSeq_5155_ = lean_ctor_get(v_toApplicative_5150_, 2);
v_toSeqLeft_5156_ = lean_ctor_get(v_toApplicative_5150_, 3);
v_toSeqRight_5157_ = lean_ctor_get(v_toApplicative_5150_, 4);
v_isSharedCheck_5179_ = !lean_is_exclusive(v_toApplicative_5150_);
if (v_isSharedCheck_5179_ == 0)
{
lean_object* v_unused_5180_; 
v_unused_5180_ = lean_ctor_get(v_toApplicative_5150_, 1);
lean_dec(v_unused_5180_);
v___x_5159_ = v_toApplicative_5150_;
v_isShared_5160_ = v_isSharedCheck_5179_;
goto v_resetjp_5158_;
}
else
{
lean_inc(v_toSeqRight_5157_);
lean_inc(v_toSeqLeft_5156_);
lean_inc(v_toSeq_5155_);
lean_inc(v_toFunctor_5154_);
lean_dec(v_toApplicative_5150_);
v___x_5159_ = lean_box(0);
v_isShared_5160_ = v_isSharedCheck_5179_;
goto v_resetjp_5158_;
}
v_resetjp_5158_:
{
lean_object* v___f_5161_; lean_object* v___f_5162_; lean_object* v___f_5163_; lean_object* v___f_5164_; lean_object* v___x_5165_; lean_object* v___f_5166_; lean_object* v___f_5167_; lean_object* v___f_5168_; lean_object* v___x_5170_; 
v___f_5161_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5162_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5154_);
v___f_5163_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5163_, 0, v_toFunctor_5154_);
v___f_5164_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5164_, 0, v_toFunctor_5154_);
v___x_5165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5165_, 0, v___f_5163_);
lean_ctor_set(v___x_5165_, 1, v___f_5164_);
v___f_5166_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5166_, 0, v_toSeqRight_5157_);
v___f_5167_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5167_, 0, v_toSeqLeft_5156_);
v___f_5168_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5168_, 0, v_toSeq_5155_);
if (v_isShared_5160_ == 0)
{
lean_ctor_set(v___x_5159_, 4, v___f_5166_);
lean_ctor_set(v___x_5159_, 3, v___f_5167_);
lean_ctor_set(v___x_5159_, 2, v___f_5168_);
lean_ctor_set(v___x_5159_, 1, v___f_5161_);
lean_ctor_set(v___x_5159_, 0, v___x_5165_);
v___x_5170_ = v___x_5159_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v___x_5165_);
lean_ctor_set(v_reuseFailAlloc_5178_, 1, v___f_5161_);
lean_ctor_set(v_reuseFailAlloc_5178_, 2, v___f_5168_);
lean_ctor_set(v_reuseFailAlloc_5178_, 3, v___f_5167_);
lean_ctor_set(v_reuseFailAlloc_5178_, 4, v___f_5166_);
v___x_5170_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5172_; 
if (v_isShared_5153_ == 0)
{
lean_ctor_set(v___x_5152_, 1, v___f_5162_);
lean_ctor_set(v___x_5152_, 0, v___x_5170_);
v___x_5172_ = v___x_5152_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5170_);
lean_ctor_set(v_reuseFailAlloc_5177_, 1, v___f_5162_);
v___x_5172_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
lean_object* v___x_5173_; lean_object* v___x_5174_; lean_object* v___x_27299__overap_5175_; lean_object* v___x_5176_; 
v___x_5173_ = l_Lean_instInhabitedExpr;
v___x_5174_ = l_instInhabitedOfMonad___redArg(v___x_5172_, v___x_5173_);
v___x_27299__overap_5175_ = lean_panic_fn_borrowed(v___x_5174_, v_msg_5118_);
lean_dec(v___x_5174_);
lean_inc(v___y_5122_);
lean_inc_ref(v___y_5121_);
lean_inc(v___y_5120_);
lean_inc_ref(v___y_5119_);
v___x_5176_ = lean_apply_5(v___x_27299__overap_5175_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, lean_box(0));
return v___x_5176_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_){
_start:
{
lean_object* v_res_5195_; 
v_res_5195_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5189_, v___y_5190_, v___y_5191_, v___y_5192_, v___y_5193_);
lean_dec(v___y_5193_);
lean_dec_ref(v___y_5192_);
lean_dec(v___y_5191_);
lean_dec_ref(v___y_5190_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5196_, lean_object* v_onAlt_5197_, lean_object* v_a_5198_, uint8_t v___x_5199_, uint8_t v_useSplitter_5200_, lean_object* v___x_5201_, lean_object* v_extraEqualities_5202_, lean_object* v_numDiscrEqs_5203_, lean_object* v___x_5204_, uint8_t v_hasUnitThunk_5205_, lean_object* v___x_5206_, lean_object* v_ys_5207_, lean_object* v_args_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_){
_start:
{
lean_object* v_numFields_5214_; lean_object* v_numOverlaps_5215_; uint8_t v_hasUnitThunk_5216_; lean_object* v___x_5217_; uint8_t v___x_5218_; 
v_numFields_5214_ = lean_ctor_get(v___x_5196_, 0);
v_numOverlaps_5215_ = lean_ctor_get(v___x_5196_, 1);
v_hasUnitThunk_5216_ = lean_ctor_get_uint8(v___x_5196_, sizeof(void*)*2);
v___x_5217_ = lean_array_get_size(v_ys_5207_);
v___x_5218_ = lean_nat_dec_eq(v___x_5217_, v_numFields_5214_);
if (v___x_5218_ == 0)
{
lean_object* v___x_5219_; lean_object* v___x_5220_; 
lean_dec_ref(v_args_5208_);
lean_dec_ref(v_ys_5207_);
lean_dec_ref(v___x_5204_);
lean_dec(v_numDiscrEqs_5203_);
lean_dec(v_extraEqualities_5202_);
lean_dec_ref(v___x_5201_);
lean_dec(v_a_5198_);
lean_dec_ref(v_onAlt_5197_);
v___x_5219_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5220_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v___x_5219_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
return v___x_5220_;
}
else
{
lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___f_5223_; lean_object* v_altType_5225_; lean_object* v___y_5226_; lean_object* v___y_5227_; lean_object* v___y_5228_; lean_object* v___y_5229_; lean_object* v___x_5239_; 
v___x_5221_ = lean_box(v___x_5199_);
v___x_5222_ = lean_box(v_useSplitter_5200_);
lean_inc_ref(v_ys_5207_);
v___f_5223_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5223_, 0, v_args_5208_);
lean_closure_set(v___f_5223_, 1, v_ys_5207_);
lean_closure_set(v___f_5223_, 2, v_onAlt_5197_);
lean_closure_set(v___f_5223_, 3, v_a_5198_);
lean_closure_set(v___f_5223_, 4, v___x_5221_);
lean_closure_set(v___f_5223_, 5, v___x_5222_);
lean_closure_set(v___f_5223_, 6, v___x_5201_);
lean_closure_set(v___f_5223_, 7, v_extraEqualities_5202_);
lean_closure_set(v___f_5223_, 8, v_numDiscrEqs_5203_);
v___x_5239_ = l_Lean_Meta_instantiateForall(v___x_5204_, v_ys_5207_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
lean_dec_ref(v_ys_5207_);
if (lean_obj_tag(v___x_5239_) == 0)
{
if (v_hasUnitThunk_5205_ == 0)
{
lean_object* v_a_5240_; 
v_a_5240_ = lean_ctor_get(v___x_5239_, 0);
lean_inc(v_a_5240_);
lean_dec_ref_known(v___x_5239_, 1);
v_altType_5225_ = v_a_5240_;
v___y_5226_ = v___y_5209_;
v___y_5227_ = v___y_5210_;
v___y_5228_ = v___y_5211_;
v___y_5229_ = v___y_5212_;
goto v___jp_5224_;
}
else
{
lean_object* v_a_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; 
v_a_5241_ = lean_ctor_get(v___x_5239_, 0);
lean_inc(v_a_5241_);
lean_dec_ref_known(v___x_5239_, 1);
v___x_5242_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5243_ = lean_mk_empty_array_with_capacity(v___x_5206_);
v___x_5244_ = lean_array_push(v___x_5243_, v___x_5242_);
v___x_5245_ = l_Lean_Meta_instantiateForall(v_a_5241_, v___x_5244_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_);
lean_dec_ref(v___x_5244_);
if (lean_obj_tag(v___x_5245_) == 0)
{
lean_object* v_a_5246_; 
v_a_5246_ = lean_ctor_get(v___x_5245_, 0);
lean_inc(v_a_5246_);
lean_dec_ref_known(v___x_5245_, 1);
v_altType_5225_ = v_a_5246_;
v___y_5226_ = v___y_5209_;
v___y_5227_ = v___y_5210_;
v___y_5228_ = v___y_5211_;
v___y_5229_ = v___y_5212_;
goto v___jp_5224_;
}
else
{
lean_dec_ref(v___f_5223_);
return v___x_5245_;
}
}
}
else
{
lean_dec_ref(v___f_5223_);
return v___x_5239_;
}
v___jp_5224_:
{
lean_object* v___x_5230_; lean_object* v___x_5231_; 
lean_inc(v_numOverlaps_5215_);
v___x_5230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5230_, 0, v_numOverlaps_5215_);
v___x_5231_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5225_, v___x_5230_, v___f_5223_, v___x_5199_, v___x_5199_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
if (lean_obj_tag(v___x_5231_) == 0)
{
if (v_hasUnitThunk_5216_ == 0)
{
return v___x_5231_;
}
else
{
lean_object* v_a_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v_a_5232_ = lean_ctor_get(v___x_5231_, 0);
lean_inc(v_a_5232_);
lean_dec_ref_known(v___x_5231_, 1);
v___x_5233_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5234_ = lean_unsigned_to_nat(2u);
v___x_5235_ = lean_mk_empty_array_with_capacity(v___x_5234_);
lean_dec_ref(v___x_5235_);
v___x_5236_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5237_ = lean_array_push(v___x_5236_, v_a_5232_);
v___x_5238_ = l_Lean_Meta_mkAppM(v___x_5233_, v___x_5237_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
return v___x_5238_;
}
}
else
{
return v___x_5231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5247_ = _args[0];
lean_object* v_onAlt_5248_ = _args[1];
lean_object* v_a_5249_ = _args[2];
lean_object* v___x_5250_ = _args[3];
lean_object* v_useSplitter_5251_ = _args[4];
lean_object* v___x_5252_ = _args[5];
lean_object* v_extraEqualities_5253_ = _args[6];
lean_object* v_numDiscrEqs_5254_ = _args[7];
lean_object* v___x_5255_ = _args[8];
lean_object* v_hasUnitThunk_5256_ = _args[9];
lean_object* v___x_5257_ = _args[10];
lean_object* v_ys_5258_ = _args[11];
lean_object* v_args_5259_ = _args[12];
lean_object* v___y_5260_ = _args[13];
lean_object* v___y_5261_ = _args[14];
lean_object* v___y_5262_ = _args[15];
lean_object* v___y_5263_ = _args[16];
lean_object* v___y_5264_ = _args[17];
_start:
{
uint8_t v___x_33543__boxed_5265_; uint8_t v_useSplitter_boxed_5266_; uint8_t v_hasUnitThunk_boxed_5267_; lean_object* v_res_5268_; 
v___x_33543__boxed_5265_ = lean_unbox(v___x_5250_);
v_useSplitter_boxed_5266_ = lean_unbox(v_useSplitter_5251_);
v_hasUnitThunk_boxed_5267_ = lean_unbox(v_hasUnitThunk_5256_);
v_res_5268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5247_, v_onAlt_5248_, v_a_5249_, v___x_33543__boxed_5265_, v_useSplitter_boxed_5266_, v___x_5252_, v_extraEqualities_5253_, v_numDiscrEqs_5254_, v___x_5255_, v_hasUnitThunk_boxed_5267_, v___x_5257_, v_ys_5258_, v_args_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
lean_dec(v___x_5257_);
lean_dec_ref(v___x_5247_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_){
_start:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v_toApplicative_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5338_; 
v___x_5275_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5276_ = l_StateRefT_x27_instMonad___redArg(v___x_5275_);
v_toApplicative_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5338_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5338_ == 0)
{
lean_object* v_unused_5339_; 
v_unused_5339_ = lean_ctor_get(v___x_5276_, 1);
lean_dec(v_unused_5339_);
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5338_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_toApplicative_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5338_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_toFunctor_5281_; lean_object* v_toSeq_5282_; lean_object* v_toSeqLeft_5283_; lean_object* v_toSeqRight_5284_; lean_object* v___x_5286_; uint8_t v_isShared_5287_; uint8_t v_isSharedCheck_5336_; 
v_toFunctor_5281_ = lean_ctor_get(v_toApplicative_5277_, 0);
v_toSeq_5282_ = lean_ctor_get(v_toApplicative_5277_, 2);
v_toSeqLeft_5283_ = lean_ctor_get(v_toApplicative_5277_, 3);
v_toSeqRight_5284_ = lean_ctor_get(v_toApplicative_5277_, 4);
v_isSharedCheck_5336_ = !lean_is_exclusive(v_toApplicative_5277_);
if (v_isSharedCheck_5336_ == 0)
{
lean_object* v_unused_5337_; 
v_unused_5337_ = lean_ctor_get(v_toApplicative_5277_, 1);
lean_dec(v_unused_5337_);
v___x_5286_ = v_toApplicative_5277_;
v_isShared_5287_ = v_isSharedCheck_5336_;
goto v_resetjp_5285_;
}
else
{
lean_inc(v_toSeqRight_5284_);
lean_inc(v_toSeqLeft_5283_);
lean_inc(v_toSeq_5282_);
lean_inc(v_toFunctor_5281_);
lean_dec(v_toApplicative_5277_);
v___x_5286_ = lean_box(0);
v_isShared_5287_ = v_isSharedCheck_5336_;
goto v_resetjp_5285_;
}
v_resetjp_5285_:
{
lean_object* v___f_5288_; lean_object* v___f_5289_; lean_object* v___f_5290_; lean_object* v___f_5291_; lean_object* v___x_5292_; lean_object* v___f_5293_; lean_object* v___f_5294_; lean_object* v___f_5295_; lean_object* v___x_5297_; 
v___f_5288_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5289_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5281_);
v___f_5290_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5290_, 0, v_toFunctor_5281_);
v___f_5291_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5291_, 0, v_toFunctor_5281_);
v___x_5292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5292_, 0, v___f_5290_);
lean_ctor_set(v___x_5292_, 1, v___f_5291_);
v___f_5293_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5293_, 0, v_toSeqRight_5284_);
v___f_5294_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5294_, 0, v_toSeqLeft_5283_);
v___f_5295_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5295_, 0, v_toSeq_5282_);
if (v_isShared_5287_ == 0)
{
lean_ctor_set(v___x_5286_, 4, v___f_5293_);
lean_ctor_set(v___x_5286_, 3, v___f_5294_);
lean_ctor_set(v___x_5286_, 2, v___f_5295_);
lean_ctor_set(v___x_5286_, 1, v___f_5288_);
lean_ctor_set(v___x_5286_, 0, v___x_5292_);
v___x_5297_ = v___x_5286_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v___x_5292_);
lean_ctor_set(v_reuseFailAlloc_5335_, 1, v___f_5288_);
lean_ctor_set(v_reuseFailAlloc_5335_, 2, v___f_5295_);
lean_ctor_set(v_reuseFailAlloc_5335_, 3, v___f_5294_);
lean_ctor_set(v_reuseFailAlloc_5335_, 4, v___f_5293_);
v___x_5297_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
lean_object* v___x_5299_; 
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 1, v___f_5289_);
lean_ctor_set(v___x_5279_, 0, v___x_5297_);
v___x_5299_ = v___x_5279_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5334_; 
v_reuseFailAlloc_5334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5334_, 0, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5334_, 1, v___f_5289_);
v___x_5299_ = v_reuseFailAlloc_5334_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v_toApplicative_5301_; lean_object* v___x_5303_; uint8_t v_isShared_5304_; uint8_t v_isSharedCheck_5332_; 
v___x_5300_ = l_StateRefT_x27_instMonad___redArg(v___x_5299_);
v_toApplicative_5301_ = lean_ctor_get(v___x_5300_, 0);
v_isSharedCheck_5332_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5332_ == 0)
{
lean_object* v_unused_5333_; 
v_unused_5333_ = lean_ctor_get(v___x_5300_, 1);
lean_dec(v_unused_5333_);
v___x_5303_ = v___x_5300_;
v_isShared_5304_ = v_isSharedCheck_5332_;
goto v_resetjp_5302_;
}
else
{
lean_inc(v_toApplicative_5301_);
lean_dec(v___x_5300_);
v___x_5303_ = lean_box(0);
v_isShared_5304_ = v_isSharedCheck_5332_;
goto v_resetjp_5302_;
}
v_resetjp_5302_:
{
lean_object* v_toFunctor_5305_; lean_object* v_toSeq_5306_; lean_object* v_toSeqLeft_5307_; lean_object* v_toSeqRight_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5330_; 
v_toFunctor_5305_ = lean_ctor_get(v_toApplicative_5301_, 0);
v_toSeq_5306_ = lean_ctor_get(v_toApplicative_5301_, 2);
v_toSeqLeft_5307_ = lean_ctor_get(v_toApplicative_5301_, 3);
v_toSeqRight_5308_ = lean_ctor_get(v_toApplicative_5301_, 4);
v_isSharedCheck_5330_ = !lean_is_exclusive(v_toApplicative_5301_);
if (v_isSharedCheck_5330_ == 0)
{
lean_object* v_unused_5331_; 
v_unused_5331_ = lean_ctor_get(v_toApplicative_5301_, 1);
lean_dec(v_unused_5331_);
v___x_5310_ = v_toApplicative_5301_;
v_isShared_5311_ = v_isSharedCheck_5330_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_toSeqRight_5308_);
lean_inc(v_toSeqLeft_5307_);
lean_inc(v_toSeq_5306_);
lean_inc(v_toFunctor_5305_);
lean_dec(v_toApplicative_5301_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5330_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___f_5312_; lean_object* v___f_5313_; lean_object* v___f_5314_; lean_object* v___f_5315_; lean_object* v___x_5316_; lean_object* v___f_5317_; lean_object* v___f_5318_; lean_object* v___f_5319_; lean_object* v___x_5321_; 
v___f_5312_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5313_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5305_);
v___f_5314_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5314_, 0, v_toFunctor_5305_);
v___f_5315_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5315_, 0, v_toFunctor_5305_);
v___x_5316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5316_, 0, v___f_5314_);
lean_ctor_set(v___x_5316_, 1, v___f_5315_);
v___f_5317_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5317_, 0, v_toSeqRight_5308_);
v___f_5318_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5318_, 0, v_toSeqLeft_5307_);
v___f_5319_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5319_, 0, v_toSeq_5306_);
if (v_isShared_5311_ == 0)
{
lean_ctor_set(v___x_5310_, 4, v___f_5317_);
lean_ctor_set(v___x_5310_, 3, v___f_5318_);
lean_ctor_set(v___x_5310_, 2, v___f_5319_);
lean_ctor_set(v___x_5310_, 1, v___f_5312_);
lean_ctor_set(v___x_5310_, 0, v___x_5316_);
v___x_5321_ = v___x_5310_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5329_; 
v_reuseFailAlloc_5329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5329_, 0, v___x_5316_);
lean_ctor_set(v_reuseFailAlloc_5329_, 1, v___f_5312_);
lean_ctor_set(v_reuseFailAlloc_5329_, 2, v___f_5319_);
lean_ctor_set(v_reuseFailAlloc_5329_, 3, v___f_5318_);
lean_ctor_set(v_reuseFailAlloc_5329_, 4, v___f_5317_);
v___x_5321_ = v_reuseFailAlloc_5329_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
lean_object* v___x_5323_; 
if (v_isShared_5304_ == 0)
{
lean_ctor_set(v___x_5303_, 1, v___f_5313_);
lean_ctor_set(v___x_5303_, 0, v___x_5321_);
v___x_5323_ = v___x_5303_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5328_, 1, v___f_5313_);
v___x_5323_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
lean_object* v___x_5324_; lean_object* v___x_5325_; lean_object* v___x_27319__overap_5326_; lean_object* v___x_5327_; 
v___x_5324_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
v___x_5325_ = l_instInhabitedOfMonad___redArg(v___x_5323_, v___x_5324_);
v___x_27319__overap_5326_ = lean_panic_fn_borrowed(v___x_5325_, v_msg_5269_);
lean_dec(v___x_5325_);
lean_inc(v___y_5273_);
lean_inc_ref(v___y_5272_);
lean_inc(v___y_5271_);
lean_inc_ref(v___y_5270_);
v___x_5327_ = lean_apply_5(v___x_27319__overap_5326_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, lean_box(0));
return v___x_5327_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_){
_start:
{
lean_object* v_res_5346_; 
v_res_5346_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
return v_res_5346_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_){
_start:
{
lean_object* v___x_5353_; 
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5347_);
return v___x_5353_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v_res_5360_; 
v_res_5360_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5354_, v___y_5355_, v___y_5356_, v___y_5357_, v___y_5358_);
lean_dec(v___y_5358_);
lean_dec_ref(v___y_5357_);
lean_dec(v___y_5356_);
lean_dec_ref(v___y_5355_);
return v_res_5360_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5361_, lean_object* v_onAlt_5362_, uint8_t v_useSplitter_5363_, lean_object* v_extraEqualities_5364_, lean_object* v_numDiscrEqs_5365_, lean_object* v_a_5366_, lean_object* v_b_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_){
_start:
{
lean_object* v___y_5374_; uint8_t v___x_5397_; 
v___x_5397_ = lean_nat_dec_lt(v_a_5366_, v_upperBound_5361_);
if (v___x_5397_ == 0)
{
lean_object* v___x_5398_; 
lean_dec(v_a_5366_);
lean_dec(v_numDiscrEqs_5365_);
lean_dec(v_extraEqualities_5364_);
lean_dec_ref(v_onAlt_5362_);
v___x_5398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5398_, 0, v_b_5367_);
return v___x_5398_;
}
else
{
lean_object* v_snd_5399_; lean_object* v_snd_5400_; lean_object* v_snd_5401_; lean_object* v_snd_5402_; lean_object* v_snd_5403_; lean_object* v_fst_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5610_; 
v_snd_5399_ = lean_ctor_get(v_b_5367_, 1);
lean_inc(v_snd_5399_);
v_snd_5400_ = lean_ctor_get(v_snd_5399_, 1);
lean_inc(v_snd_5400_);
v_snd_5401_ = lean_ctor_get(v_snd_5400_, 1);
lean_inc(v_snd_5401_);
v_snd_5402_ = lean_ctor_get(v_snd_5401_, 1);
lean_inc(v_snd_5402_);
v_snd_5403_ = lean_ctor_get(v_snd_5402_, 1);
lean_inc(v_snd_5403_);
v_fst_5404_ = lean_ctor_get(v_b_5367_, 0);
v_isSharedCheck_5610_ = !lean_is_exclusive(v_b_5367_);
if (v_isSharedCheck_5610_ == 0)
{
lean_object* v_unused_5611_; 
v_unused_5611_ = lean_ctor_get(v_b_5367_, 1);
lean_dec(v_unused_5611_);
v___x_5406_ = v_b_5367_;
v_isShared_5407_ = v_isSharedCheck_5610_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_fst_5404_);
lean_dec(v_b_5367_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5610_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v_fst_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5608_; 
v_fst_5408_ = lean_ctor_get(v_snd_5399_, 0);
v_isSharedCheck_5608_ = !lean_is_exclusive(v_snd_5399_);
if (v_isSharedCheck_5608_ == 0)
{
lean_object* v_unused_5609_; 
v_unused_5609_ = lean_ctor_get(v_snd_5399_, 1);
lean_dec(v_unused_5609_);
v___x_5410_ = v_snd_5399_;
v_isShared_5411_ = v_isSharedCheck_5608_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_fst_5408_);
lean_dec(v_snd_5399_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5608_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v_fst_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5606_; 
v_fst_5412_ = lean_ctor_get(v_snd_5400_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v_snd_5400_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; 
v_unused_5607_ = lean_ctor_get(v_snd_5400_, 1);
lean_dec(v_unused_5607_);
v___x_5414_ = v_snd_5400_;
v_isShared_5415_ = v_isSharedCheck_5606_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_fst_5412_);
lean_dec(v_snd_5400_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5606_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v_fst_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5604_; 
v_fst_5416_ = lean_ctor_get(v_snd_5401_, 0);
v_isSharedCheck_5604_ = !lean_is_exclusive(v_snd_5401_);
if (v_isSharedCheck_5604_ == 0)
{
lean_object* v_unused_5605_; 
v_unused_5605_ = lean_ctor_get(v_snd_5401_, 1);
lean_dec(v_unused_5605_);
v___x_5418_ = v_snd_5401_;
v_isShared_5419_ = v_isSharedCheck_5604_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_fst_5416_);
lean_dec(v_snd_5401_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5604_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v_fst_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5602_; 
v_fst_5420_ = lean_ctor_get(v_snd_5402_, 0);
v_isSharedCheck_5602_ = !lean_is_exclusive(v_snd_5402_);
if (v_isSharedCheck_5602_ == 0)
{
lean_object* v_unused_5603_; 
v_unused_5603_ = lean_ctor_get(v_snd_5402_, 1);
lean_dec(v_unused_5603_);
v___x_5422_ = v_snd_5402_;
v_isShared_5423_ = v_isSharedCheck_5602_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_fst_5420_);
lean_dec(v_snd_5402_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5602_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v_array_5424_; lean_object* v_start_5425_; lean_object* v_stop_5426_; uint8_t v___x_5427_; 
v_array_5424_ = lean_ctor_get(v_snd_5403_, 0);
v_start_5425_ = lean_ctor_get(v_snd_5403_, 1);
v_stop_5426_ = lean_ctor_get(v_snd_5403_, 2);
v___x_5427_ = lean_nat_dec_lt(v_start_5425_, v_stop_5426_);
if (v___x_5427_ == 0)
{
lean_object* v___x_5429_; 
if (v_isShared_5423_ == 0)
{
v___x_5429_ = v___x_5422_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_fst_5420_);
lean_ctor_set(v_reuseFailAlloc_5444_, 1, v_snd_5403_);
v___x_5429_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
lean_object* v___x_5431_; 
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 1, v___x_5429_);
v___x_5431_ = v___x_5418_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_fst_5416_);
lean_ctor_set(v_reuseFailAlloc_5443_, 1, v___x_5429_);
v___x_5431_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
lean_object* v___x_5433_; 
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 1, v___x_5431_);
v___x_5433_ = v___x_5414_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_fst_5412_);
lean_ctor_set(v_reuseFailAlloc_5442_, 1, v___x_5431_);
v___x_5433_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
lean_object* v___x_5435_; 
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5433_);
v___x_5435_ = v___x_5410_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5441_; 
v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5441_, 0, v_fst_5408_);
lean_ctor_set(v_reuseFailAlloc_5441_, 1, v___x_5433_);
v___x_5435_ = v_reuseFailAlloc_5441_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
lean_object* v___x_5437_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5435_);
v___x_5437_ = v___x_5406_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5440_; 
v_reuseFailAlloc_5440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5440_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5440_, 1, v___x_5435_);
v___x_5437_ = v_reuseFailAlloc_5440_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
lean_object* v___x_5438_; lean_object* v___f_5439_; 
v___x_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5438_, 0, v___x_5437_);
v___f_5439_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5439_, 0, v___x_5438_);
v___y_5374_ = v___f_5439_;
goto v___jp_5373_;
}
}
}
}
}
}
else
{
lean_object* v___x_5446_; uint8_t v_isShared_5447_; uint8_t v_isSharedCheck_5598_; 
lean_inc(v_stop_5426_);
lean_inc(v_start_5425_);
lean_inc_ref(v_array_5424_);
v_isSharedCheck_5598_ = !lean_is_exclusive(v_snd_5403_);
if (v_isSharedCheck_5598_ == 0)
{
lean_object* v_unused_5599_; lean_object* v_unused_5600_; lean_object* v_unused_5601_; 
v_unused_5599_ = lean_ctor_get(v_snd_5403_, 2);
lean_dec(v_unused_5599_);
v_unused_5600_ = lean_ctor_get(v_snd_5403_, 1);
lean_dec(v_unused_5600_);
v_unused_5601_ = lean_ctor_get(v_snd_5403_, 0);
lean_dec(v_unused_5601_);
v___x_5446_ = v_snd_5403_;
v_isShared_5447_ = v_isSharedCheck_5598_;
goto v_resetjp_5445_;
}
else
{
lean_dec(v_snd_5403_);
v___x_5446_ = lean_box(0);
v_isShared_5447_ = v_isSharedCheck_5598_;
goto v_resetjp_5445_;
}
v_resetjp_5445_:
{
lean_object* v_array_5448_; lean_object* v_start_5449_; lean_object* v_stop_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5455_; 
v_array_5448_ = lean_ctor_get(v_fst_5420_, 0);
v_start_5449_ = lean_ctor_get(v_fst_5420_, 1);
v_stop_5450_ = lean_ctor_get(v_fst_5420_, 2);
v___x_5451_ = lean_array_fget(v_array_5424_, v_start_5425_);
v___x_5452_ = lean_unsigned_to_nat(1u);
v___x_5453_ = lean_nat_add(v_start_5425_, v___x_5452_);
lean_dec(v_start_5425_);
if (v_isShared_5447_ == 0)
{
lean_ctor_set(v___x_5446_, 1, v___x_5453_);
v___x_5455_ = v___x_5446_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_array_5424_);
lean_ctor_set(v_reuseFailAlloc_5597_, 1, v___x_5453_);
lean_ctor_set(v_reuseFailAlloc_5597_, 2, v_stop_5426_);
v___x_5455_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
uint8_t v___x_5456_; 
v___x_5456_ = lean_nat_dec_lt(v_start_5449_, v_stop_5450_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5458_; 
lean_dec(v___x_5451_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 1, v___x_5455_);
v___x_5458_ = v___x_5422_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_fst_5420_);
lean_ctor_set(v_reuseFailAlloc_5473_, 1, v___x_5455_);
v___x_5458_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
lean_object* v___x_5460_; 
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 1, v___x_5458_);
v___x_5460_ = v___x_5418_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_fst_5416_);
lean_ctor_set(v_reuseFailAlloc_5472_, 1, v___x_5458_);
v___x_5460_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
lean_object* v___x_5462_; 
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 1, v___x_5460_);
v___x_5462_ = v___x_5414_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_fst_5412_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v___x_5460_);
v___x_5462_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
lean_object* v___x_5464_; 
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5462_);
v___x_5464_ = v___x_5410_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5470_; 
v_reuseFailAlloc_5470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5470_, 0, v_fst_5408_);
lean_ctor_set(v_reuseFailAlloc_5470_, 1, v___x_5462_);
v___x_5464_ = v_reuseFailAlloc_5470_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
lean_object* v___x_5466_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5464_);
v___x_5466_ = v___x_5406_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5469_, 1, v___x_5464_);
v___x_5466_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
lean_object* v___x_5467_; lean_object* v___f_5468_; 
v___x_5467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5467_, 0, v___x_5466_);
v___f_5468_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5468_, 0, v___x_5467_);
v___y_5374_ = v___f_5468_;
goto v___jp_5373_;
}
}
}
}
}
}
else
{
lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5593_; 
lean_inc(v_stop_5450_);
lean_inc(v_start_5449_);
lean_inc_ref(v_array_5448_);
v_isSharedCheck_5593_ = !lean_is_exclusive(v_fst_5420_);
if (v_isSharedCheck_5593_ == 0)
{
lean_object* v_unused_5594_; lean_object* v_unused_5595_; lean_object* v_unused_5596_; 
v_unused_5594_ = lean_ctor_get(v_fst_5420_, 2);
lean_dec(v_unused_5594_);
v_unused_5595_ = lean_ctor_get(v_fst_5420_, 1);
lean_dec(v_unused_5595_);
v_unused_5596_ = lean_ctor_get(v_fst_5420_, 0);
lean_dec(v_unused_5596_);
v___x_5475_ = v_fst_5420_;
v_isShared_5476_ = v_isSharedCheck_5593_;
goto v_resetjp_5474_;
}
else
{
lean_dec(v_fst_5420_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5593_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v_array_5477_; lean_object* v_start_5478_; lean_object* v_stop_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5483_; 
v_array_5477_ = lean_ctor_get(v_fst_5416_, 0);
v_start_5478_ = lean_ctor_get(v_fst_5416_, 1);
v_stop_5479_ = lean_ctor_get(v_fst_5416_, 2);
v___x_5480_ = lean_array_fget(v_array_5448_, v_start_5449_);
v___x_5481_ = lean_nat_add(v_start_5449_, v___x_5452_);
lean_dec(v_start_5449_);
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 1, v___x_5481_);
v___x_5483_ = v___x_5475_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_array_5448_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v___x_5481_);
lean_ctor_set(v_reuseFailAlloc_5592_, 2, v_stop_5450_);
v___x_5483_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
uint8_t v___x_5484_; 
v___x_5484_ = lean_nat_dec_lt(v_start_5478_, v_stop_5479_);
if (v___x_5484_ == 0)
{
lean_object* v___x_5486_; 
lean_dec(v___x_5480_);
lean_dec(v___x_5451_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 1, v___x_5455_);
lean_ctor_set(v___x_5422_, 0, v___x_5483_);
v___x_5486_ = v___x_5422_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v___x_5483_);
lean_ctor_set(v_reuseFailAlloc_5501_, 1, v___x_5455_);
v___x_5486_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5488_; 
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 1, v___x_5486_);
v___x_5488_ = v___x_5418_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_fst_5416_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5490_; 
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 1, v___x_5488_);
v___x_5490_ = v___x_5414_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5499_; 
v_reuseFailAlloc_5499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_fst_5412_);
lean_ctor_set(v_reuseFailAlloc_5499_, 1, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5499_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5492_; 
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5490_);
v___x_5492_ = v___x_5410_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5498_; 
v_reuseFailAlloc_5498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5498_, 0, v_fst_5408_);
lean_ctor_set(v_reuseFailAlloc_5498_, 1, v___x_5490_);
v___x_5492_ = v_reuseFailAlloc_5498_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5494_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5492_);
v___x_5494_ = v___x_5406_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5497_; 
v_reuseFailAlloc_5497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5497_, 1, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5497_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
lean_object* v___x_5495_; lean_object* v___f_5496_; 
v___x_5495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5495_, 0, v___x_5494_);
v___f_5496_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5496_, 0, v___x_5495_);
v___y_5374_ = v___f_5496_;
goto v___jp_5373_;
}
}
}
}
}
}
else
{
lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5588_; 
lean_inc(v_stop_5479_);
lean_inc(v_start_5478_);
lean_inc_ref(v_array_5477_);
v_isSharedCheck_5588_ = !lean_is_exclusive(v_fst_5416_);
if (v_isSharedCheck_5588_ == 0)
{
lean_object* v_unused_5589_; lean_object* v_unused_5590_; lean_object* v_unused_5591_; 
v_unused_5589_ = lean_ctor_get(v_fst_5416_, 2);
lean_dec(v_unused_5589_);
v_unused_5590_ = lean_ctor_get(v_fst_5416_, 1);
lean_dec(v_unused_5590_);
v_unused_5591_ = lean_ctor_get(v_fst_5416_, 0);
lean_dec(v_unused_5591_);
v___x_5503_ = v_fst_5416_;
v_isShared_5504_ = v_isSharedCheck_5588_;
goto v_resetjp_5502_;
}
else
{
lean_dec(v_fst_5416_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5588_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v_array_5505_; lean_object* v_start_5506_; lean_object* v_stop_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; lean_object* v___x_5511_; 
v_array_5505_ = lean_ctor_get(v_fst_5412_, 0);
v_start_5506_ = lean_ctor_get(v_fst_5412_, 1);
v_stop_5507_ = lean_ctor_get(v_fst_5412_, 2);
v___x_5508_ = lean_array_fget(v_array_5477_, v_start_5478_);
v___x_5509_ = lean_nat_add(v_start_5478_, v___x_5452_);
lean_dec(v_start_5478_);
if (v_isShared_5504_ == 0)
{
lean_ctor_set(v___x_5503_, 1, v___x_5509_);
v___x_5511_ = v___x_5503_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_array_5477_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v___x_5509_);
lean_ctor_set(v_reuseFailAlloc_5587_, 2, v_stop_5479_);
v___x_5511_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
uint8_t v___x_5512_; 
v___x_5512_ = lean_nat_dec_lt(v_start_5506_, v_stop_5507_);
if (v___x_5512_ == 0)
{
lean_object* v___x_5514_; 
lean_dec(v___x_5508_);
lean_dec(v___x_5480_);
lean_dec(v___x_5451_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 1, v___x_5455_);
lean_ctor_set(v___x_5422_, 0, v___x_5483_);
v___x_5514_ = v___x_5422_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5483_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v___x_5455_);
v___x_5514_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5516_; 
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 1, v___x_5514_);
lean_ctor_set(v___x_5418_, 0, v___x_5511_);
v___x_5516_ = v___x_5418_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5511_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v___x_5514_);
v___x_5516_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5518_; 
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 1, v___x_5516_);
v___x_5518_ = v___x_5414_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_fst_5412_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v___x_5516_);
v___x_5518_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
lean_object* v___x_5520_; 
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5518_);
v___x_5520_ = v___x_5410_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v_fst_5408_);
lean_ctor_set(v_reuseFailAlloc_5526_, 1, v___x_5518_);
v___x_5520_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
lean_object* v___x_5522_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5520_);
v___x_5522_ = v___x_5406_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5525_, 1, v___x_5520_);
v___x_5522_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
lean_object* v___x_5523_; lean_object* v___f_5524_; 
v___x_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5523_, 0, v___x_5522_);
v___f_5524_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5524_, 0, v___x_5523_);
v___y_5374_ = v___f_5524_;
goto v___jp_5373_;
}
}
}
}
}
}
else
{
lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5583_; 
lean_inc(v_stop_5507_);
lean_inc(v_start_5506_);
lean_inc_ref(v_array_5505_);
v_isSharedCheck_5583_ = !lean_is_exclusive(v_fst_5412_);
if (v_isSharedCheck_5583_ == 0)
{
lean_object* v_unused_5584_; lean_object* v_unused_5585_; lean_object* v_unused_5586_; 
v_unused_5584_ = lean_ctor_get(v_fst_5412_, 2);
lean_dec(v_unused_5584_);
v_unused_5585_ = lean_ctor_get(v_fst_5412_, 1);
lean_dec(v_unused_5585_);
v_unused_5586_ = lean_ctor_get(v_fst_5412_, 0);
lean_dec(v_unused_5586_);
v___x_5531_ = v_fst_5412_;
v_isShared_5532_ = v_isSharedCheck_5583_;
goto v_resetjp_5530_;
}
else
{
lean_dec(v_fst_5412_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5583_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v_array_5533_; lean_object* v_start_5534_; lean_object* v_stop_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5539_; 
v_array_5533_ = lean_ctor_get(v_fst_5408_, 0);
v_start_5534_ = lean_ctor_get(v_fst_5408_, 1);
v_stop_5535_ = lean_ctor_get(v_fst_5408_, 2);
v___x_5536_ = lean_array_fget(v_array_5505_, v_start_5506_);
v___x_5537_ = lean_nat_add(v_start_5506_, v___x_5452_);
lean_dec(v_start_5506_);
if (v_isShared_5532_ == 0)
{
lean_ctor_set(v___x_5531_, 1, v___x_5537_);
v___x_5539_ = v___x_5531_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_array_5505_);
lean_ctor_set(v_reuseFailAlloc_5582_, 1, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5582_, 2, v_stop_5507_);
v___x_5539_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
uint8_t v___x_5540_; 
v___x_5540_ = lean_nat_dec_lt(v_start_5534_, v_stop_5535_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5542_; 
lean_dec(v___x_5536_);
lean_dec(v___x_5508_);
lean_dec(v___x_5480_);
lean_dec(v___x_5451_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 1, v___x_5455_);
lean_ctor_set(v___x_5422_, 0, v___x_5483_);
v___x_5542_ = v___x_5422_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v___x_5483_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5455_);
v___x_5542_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5544_; 
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 1, v___x_5542_);
lean_ctor_set(v___x_5418_, 0, v___x_5511_);
v___x_5544_ = v___x_5418_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5556_; 
v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5511_);
lean_ctor_set(v_reuseFailAlloc_5556_, 1, v___x_5542_);
v___x_5544_ = v_reuseFailAlloc_5556_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
lean_object* v___x_5546_; 
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 1, v___x_5544_);
lean_ctor_set(v___x_5414_, 0, v___x_5539_);
v___x_5546_ = v___x_5414_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5555_, 1, v___x_5544_);
v___x_5546_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5548_; 
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5546_);
v___x_5548_ = v___x_5410_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_fst_5408_);
lean_ctor_set(v_reuseFailAlloc_5554_, 1, v___x_5546_);
v___x_5548_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
lean_object* v___x_5550_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5548_);
v___x_5550_ = v___x_5406_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5553_, 1, v___x_5548_);
v___x_5550_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
lean_object* v___x_5551_; lean_object* v___f_5552_; 
v___x_5551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5551_, 0, v___x_5550_);
v___f_5552_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5552_, 0, v___x_5551_);
v___y_5374_ = v___f_5552_;
goto v___jp_5373_;
}
}
}
}
}
}
else
{
lean_object* v___x_5559_; uint8_t v_isShared_5560_; uint8_t v_isSharedCheck_5578_; 
lean_inc(v_stop_5535_);
lean_inc(v_start_5534_);
lean_inc_ref(v_array_5533_);
lean_del_object(v___x_5422_);
lean_del_object(v___x_5418_);
lean_del_object(v___x_5414_);
lean_del_object(v___x_5410_);
lean_del_object(v___x_5406_);
v_isSharedCheck_5578_ = !lean_is_exclusive(v_fst_5408_);
if (v_isSharedCheck_5578_ == 0)
{
lean_object* v_unused_5579_; lean_object* v_unused_5580_; lean_object* v_unused_5581_; 
v_unused_5579_ = lean_ctor_get(v_fst_5408_, 2);
lean_dec(v_unused_5579_);
v_unused_5580_ = lean_ctor_get(v_fst_5408_, 1);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_fst_5408_, 0);
lean_dec(v_unused_5581_);
v___x_5559_ = v_fst_5408_;
v_isShared_5560_ = v_isSharedCheck_5578_;
goto v_resetjp_5558_;
}
else
{
lean_dec(v_fst_5408_);
v___x_5559_ = lean_box(0);
v_isShared_5560_ = v_isSharedCheck_5578_;
goto v_resetjp_5558_;
}
v_resetjp_5558_:
{
lean_object* v_numOverlaps_5561_; uint8_t v_hasUnitThunk_5562_; lean_object* v___x_5563_; uint8_t v___x_5564_; 
v_numOverlaps_5561_ = lean_ctor_get(v___x_5536_, 1);
v_hasUnitThunk_5562_ = lean_ctor_get_uint8(v___x_5536_, sizeof(void*)*2);
v___x_5563_ = lean_unsigned_to_nat(0u);
v___x_5564_ = lean_nat_dec_eq(v_numOverlaps_5561_, v___x_5563_);
if (v___x_5564_ == 0)
{
lean_object* v___x_5565_; lean_object* v___x_5566_; 
lean_del_object(v___x_5559_);
lean_dec_ref(v___x_5539_);
lean_dec(v___x_5536_);
lean_dec(v_stop_5535_);
lean_dec(v_start_5534_);
lean_dec_ref(v_array_5533_);
lean_dec_ref(v___x_5511_);
lean_dec(v___x_5508_);
lean_dec_ref(v___x_5483_);
lean_dec(v___x_5480_);
lean_dec_ref(v___x_5455_);
lean_dec(v___x_5451_);
lean_dec(v_fst_5404_);
v___x_5565_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_5566_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed), 6, 1);
lean_closure_set(v___x_5566_, 0, v___x_5565_);
v___y_5374_ = v___x_5566_;
goto v___jp_5373_;
}
else
{
uint8_t v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v___x_5570_; lean_object* v___x_5571_; lean_object* v___f_5572_; lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5567_ = 0;
v___x_5568_ = lean_array_fget_borrowed(v_array_5533_, v_start_5534_);
v___x_5569_ = lean_box(v___x_5567_);
v___x_5570_ = lean_box(v_useSplitter_5363_);
v___x_5571_ = lean_box(v_hasUnitThunk_5562_);
lean_inc(v_numDiscrEqs_5365_);
lean_inc(v_extraEqualities_5364_);
lean_inc(v___x_5568_);
lean_inc(v_a_5366_);
lean_inc_ref(v_onAlt_5362_);
v___f_5572_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5572_, 0, v___x_5508_);
lean_closure_set(v___f_5572_, 1, v_onAlt_5362_);
lean_closure_set(v___f_5572_, 2, v_a_5366_);
lean_closure_set(v___f_5572_, 3, v___x_5569_);
lean_closure_set(v___f_5572_, 4, v___x_5570_);
lean_closure_set(v___f_5572_, 5, v___x_5568_);
lean_closure_set(v___f_5572_, 6, v_extraEqualities_5364_);
lean_closure_set(v___f_5572_, 7, v_numDiscrEqs_5365_);
lean_closure_set(v___f_5572_, 8, v___x_5451_);
lean_closure_set(v___f_5572_, 9, v___x_5571_);
lean_closure_set(v___f_5572_, 10, v___x_5452_);
v___x_5573_ = lean_nat_add(v_start_5534_, v___x_5452_);
lean_dec(v_start_5534_);
if (v_isShared_5560_ == 0)
{
lean_ctor_set(v___x_5559_, 1, v___x_5573_);
v___x_5575_ = v___x_5559_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_array_5533_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5577_, 2, v_stop_5535_);
v___x_5575_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
lean_object* v___f_5576_; 
v___f_5576_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5576_, 0, v___x_5480_);
lean_closure_set(v___f_5576_, 1, v___x_5536_);
lean_closure_set(v___f_5576_, 2, v___f_5572_);
lean_closure_set(v___f_5576_, 3, v_fst_5404_);
lean_closure_set(v___f_5576_, 4, v___x_5483_);
lean_closure_set(v___f_5576_, 5, v___x_5455_);
lean_closure_set(v___f_5576_, 6, v___x_5511_);
lean_closure_set(v___f_5576_, 7, v___x_5539_);
lean_closure_set(v___f_5576_, 8, v___x_5575_);
v___y_5374_ = v___f_5576_;
goto v___jp_5373_;
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
v___jp_5373_:
{
lean_object* v___x_5375_; 
lean_inc(v___y_5371_);
lean_inc_ref(v___y_5370_);
lean_inc(v___y_5369_);
lean_inc_ref(v___y_5368_);
v___x_5375_ = lean_apply_5(v___y_5374_, v___y_5368_, v___y_5369_, v___y_5370_, v___y_5371_, lean_box(0));
if (lean_obj_tag(v___x_5375_) == 0)
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5388_; 
v_a_5376_ = lean_ctor_get(v___x_5375_, 0);
v_isSharedCheck_5388_ = !lean_is_exclusive(v___x_5375_);
if (v_isSharedCheck_5388_ == 0)
{
v___x_5378_ = v___x_5375_;
v_isShared_5379_ = v_isSharedCheck_5388_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5375_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5388_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
if (lean_obj_tag(v_a_5376_) == 0)
{
lean_object* v_a_5380_; lean_object* v___x_5382_; 
lean_dec(v_a_5366_);
lean_dec(v_numDiscrEqs_5365_);
lean_dec(v_extraEqualities_5364_);
lean_dec_ref(v_onAlt_5362_);
v_a_5380_ = lean_ctor_get(v_a_5376_, 0);
lean_inc(v_a_5380_);
lean_dec_ref_known(v_a_5376_, 1);
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 0, v_a_5380_);
v___x_5382_ = v___x_5378_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5380_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
else
{
lean_object* v_a_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; 
lean_del_object(v___x_5378_);
v_a_5384_ = lean_ctor_get(v_a_5376_, 0);
lean_inc(v_a_5384_);
lean_dec_ref_known(v_a_5376_, 1);
v___x_5385_ = lean_unsigned_to_nat(1u);
v___x_5386_ = lean_nat_add(v_a_5366_, v___x_5385_);
lean_dec(v_a_5366_);
v_a_5366_ = v___x_5386_;
v_b_5367_ = v_a_5384_;
goto _start;
}
}
}
else
{
lean_object* v_a_5389_; lean_object* v___x_5391_; uint8_t v_isShared_5392_; uint8_t v_isSharedCheck_5396_; 
lean_dec(v_a_5366_);
lean_dec(v_numDiscrEqs_5365_);
lean_dec(v_extraEqualities_5364_);
lean_dec_ref(v_onAlt_5362_);
v_a_5389_ = lean_ctor_get(v___x_5375_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5375_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5391_ = v___x_5375_;
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
else
{
lean_inc(v_a_5389_);
lean_dec(v___x_5375_);
v___x_5391_ = lean_box(0);
v_isShared_5392_ = v_isSharedCheck_5396_;
goto v_resetjp_5390_;
}
v_resetjp_5390_:
{
lean_object* v___x_5394_; 
if (v_isShared_5392_ == 0)
{
v___x_5394_ = v___x_5391_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5395_; 
v_reuseFailAlloc_5395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5395_, 0, v_a_5389_);
v___x_5394_ = v_reuseFailAlloc_5395_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
return v___x_5394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5612_, lean_object* v_onAlt_5613_, lean_object* v_useSplitter_5614_, lean_object* v_extraEqualities_5615_, lean_object* v_numDiscrEqs_5616_, lean_object* v_a_5617_, lean_object* v_b_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_){
_start:
{
uint8_t v_useSplitter_boxed_5624_; lean_object* v_res_5625_; 
v_useSplitter_boxed_5624_ = lean_unbox(v_useSplitter_5614_);
v_res_5625_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5612_, v_onAlt_5613_, v_useSplitter_boxed_5624_, v_extraEqualities_5615_, v_numDiscrEqs_5616_, v_a_5617_, v_b_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_);
lean_dec(v___y_5622_);
lean_dec_ref(v___y_5621_);
lean_dec(v___y_5620_);
lean_dec_ref(v___y_5619_);
lean_dec(v_upperBound_5612_);
return v_res_5625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5626_, lean_object* v_as_5627_, size_t v_sz_5628_, size_t v_i_5629_, lean_object* v_b_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_){
_start:
{
lean_object* v_a_5637_; uint8_t v___x_5641_; 
v___x_5641_ = lean_usize_dec_lt(v_i_5629_, v_sz_5628_);
if (v___x_5641_ == 0)
{
lean_object* v___x_5642_; 
v___x_5642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5642_, 0, v_b_5630_);
return v___x_5642_;
}
else
{
lean_object* v_snd_5643_; lean_object* v_snd_5644_; lean_object* v_snd_5645_; lean_object* v_snd_5646_; lean_object* v_fst_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5793_; 
v_snd_5643_ = lean_ctor_get(v_b_5630_, 1);
lean_inc(v_snd_5643_);
v_snd_5644_ = lean_ctor_get(v_snd_5643_, 1);
lean_inc(v_snd_5644_);
v_snd_5645_ = lean_ctor_get(v_snd_5644_, 1);
lean_inc(v_snd_5645_);
v_snd_5646_ = lean_ctor_get(v_snd_5645_, 1);
lean_inc(v_snd_5646_);
v_fst_5647_ = lean_ctor_get(v_b_5630_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v_b_5630_);
if (v_isSharedCheck_5793_ == 0)
{
lean_object* v_unused_5794_; 
v_unused_5794_ = lean_ctor_get(v_b_5630_, 1);
lean_dec(v_unused_5794_);
v___x_5649_ = v_b_5630_;
v_isShared_5650_ = v_isSharedCheck_5793_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_fst_5647_);
lean_dec(v_b_5630_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5793_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v_fst_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5791_; 
v_fst_5651_ = lean_ctor_get(v_snd_5643_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v_snd_5643_);
if (v_isSharedCheck_5791_ == 0)
{
lean_object* v_unused_5792_; 
v_unused_5792_ = lean_ctor_get(v_snd_5643_, 1);
lean_dec(v_unused_5792_);
v___x_5653_ = v_snd_5643_;
v_isShared_5654_ = v_isSharedCheck_5791_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_fst_5651_);
lean_dec(v_snd_5643_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5791_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v_fst_5655_; lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5789_; 
v_fst_5655_ = lean_ctor_get(v_snd_5644_, 0);
v_isSharedCheck_5789_ = !lean_is_exclusive(v_snd_5644_);
if (v_isSharedCheck_5789_ == 0)
{
lean_object* v_unused_5790_; 
v_unused_5790_ = lean_ctor_get(v_snd_5644_, 1);
lean_dec(v_unused_5790_);
v___x_5657_ = v_snd_5644_;
v_isShared_5658_ = v_isSharedCheck_5789_;
goto v_resetjp_5656_;
}
else
{
lean_inc(v_fst_5655_);
lean_dec(v_snd_5644_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5789_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v_fst_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5787_; 
v_fst_5659_ = lean_ctor_get(v_snd_5645_, 0);
v_isSharedCheck_5787_ = !lean_is_exclusive(v_snd_5645_);
if (v_isSharedCheck_5787_ == 0)
{
lean_object* v_unused_5788_; 
v_unused_5788_ = lean_ctor_get(v_snd_5645_, 1);
lean_dec(v_unused_5788_);
v___x_5661_ = v_snd_5645_;
v_isShared_5662_ = v_isSharedCheck_5787_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_fst_5659_);
lean_dec(v_snd_5645_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5787_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v_array_5663_; lean_object* v_start_5664_; lean_object* v_stop_5665_; uint8_t v___x_5666_; 
v_array_5663_ = lean_ctor_get(v_snd_5646_, 0);
v_start_5664_ = lean_ctor_get(v_snd_5646_, 1);
v_stop_5665_ = lean_ctor_get(v_snd_5646_, 2);
v___x_5666_ = lean_nat_dec_lt(v_start_5664_, v_stop_5665_);
if (v___x_5666_ == 0)
{
lean_object* v___x_5668_; 
if (v_isShared_5662_ == 0)
{
v___x_5668_ = v___x_5661_;
goto v_reusejp_5667_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_fst_5659_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v_snd_5646_);
v___x_5668_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5667_;
}
v_reusejp_5667_:
{
lean_object* v___x_5670_; 
if (v_isShared_5658_ == 0)
{
lean_ctor_set(v___x_5657_, 1, v___x_5668_);
v___x_5670_ = v___x_5657_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_fst_5655_);
lean_ctor_set(v_reuseFailAlloc_5678_, 1, v___x_5668_);
v___x_5670_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
lean_object* v___x_5672_; 
if (v_isShared_5654_ == 0)
{
lean_ctor_set(v___x_5653_, 1, v___x_5670_);
v___x_5672_ = v___x_5653_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_fst_5651_);
lean_ctor_set(v_reuseFailAlloc_5677_, 1, v___x_5670_);
v___x_5672_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5674_; 
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 1, v___x_5672_);
v___x_5674_ = v___x_5649_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_fst_5647_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v___x_5672_);
v___x_5674_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
lean_object* v___x_5675_; 
v___x_5675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5674_);
return v___x_5675_;
}
}
}
}
}
else
{
lean_object* v___x_5681_; uint8_t v_isShared_5682_; uint8_t v_isSharedCheck_5783_; 
lean_inc(v_stop_5665_);
lean_inc(v_start_5664_);
lean_inc_ref(v_array_5663_);
v_isSharedCheck_5783_ = !lean_is_exclusive(v_snd_5646_);
if (v_isSharedCheck_5783_ == 0)
{
lean_object* v_unused_5784_; lean_object* v_unused_5785_; lean_object* v_unused_5786_; 
v_unused_5784_ = lean_ctor_get(v_snd_5646_, 2);
lean_dec(v_unused_5784_);
v_unused_5785_ = lean_ctor_get(v_snd_5646_, 1);
lean_dec(v_unused_5785_);
v_unused_5786_ = lean_ctor_get(v_snd_5646_, 0);
lean_dec(v_unused_5786_);
v___x_5681_ = v_snd_5646_;
v_isShared_5682_ = v_isSharedCheck_5783_;
goto v_resetjp_5680_;
}
else
{
lean_dec(v_snd_5646_);
v___x_5681_ = lean_box(0);
v_isShared_5682_ = v_isSharedCheck_5783_;
goto v_resetjp_5680_;
}
v_resetjp_5680_:
{
lean_object* v_array_5683_; lean_object* v_start_5684_; lean_object* v_stop_5685_; lean_object* v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5690_; 
v_array_5683_ = lean_ctor_get(v_fst_5659_, 0);
v_start_5684_ = lean_ctor_get(v_fst_5659_, 1);
v_stop_5685_ = lean_ctor_get(v_fst_5659_, 2);
v___x_5686_ = lean_array_fget(v_array_5663_, v_start_5664_);
v___x_5687_ = lean_unsigned_to_nat(1u);
v___x_5688_ = lean_nat_add(v_start_5664_, v___x_5687_);
lean_dec(v_start_5664_);
if (v_isShared_5682_ == 0)
{
lean_ctor_set(v___x_5681_, 1, v___x_5688_);
v___x_5690_ = v___x_5681_;
goto v_reusejp_5689_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_array_5663_);
lean_ctor_set(v_reuseFailAlloc_5782_, 1, v___x_5688_);
lean_ctor_set(v_reuseFailAlloc_5782_, 2, v_stop_5665_);
v___x_5690_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5689_;
}
v_reusejp_5689_:
{
uint8_t v___x_5691_; 
v___x_5691_ = lean_nat_dec_lt(v_start_5684_, v_stop_5685_);
if (v___x_5691_ == 0)
{
lean_object* v___x_5693_; 
lean_dec(v___x_5686_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 1, v___x_5690_);
v___x_5693_ = v___x_5661_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v_fst_5659_);
lean_ctor_set(v_reuseFailAlloc_5704_, 1, v___x_5690_);
v___x_5693_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
lean_object* v___x_5695_; 
if (v_isShared_5658_ == 0)
{
lean_ctor_set(v___x_5657_, 1, v___x_5693_);
v___x_5695_ = v___x_5657_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v_fst_5655_);
lean_ctor_set(v_reuseFailAlloc_5703_, 1, v___x_5693_);
v___x_5695_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5654_ == 0)
{
lean_ctor_set(v___x_5653_, 1, v___x_5695_);
v___x_5697_ = v___x_5653_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v_fst_5651_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
lean_object* v___x_5699_; 
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 1, v___x_5697_);
v___x_5699_ = v___x_5649_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v_fst_5647_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v___x_5697_);
v___x_5699_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
lean_object* v___x_5700_; 
v___x_5700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5700_, 0, v___x_5699_);
return v___x_5700_;
}
}
}
}
}
else
{
lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5778_; 
lean_inc(v_stop_5685_);
lean_inc(v_start_5684_);
lean_inc_ref(v_array_5683_);
v_isSharedCheck_5778_ = !lean_is_exclusive(v_fst_5659_);
if (v_isSharedCheck_5778_ == 0)
{
lean_object* v_unused_5779_; lean_object* v_unused_5780_; lean_object* v_unused_5781_; 
v_unused_5779_ = lean_ctor_get(v_fst_5659_, 2);
lean_dec(v_unused_5779_);
v_unused_5780_ = lean_ctor_get(v_fst_5659_, 1);
lean_dec(v_unused_5780_);
v_unused_5781_ = lean_ctor_get(v_fst_5659_, 0);
lean_dec(v_unused_5781_);
v___x_5706_ = v_fst_5659_;
v_isShared_5707_ = v_isSharedCheck_5778_;
goto v_resetjp_5705_;
}
else
{
lean_dec(v_fst_5659_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5778_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5711_; 
v___x_5708_ = lean_array_fget(v_array_5683_, v_start_5684_);
v___x_5709_ = lean_nat_add(v_start_5684_, v___x_5687_);
lean_dec(v_start_5684_);
if (v_isShared_5707_ == 0)
{
lean_ctor_set(v___x_5706_, 1, v___x_5709_);
v___x_5711_ = v___x_5706_;
goto v_reusejp_5710_;
}
else
{
lean_object* v_reuseFailAlloc_5777_; 
v_reuseFailAlloc_5777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5777_, 0, v_array_5683_);
lean_ctor_set(v_reuseFailAlloc_5777_, 1, v___x_5709_);
lean_ctor_set(v_reuseFailAlloc_5777_, 2, v_stop_5685_);
v___x_5711_ = v_reuseFailAlloc_5777_;
goto v_reusejp_5710_;
}
v_reusejp_5710_:
{
if (v_addEqualities_5626_ == 0)
{
lean_dec(v___x_5708_);
goto v___jp_5712_;
}
else
{
if (lean_obj_tag(v___x_5686_) == 0)
{
lean_object* v_a_5728_; lean_object* v___x_5729_; 
lean_del_object(v___x_5661_);
lean_del_object(v___x_5657_);
lean_del_object(v___x_5653_);
lean_del_object(v___x_5649_);
v_a_5728_ = lean_array_uget_borrowed(v_as_5627_, v_i_5629_);
lean_inc(v_a_5728_);
v___x_5729_ = l_Lean_Meta_isProof(v_a_5728_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_);
if (lean_obj_tag(v___x_5729_) == 0)
{
lean_object* v_a_5730_; uint8_t v___x_5731_; 
v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
lean_inc(v_a_5730_);
lean_dec_ref_known(v___x_5729_, 1);
v___x_5731_ = lean_unbox(v_a_5730_);
lean_dec(v_a_5730_);
if (v___x_5731_ == 0)
{
lean_object* v___x_5732_; 
lean_inc(v_a_5728_);
v___x_5732_ = l_Lean_Meta_mkEqHEq(v___x_5708_, v_a_5728_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; lean_object* v___x_5734_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
lean_inc_n(v_a_5733_, 2);
lean_dec_ref_known(v___x_5732_, 1);
v___x_5734_ = l_Lean_mkArrow(v_a_5733_, v_fst_5647_, v___y_5633_, v___y_5634_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; uint8_t v___x_5736_; lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_a_5735_);
lean_dec_ref_known(v___x_5734_, 1);
v___x_5736_ = l_Lean_Expr_isHEq(v_a_5733_);
lean_dec(v_a_5733_);
v___x_5737_ = lean_box(v___x_5736_);
v___x_5738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5738_, 0, v___x_5737_);
v___x_5739_ = lean_array_push(v_fst_5651_, v___x_5738_);
v___x_5740_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_5741_ = lean_array_push(v_fst_5655_, v___x_5740_);
v___x_5742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5711_);
lean_ctor_set(v___x_5742_, 1, v___x_5690_);
v___x_5743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5741_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5744_, 0, v___x_5739_);
lean_ctor_set(v___x_5744_, 1, v___x_5743_);
v___x_5745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5745_, 0, v_a_5735_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v_a_5637_ = v___x_5745_;
goto v___jp_5636_;
}
else
{
lean_object* v_a_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5753_; 
lean_dec(v_a_5733_);
lean_dec_ref(v___x_5711_);
lean_dec_ref(v___x_5690_);
lean_dec(v_fst_5655_);
lean_dec(v_fst_5651_);
v_a_5746_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5753_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5753_ == 0)
{
v___x_5748_ = v___x_5734_;
v_isShared_5749_ = v_isSharedCheck_5753_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_a_5746_);
lean_dec(v___x_5734_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5753_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5751_; 
if (v_isShared_5749_ == 0)
{
v___x_5751_ = v___x_5748_;
goto v_reusejp_5750_;
}
else
{
lean_object* v_reuseFailAlloc_5752_; 
v_reuseFailAlloc_5752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5752_, 0, v_a_5746_);
v___x_5751_ = v_reuseFailAlloc_5752_;
goto v_reusejp_5750_;
}
v_reusejp_5750_:
{
return v___x_5751_;
}
}
}
}
else
{
lean_object* v_a_5754_; lean_object* v___x_5756_; uint8_t v_isShared_5757_; uint8_t v_isSharedCheck_5761_; 
lean_dec_ref(v___x_5711_);
lean_dec_ref(v___x_5690_);
lean_dec(v_fst_5655_);
lean_dec(v_fst_5651_);
lean_dec(v_fst_5647_);
v_a_5754_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5761_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5761_ == 0)
{
v___x_5756_ = v___x_5732_;
v_isShared_5757_ = v_isSharedCheck_5761_;
goto v_resetjp_5755_;
}
else
{
lean_inc(v_a_5754_);
lean_dec(v___x_5732_);
v___x_5756_ = lean_box(0);
v_isShared_5757_ = v_isSharedCheck_5761_;
goto v_resetjp_5755_;
}
v_resetjp_5755_:
{
lean_object* v___x_5759_; 
if (v_isShared_5757_ == 0)
{
v___x_5759_ = v___x_5756_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v_a_5754_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
}
else
{
lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; 
lean_dec(v___x_5708_);
v___x_5762_ = lean_box(0);
v___x_5763_ = lean_array_push(v_fst_5651_, v___x_5762_);
v___x_5764_ = lean_array_push(v_fst_5655_, v___x_5686_);
v___x_5765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5765_, 0, v___x_5711_);
lean_ctor_set(v___x_5765_, 1, v___x_5690_);
v___x_5766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5766_, 0, v___x_5764_);
lean_ctor_set(v___x_5766_, 1, v___x_5765_);
v___x_5767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5767_, 0, v___x_5763_);
lean_ctor_set(v___x_5767_, 1, v___x_5766_);
v___x_5768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5768_, 0, v_fst_5647_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v_a_5637_ = v___x_5768_;
goto v___jp_5636_;
}
}
else
{
lean_object* v_a_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5776_; 
lean_dec_ref(v___x_5711_);
lean_dec(v___x_5708_);
lean_dec_ref(v___x_5690_);
lean_dec(v_fst_5655_);
lean_dec(v_fst_5651_);
lean_dec(v_fst_5647_);
v_a_5769_ = lean_ctor_get(v___x_5729_, 0);
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5776_ == 0)
{
v___x_5771_ = v___x_5729_;
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_a_5769_);
lean_dec(v___x_5729_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v___x_5774_; 
if (v_isShared_5772_ == 0)
{
v___x_5774_ = v___x_5771_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_a_5769_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
}
else
{
lean_dec(v___x_5708_);
goto v___jp_5712_;
}
}
v___jp_5712_:
{
lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5717_; 
v___x_5713_ = lean_box(0);
v___x_5714_ = lean_array_push(v_fst_5651_, v___x_5713_);
v___x_5715_ = lean_array_push(v_fst_5655_, v___x_5686_);
if (v_isShared_5662_ == 0)
{
lean_ctor_set(v___x_5661_, 1, v___x_5690_);
lean_ctor_set(v___x_5661_, 0, v___x_5711_);
v___x_5717_ = v___x_5661_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v___x_5711_);
lean_ctor_set(v_reuseFailAlloc_5727_, 1, v___x_5690_);
v___x_5717_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
lean_object* v___x_5719_; 
if (v_isShared_5658_ == 0)
{
lean_ctor_set(v___x_5657_, 1, v___x_5717_);
lean_ctor_set(v___x_5657_, 0, v___x_5715_);
v___x_5719_ = v___x_5657_;
goto v_reusejp_5718_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v___x_5715_);
lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5717_);
v___x_5719_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5718_;
}
v_reusejp_5718_:
{
lean_object* v___x_5721_; 
if (v_isShared_5654_ == 0)
{
lean_ctor_set(v___x_5653_, 1, v___x_5719_);
lean_ctor_set(v___x_5653_, 0, v___x_5714_);
v___x_5721_ = v___x_5653_;
goto v_reusejp_5720_;
}
else
{
lean_object* v_reuseFailAlloc_5725_; 
v_reuseFailAlloc_5725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5725_, 0, v___x_5714_);
lean_ctor_set(v_reuseFailAlloc_5725_, 1, v___x_5719_);
v___x_5721_ = v_reuseFailAlloc_5725_;
goto v_reusejp_5720_;
}
v_reusejp_5720_:
{
lean_object* v___x_5723_; 
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 1, v___x_5721_);
v___x_5723_ = v___x_5649_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_fst_5647_);
lean_ctor_set(v_reuseFailAlloc_5724_, 1, v___x_5721_);
v___x_5723_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
v_a_5637_ = v___x_5723_;
goto v___jp_5636_;
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
v___jp_5636_:
{
size_t v___x_5638_; size_t v___x_5639_; 
v___x_5638_ = ((size_t)1ULL);
v___x_5639_ = lean_usize_add(v_i_5629_, v___x_5638_);
v_i_5629_ = v___x_5639_;
v_b_5630_ = v_a_5637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5795_, lean_object* v_as_5796_, lean_object* v_sz_5797_, lean_object* v_i_5798_, lean_object* v_b_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
uint8_t v_addEqualities_boxed_5805_; size_t v_sz_boxed_5806_; size_t v_i_boxed_5807_; lean_object* v_res_5808_; 
v_addEqualities_boxed_5805_ = lean_unbox(v_addEqualities_5795_);
v_sz_boxed_5806_ = lean_unbox_usize(v_sz_5797_);
lean_dec(v_sz_5797_);
v_i_boxed_5807_ = lean_unbox_usize(v_i_5798_);
lean_dec(v_i_5798_);
v_res_5808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5805_, v_as_5796_, v_sz_boxed_5806_, v_i_boxed_5807_, v_b_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5801_);
lean_dec_ref(v___y_5800_);
lean_dec_ref(v_as_5796_);
return v_res_5808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5809_, lean_object* v_toMatcherInfo_5810_, lean_object* v_a_5811_, uint8_t v_addEqualities_5812_, size_t v___x_5813_, lean_object* v_discrs_5814_, lean_object* v_motiveArgs_5815_, lean_object* v_motiveBody_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_){
_start:
{
lean_object* v___x_5914_; lean_object* v___x_5915_; uint8_t v___x_5916_; 
v___x_5914_ = lean_array_get_size(v_motiveArgs_5815_);
v___x_5915_ = lean_array_get_size(v_discrs_5814_);
v___x_5916_ = lean_nat_dec_eq(v___x_5914_, v___x_5915_);
if (v___x_5916_ == 0)
{
lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v_a_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5932_; 
lean_dec_ref(v_motiveBody_5816_);
lean_dec_ref(v_motiveArgs_5815_);
lean_dec_ref(v_a_5811_);
lean_dec_ref(v_toMatcherInfo_5810_);
lean_dec_ref(v_onMotive_5809_);
v___x_5917_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5918_ = l_Nat_reprFast(v___x_5915_);
v___x_5919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
v___x_5920_ = l_Lean_MessageData_ofFormat(v___x_5919_);
v___x_5921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5917_);
lean_ctor_set(v___x_5921_, 1, v___x_5920_);
v___x_5922_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5921_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5923_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
v_a_5925_ = lean_ctor_get(v___x_5924_, 0);
v_isSharedCheck_5932_ = !lean_is_exclusive(v___x_5924_);
if (v_isSharedCheck_5932_ == 0)
{
v___x_5927_ = v___x_5924_;
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_a_5925_);
lean_dec(v___x_5924_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___x_5930_; 
if (v_isShared_5928_ == 0)
{
v___x_5930_ = v___x_5927_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_a_5925_);
v___x_5930_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
return v___x_5930_;
}
}
}
else
{
goto v___jp_5822_;
}
v___jp_5822_:
{
lean_object* v___x_5823_; 
lean_inc(v___y_5820_);
lean_inc_ref(v___y_5819_);
lean_inc(v___y_5818_);
lean_inc_ref(v___y_5817_);
lean_inc_ref(v_motiveArgs_5815_);
v___x_5823_ = lean_apply_7(v_onMotive_5809_, v_motiveArgs_5815_, v_motiveBody_5816_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, lean_box(0));
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v_a_5824_; lean_object* v_discrInfos_5825_; lean_object* v___x_5826_; lean_object* v_addHEqualities_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5832_; lean_object* v___x_5833_; lean_object* v___x_5834_; lean_object* v___x_5835_; size_t v_sz_5836_; lean_object* v___x_5837_; 
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
lean_inc(v_a_5824_);
lean_dec_ref_known(v___x_5823_, 1);
v_discrInfos_5825_ = lean_ctor_get(v_toMatcherInfo_5810_, 4);
lean_inc_ref(v_discrInfos_5825_);
lean_dec_ref(v_toMatcherInfo_5810_);
v___x_5826_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5827_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5828_ = lean_array_get_size(v_a_5811_);
v___x_5829_ = l_Array_toSubarray___redArg(v_a_5811_, v___x_5826_, v___x_5828_);
v___x_5830_ = lean_array_get_size(v_discrInfos_5825_);
v___x_5831_ = l_Array_toSubarray___redArg(v_discrInfos_5825_, v___x_5826_, v___x_5830_);
v___x_5832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5832_, 0, v___x_5829_);
lean_ctor_set(v___x_5832_, 1, v___x_5831_);
v___x_5833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5833_, 0, v_addHEqualities_5827_);
lean_ctor_set(v___x_5833_, 1, v___x_5832_);
v___x_5834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5834_, 0, v_addHEqualities_5827_);
lean_ctor_set(v___x_5834_, 1, v___x_5833_);
v___x_5835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5835_, 0, v_a_5824_);
lean_ctor_set(v___x_5835_, 1, v___x_5834_);
v_sz_5836_ = lean_array_size(v_motiveArgs_5815_);
v___x_5837_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5812_, v_motiveArgs_5815_, v_sz_5836_, v___x_5813_, v___x_5835_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; lean_object* v_snd_5839_; lean_object* v_snd_5840_; lean_object* v_fst_5841_; lean_object* v___x_5843_; uint8_t v_isShared_5844_; uint8_t v_isSharedCheck_5896_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5838_);
lean_dec_ref_known(v___x_5837_, 1);
v_snd_5839_ = lean_ctor_get(v_a_5838_, 1);
lean_inc(v_snd_5839_);
v_snd_5840_ = lean_ctor_get(v_snd_5839_, 1);
lean_inc(v_snd_5840_);
v_fst_5841_ = lean_ctor_get(v_a_5838_, 0);
v_isSharedCheck_5896_ = !lean_is_exclusive(v_a_5838_);
if (v_isSharedCheck_5896_ == 0)
{
lean_object* v_unused_5897_; 
v_unused_5897_ = lean_ctor_get(v_a_5838_, 1);
lean_dec(v_unused_5897_);
v___x_5843_ = v_a_5838_;
v_isShared_5844_ = v_isSharedCheck_5896_;
goto v_resetjp_5842_;
}
else
{
lean_inc(v_fst_5841_);
lean_dec(v_a_5838_);
v___x_5843_ = lean_box(0);
v_isShared_5844_ = v_isSharedCheck_5896_;
goto v_resetjp_5842_;
}
v_resetjp_5842_:
{
lean_object* v_fst_5845_; lean_object* v___x_5847_; uint8_t v_isShared_5848_; uint8_t v_isSharedCheck_5894_; 
v_fst_5845_ = lean_ctor_get(v_snd_5839_, 0);
v_isSharedCheck_5894_ = !lean_is_exclusive(v_snd_5839_);
if (v_isSharedCheck_5894_ == 0)
{
lean_object* v_unused_5895_; 
v_unused_5895_ = lean_ctor_get(v_snd_5839_, 1);
lean_dec(v_unused_5895_);
v___x_5847_ = v_snd_5839_;
v_isShared_5848_ = v_isSharedCheck_5894_;
goto v_resetjp_5846_;
}
else
{
lean_inc(v_fst_5845_);
lean_dec(v_snd_5839_);
v___x_5847_ = lean_box(0);
v_isShared_5848_ = v_isSharedCheck_5894_;
goto v_resetjp_5846_;
}
v_resetjp_5846_:
{
lean_object* v_fst_5849_; lean_object* v___x_5851_; uint8_t v_isShared_5852_; uint8_t v_isSharedCheck_5892_; 
v_fst_5849_ = lean_ctor_get(v_snd_5840_, 0);
v_isSharedCheck_5892_ = !lean_is_exclusive(v_snd_5840_);
if (v_isSharedCheck_5892_ == 0)
{
lean_object* v_unused_5893_; 
v_unused_5893_ = lean_ctor_get(v_snd_5840_, 1);
lean_dec(v_unused_5893_);
v___x_5851_ = v_snd_5840_;
v_isShared_5852_ = v_isSharedCheck_5892_;
goto v_resetjp_5850_;
}
else
{
lean_inc(v_fst_5849_);
lean_dec(v_snd_5840_);
v___x_5851_ = lean_box(0);
v_isShared_5852_ = v_isSharedCheck_5892_;
goto v_resetjp_5850_;
}
v_resetjp_5850_:
{
uint8_t v___x_5853_; uint8_t v___x_5854_; uint8_t v___x_5855_; lean_object* v___x_5856_; 
v___x_5853_ = 0;
v___x_5854_ = 1;
v___x_5855_ = 1;
lean_inc(v_fst_5841_);
v___x_5856_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5815_, v_fst_5841_, v___x_5853_, v___x_5854_, v___x_5853_, v___x_5854_, v___x_5855_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
lean_dec_ref(v_motiveArgs_5815_);
if (lean_obj_tag(v___x_5856_) == 0)
{
lean_object* v_a_5857_; lean_object* v___x_5858_; 
v_a_5857_ = lean_ctor_get(v___x_5856_, 0);
lean_inc(v_a_5857_);
lean_dec_ref_known(v___x_5856_, 1);
v___x_5858_ = l_Lean_Meta_getLevel(v_fst_5841_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
if (lean_obj_tag(v___x_5858_) == 0)
{
lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5875_; 
v_a_5859_ = lean_ctor_get(v___x_5858_, 0);
v_isSharedCheck_5875_ = !lean_is_exclusive(v___x_5858_);
if (v_isSharedCheck_5875_ == 0)
{
v___x_5861_ = v___x_5858_;
v_isShared_5862_ = v_isSharedCheck_5875_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5858_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5875_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5864_; 
if (v_isShared_5852_ == 0)
{
lean_ctor_set(v___x_5851_, 1, v_fst_5849_);
lean_ctor_set(v___x_5851_, 0, v_fst_5845_);
v___x_5864_ = v___x_5851_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5874_; 
v_reuseFailAlloc_5874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5874_, 0, v_fst_5845_);
lean_ctor_set(v_reuseFailAlloc_5874_, 1, v_fst_5849_);
v___x_5864_ = v_reuseFailAlloc_5874_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
lean_object* v___x_5866_; 
if (v_isShared_5848_ == 0)
{
lean_ctor_set(v___x_5847_, 1, v___x_5864_);
lean_ctor_set(v___x_5847_, 0, v_a_5859_);
v___x_5866_ = v___x_5847_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5859_);
lean_ctor_set(v_reuseFailAlloc_5873_, 1, v___x_5864_);
v___x_5866_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
lean_object* v___x_5868_; 
if (v_isShared_5844_ == 0)
{
lean_ctor_set(v___x_5843_, 1, v___x_5866_);
lean_ctor_set(v___x_5843_, 0, v_a_5857_);
v___x_5868_ = v___x_5843_;
goto v_reusejp_5867_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_a_5857_);
lean_ctor_set(v_reuseFailAlloc_5872_, 1, v___x_5866_);
v___x_5868_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5867_;
}
v_reusejp_5867_:
{
lean_object* v___x_5870_; 
if (v_isShared_5862_ == 0)
{
lean_ctor_set(v___x_5861_, 0, v___x_5868_);
v___x_5870_ = v___x_5861_;
goto v_reusejp_5869_;
}
else
{
lean_object* v_reuseFailAlloc_5871_; 
v_reuseFailAlloc_5871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5871_, 0, v___x_5868_);
v___x_5870_ = v_reuseFailAlloc_5871_;
goto v_reusejp_5869_;
}
v_reusejp_5869_:
{
return v___x_5870_;
}
}
}
}
}
}
else
{
lean_object* v_a_5876_; lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5883_; 
lean_dec(v_a_5857_);
lean_del_object(v___x_5851_);
lean_dec(v_fst_5849_);
lean_del_object(v___x_5847_);
lean_dec(v_fst_5845_);
lean_del_object(v___x_5843_);
v_a_5876_ = lean_ctor_get(v___x_5858_, 0);
v_isSharedCheck_5883_ = !lean_is_exclusive(v___x_5858_);
if (v_isSharedCheck_5883_ == 0)
{
v___x_5878_ = v___x_5858_;
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
else
{
lean_inc(v_a_5876_);
lean_dec(v___x_5858_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5883_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v___x_5881_; 
if (v_isShared_5879_ == 0)
{
v___x_5881_ = v___x_5878_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v_a_5876_);
v___x_5881_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
return v___x_5881_;
}
}
}
}
else
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5891_; 
lean_del_object(v___x_5851_);
lean_dec(v_fst_5849_);
lean_del_object(v___x_5847_);
lean_dec(v_fst_5845_);
lean_del_object(v___x_5843_);
lean_dec(v_fst_5841_);
v_a_5884_ = lean_ctor_get(v___x_5856_, 0);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___x_5856_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5886_ = v___x_5856_;
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v___x_5856_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5889_; 
if (v_isShared_5887_ == 0)
{
v___x_5889_ = v___x_5886_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5890_; 
v_reuseFailAlloc_5890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
v___x_5889_ = v_reuseFailAlloc_5890_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
return v___x_5889_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5905_; 
lean_dec_ref(v_motiveArgs_5815_);
v_a_5898_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5900_ = v___x_5837_;
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_a_5898_);
lean_dec(v___x_5837_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v___x_5903_; 
if (v_isShared_5901_ == 0)
{
v___x_5903_ = v___x_5900_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5898_);
v___x_5903_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
return v___x_5903_;
}
}
}
}
else
{
lean_object* v_a_5906_; lean_object* v___x_5908_; uint8_t v_isShared_5909_; uint8_t v_isSharedCheck_5913_; 
lean_dec_ref(v_motiveArgs_5815_);
lean_dec_ref(v_a_5811_);
lean_dec_ref(v_toMatcherInfo_5810_);
v_a_5906_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5913_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5913_ == 0)
{
v___x_5908_ = v___x_5823_;
v_isShared_5909_ = v_isSharedCheck_5913_;
goto v_resetjp_5907_;
}
else
{
lean_inc(v_a_5906_);
lean_dec(v___x_5823_);
v___x_5908_ = lean_box(0);
v_isShared_5909_ = v_isSharedCheck_5913_;
goto v_resetjp_5907_;
}
v_resetjp_5907_:
{
lean_object* v___x_5911_; 
if (v_isShared_5909_ == 0)
{
v___x_5911_ = v___x_5908_;
goto v_reusejp_5910_;
}
else
{
lean_object* v_reuseFailAlloc_5912_; 
v_reuseFailAlloc_5912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5912_, 0, v_a_5906_);
v___x_5911_ = v_reuseFailAlloc_5912_;
goto v_reusejp_5910_;
}
v_reusejp_5910_:
{
return v___x_5911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5933_, lean_object* v_toMatcherInfo_5934_, lean_object* v_a_5935_, lean_object* v_addEqualities_5936_, lean_object* v___x_5937_, lean_object* v_discrs_5938_, lean_object* v_motiveArgs_5939_, lean_object* v_motiveBody_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_, lean_object* v___y_5945_){
_start:
{
uint8_t v_addEqualities_boxed_5946_; size_t v___x_34593__boxed_5947_; lean_object* v_res_5948_; 
v_addEqualities_boxed_5946_ = lean_unbox(v_addEqualities_5936_);
v___x_34593__boxed_5947_ = lean_unbox_usize(v___x_5937_);
lean_dec(v___x_5937_);
v_res_5948_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5933_, v_toMatcherInfo_5934_, v_a_5935_, v_addEqualities_boxed_5946_, v___x_34593__boxed_5947_, v_discrs_5938_, v_motiveArgs_5939_, v_motiveBody_5940_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
lean_dec(v___y_5944_);
lean_dec_ref(v___y_5943_);
lean_dec(v___y_5942_);
lean_dec_ref(v___y_5941_);
lean_dec_ref(v_discrs_5938_);
return v_res_5948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5949_, size_t v_sz_5950_, size_t v_i_5951_, lean_object* v_b_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_){
_start:
{
lean_object* v_a_5959_; uint8_t v___x_5963_; 
v___x_5963_ = lean_usize_dec_lt(v_i_5951_, v_sz_5950_);
if (v___x_5963_ == 0)
{
lean_object* v___x_5964_; 
v___x_5964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5964_, 0, v_b_5952_);
return v___x_5964_;
}
else
{
lean_object* v_snd_5965_; lean_object* v_snd_5966_; lean_object* v_fst_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_6027_; 
v_snd_5965_ = lean_ctor_get(v_b_5952_, 1);
lean_inc(v_snd_5965_);
v_snd_5966_ = lean_ctor_get(v_snd_5965_, 1);
lean_inc(v_snd_5966_);
v_fst_5967_ = lean_ctor_get(v_b_5952_, 0);
v_isSharedCheck_6027_ = !lean_is_exclusive(v_b_5952_);
if (v_isSharedCheck_6027_ == 0)
{
lean_object* v_unused_6028_; 
v_unused_6028_ = lean_ctor_get(v_b_5952_, 1);
lean_dec(v_unused_6028_);
v___x_5969_ = v_b_5952_;
v_isShared_5970_ = v_isSharedCheck_6027_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_fst_5967_);
lean_dec(v_b_5952_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_6027_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v_fst_5971_; lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_6025_; 
v_fst_5971_ = lean_ctor_get(v_snd_5965_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v_snd_5965_);
if (v_isSharedCheck_6025_ == 0)
{
lean_object* v_unused_6026_; 
v_unused_6026_ = lean_ctor_get(v_snd_5965_, 1);
lean_dec(v_unused_6026_);
v___x_5973_ = v_snd_5965_;
v_isShared_5974_ = v_isSharedCheck_6025_;
goto v_resetjp_5972_;
}
else
{
lean_inc(v_fst_5971_);
lean_dec(v_snd_5965_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_6025_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v_array_5975_; lean_object* v_start_5976_; lean_object* v_stop_5977_; uint8_t v___x_5978_; 
v_array_5975_ = lean_ctor_get(v_snd_5966_, 0);
v_start_5976_ = lean_ctor_get(v_snd_5966_, 1);
v_stop_5977_ = lean_ctor_get(v_snd_5966_, 2);
v___x_5978_ = lean_nat_dec_lt(v_start_5976_, v_stop_5977_);
if (v___x_5978_ == 0)
{
lean_object* v___x_5980_; 
if (v_isShared_5974_ == 0)
{
v___x_5980_ = v___x_5973_;
goto v_reusejp_5979_;
}
else
{
lean_object* v_reuseFailAlloc_5985_; 
v_reuseFailAlloc_5985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5985_, 0, v_fst_5971_);
lean_ctor_set(v_reuseFailAlloc_5985_, 1, v_snd_5966_);
v___x_5980_ = v_reuseFailAlloc_5985_;
goto v_reusejp_5979_;
}
v_reusejp_5979_:
{
lean_object* v___x_5982_; 
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 1, v___x_5980_);
v___x_5982_ = v___x_5969_;
goto v_reusejp_5981_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v_fst_5967_);
lean_ctor_set(v_reuseFailAlloc_5984_, 1, v___x_5980_);
v___x_5982_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5981_;
}
v_reusejp_5981_:
{
lean_object* v___x_5983_; 
v___x_5983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5983_, 0, v___x_5982_);
return v___x_5983_;
}
}
}
else
{
lean_object* v___x_5987_; uint8_t v_isShared_5988_; uint8_t v_isSharedCheck_6021_; 
lean_inc(v_stop_5977_);
lean_inc(v_start_5976_);
lean_inc_ref(v_array_5975_);
v_isSharedCheck_6021_ = !lean_is_exclusive(v_snd_5966_);
if (v_isSharedCheck_6021_ == 0)
{
lean_object* v_unused_6022_; lean_object* v_unused_6023_; lean_object* v_unused_6024_; 
v_unused_6022_ = lean_ctor_get(v_snd_5966_, 2);
lean_dec(v_unused_6022_);
v_unused_6023_ = lean_ctor_get(v_snd_5966_, 1);
lean_dec(v_unused_6023_);
v_unused_6024_ = lean_ctor_get(v_snd_5966_, 0);
lean_dec(v_unused_6024_);
v___x_5987_ = v_snd_5966_;
v_isShared_5988_ = v_isSharedCheck_6021_;
goto v_resetjp_5986_;
}
else
{
lean_dec(v_snd_5966_);
v___x_5987_ = lean_box(0);
v_isShared_5988_ = v_isSharedCheck_6021_;
goto v_resetjp_5986_;
}
v_resetjp_5986_:
{
lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5993_; 
v___x_5989_ = lean_array_fget(v_array_5975_, v_start_5976_);
v___x_5990_ = lean_unsigned_to_nat(1u);
v___x_5991_ = lean_nat_add(v_start_5976_, v___x_5990_);
lean_dec(v_start_5976_);
if (v_isShared_5988_ == 0)
{
lean_ctor_set(v___x_5987_, 1, v___x_5991_);
v___x_5993_ = v___x_5987_;
goto v_reusejp_5992_;
}
else
{
lean_object* v_reuseFailAlloc_6020_; 
v_reuseFailAlloc_6020_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_array_5975_);
lean_ctor_set(v_reuseFailAlloc_6020_, 1, v___x_5991_);
lean_ctor_set(v_reuseFailAlloc_6020_, 2, v_stop_5977_);
v___x_5993_ = v_reuseFailAlloc_6020_;
goto v_reusejp_5992_;
}
v_reusejp_5992_:
{
lean_object* v___y_5995_; 
if (lean_obj_tag(v___x_5989_) == 0)
{
lean_object* v___x_6013_; lean_object* v___x_6014_; 
lean_del_object(v___x_5973_);
lean_del_object(v___x_5969_);
v___x_6013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6013_, 0, v_fst_5971_);
lean_ctor_set(v___x_6013_, 1, v___x_5993_);
v___x_6014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6014_, 0, v_fst_5967_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v_a_5959_ = v___x_6014_;
goto v___jp_5958_;
}
else
{
lean_object* v_val_6015_; lean_object* v_a_6016_; uint8_t v___x_6017_; 
v_val_6015_ = lean_ctor_get(v___x_5989_, 0);
lean_inc(v_val_6015_);
lean_dec_ref_known(v___x_5989_, 1);
v_a_6016_ = lean_array_uget_borrowed(v_as_5949_, v_i_5951_);
v___x_6017_ = lean_unbox(v_val_6015_);
lean_dec(v_val_6015_);
if (v___x_6017_ == 0)
{
lean_object* v___x_6018_; 
lean_inc(v_a_6016_);
v___x_6018_ = l_Lean_Meta_mkEqRefl(v_a_6016_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_);
v___y_5995_ = v___x_6018_;
goto v___jp_5994_;
}
else
{
lean_object* v___x_6019_; 
lean_inc(v_a_6016_);
v___x_6019_ = l_Lean_Meta_mkHEqRefl(v_a_6016_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_);
v___y_5995_ = v___x_6019_;
goto v___jp_5994_;
}
}
v___jp_5994_:
{
if (lean_obj_tag(v___y_5995_) == 0)
{
lean_object* v_a_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_6000_; 
v_a_5996_ = lean_ctor_get(v___y_5995_, 0);
lean_inc(v_a_5996_);
lean_dec_ref_known(v___y_5995_, 1);
v___x_5997_ = lean_array_push(v_fst_5967_, v_a_5996_);
v___x_5998_ = lean_nat_add(v_fst_5971_, v___x_5990_);
lean_dec(v_fst_5971_);
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 1, v___x_5993_);
lean_ctor_set(v___x_5973_, 0, v___x_5998_);
v___x_6000_ = v___x_5973_;
goto v_reusejp_5999_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v___x_5998_);
lean_ctor_set(v_reuseFailAlloc_6004_, 1, v___x_5993_);
v___x_6000_ = v_reuseFailAlloc_6004_;
goto v_reusejp_5999_;
}
v_reusejp_5999_:
{
lean_object* v___x_6002_; 
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 1, v___x_6000_);
lean_ctor_set(v___x_5969_, 0, v___x_5997_);
v___x_6002_ = v___x_5969_;
goto v_reusejp_6001_;
}
else
{
lean_object* v_reuseFailAlloc_6003_; 
v_reuseFailAlloc_6003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6003_, 0, v___x_5997_);
lean_ctor_set(v_reuseFailAlloc_6003_, 1, v___x_6000_);
v___x_6002_ = v_reuseFailAlloc_6003_;
goto v_reusejp_6001_;
}
v_reusejp_6001_:
{
v_a_5959_ = v___x_6002_;
goto v___jp_5958_;
}
}
}
else
{
lean_object* v_a_6005_; lean_object* v___x_6007_; uint8_t v_isShared_6008_; uint8_t v_isSharedCheck_6012_; 
lean_dec_ref(v___x_5993_);
lean_del_object(v___x_5973_);
lean_dec(v_fst_5971_);
lean_del_object(v___x_5969_);
lean_dec(v_fst_5967_);
v_a_6005_ = lean_ctor_get(v___y_5995_, 0);
v_isSharedCheck_6012_ = !lean_is_exclusive(v___y_5995_);
if (v_isSharedCheck_6012_ == 0)
{
v___x_6007_ = v___y_5995_;
v_isShared_6008_ = v_isSharedCheck_6012_;
goto v_resetjp_6006_;
}
else
{
lean_inc(v_a_6005_);
lean_dec(v___y_5995_);
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
}
}
}
}
}
}
}
v___jp_5958_:
{
size_t v___x_5960_; size_t v___x_5961_; 
v___x_5960_ = ((size_t)1ULL);
v___x_5961_ = lean_usize_add(v_i_5951_, v___x_5960_);
v_i_5951_ = v___x_5961_;
v_b_5952_ = v_a_5959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6029_, lean_object* v_sz_6030_, lean_object* v_i_6031_, lean_object* v_b_6032_, lean_object* v___y_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_){
_start:
{
size_t v_sz_boxed_6038_; size_t v_i_boxed_6039_; lean_object* v_res_6040_; 
v_sz_boxed_6038_ = lean_unbox_usize(v_sz_6030_);
lean_dec(v_sz_6030_);
v_i_boxed_6039_ = lean_unbox_usize(v_i_6031_);
lean_dec(v_i_6031_);
v_res_6040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6029_, v_sz_boxed_6038_, v_i_boxed_6039_, v_b_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
lean_dec(v___y_6036_);
lean_dec_ref(v___y_6035_);
lean_dec(v___y_6034_);
lean_dec_ref(v___y_6033_);
lean_dec_ref(v_as_6029_);
return v_res_6040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_){
_start:
{
lean_object* v___x_6047_; 
v___x_6047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6041_);
return v___x_6047_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_){
_start:
{
lean_object* v_res_6054_; 
v_res_6054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_);
lean_dec(v___y_6052_);
lean_dec_ref(v___y_6051_);
lean_dec(v___y_6050_);
lean_dec_ref(v___y_6049_);
return v_res_6054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6055_, size_t v_i_6056_, lean_object* v_bs_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_){
_start:
{
uint8_t v___x_6062_; 
v___x_6062_ = lean_usize_dec_lt(v_i_6056_, v_sz_6055_);
if (v___x_6062_ == 0)
{
lean_object* v___x_6063_; 
v___x_6063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6063_, 0, v_bs_6057_);
return v___x_6063_;
}
else
{
lean_object* v_v_6064_; lean_object* v___x_6065_; lean_object* v_bs_x27_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; 
v_v_6064_ = lean_array_uget(v_bs_6057_, v_i_6056_);
v___x_6065_ = lean_unsigned_to_nat(0u);
v_bs_x27_6066_ = lean_array_uset(v_bs_6057_, v_i_6056_, v___x_6065_);
v___x_6067_ = l_Lean_Expr_fvarId_x21(v_v_6064_);
lean_dec(v_v_6064_);
v___x_6068_ = l_Lean_FVarId_getUserName___redArg(v___x_6067_, v___y_6058_, v___y_6059_, v___y_6060_);
if (lean_obj_tag(v___x_6068_) == 0)
{
lean_object* v_a_6069_; size_t v___x_6070_; size_t v___x_6071_; lean_object* v___x_6072_; 
v_a_6069_ = lean_ctor_get(v___x_6068_, 0);
lean_inc(v_a_6069_);
lean_dec_ref_known(v___x_6068_, 1);
v___x_6070_ = ((size_t)1ULL);
v___x_6071_ = lean_usize_add(v_i_6056_, v___x_6070_);
v___x_6072_ = lean_array_uset(v_bs_x27_6066_, v_i_6056_, v_a_6069_);
v_i_6056_ = v___x_6071_;
v_bs_6057_ = v___x_6072_;
goto _start;
}
else
{
lean_object* v_a_6074_; lean_object* v___x_6076_; uint8_t v_isShared_6077_; uint8_t v_isSharedCheck_6081_; 
lean_dec_ref(v_bs_x27_6066_);
v_a_6074_ = lean_ctor_get(v___x_6068_, 0);
v_isSharedCheck_6081_ = !lean_is_exclusive(v___x_6068_);
if (v_isSharedCheck_6081_ == 0)
{
v___x_6076_ = v___x_6068_;
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
else
{
lean_inc(v_a_6074_);
lean_dec(v___x_6068_);
v___x_6076_ = lean_box(0);
v_isShared_6077_ = v_isSharedCheck_6081_;
goto v_resetjp_6075_;
}
v_resetjp_6075_:
{
lean_object* v___x_6079_; 
if (v_isShared_6077_ == 0)
{
v___x_6079_ = v___x_6076_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v_a_6074_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6082_, lean_object* v_i_6083_, lean_object* v_bs_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_){
_start:
{
size_t v_sz_boxed_6089_; size_t v_i_boxed_6090_; lean_object* v_res_6091_; 
v_sz_boxed_6089_ = lean_unbox_usize(v_sz_6082_);
lean_dec(v_sz_6082_);
v_i_boxed_6090_ = lean_unbox_usize(v_i_6083_);
lean_dec(v_i_6083_);
v_res_6091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6089_, v_i_boxed_6090_, v_bs_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
lean_dec(v___y_6087_);
lean_dec_ref(v___y_6086_);
lean_dec_ref(v___y_6085_);
return v_res_6091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6092_, lean_object* v_x_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_){
_start:
{
size_t v_sz_6099_; size_t v___x_6100_; lean_object* v___x_6101_; 
v_sz_6099_ = lean_array_size(v_xs_6092_);
v___x_6100_ = ((size_t)0ULL);
v___x_6101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6099_, v___x_6100_, v_xs_6092_, v___y_6094_, v___y_6096_, v___y_6097_);
return v___x_6101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6102_, lean_object* v_x_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_){
_start:
{
lean_object* v_res_6109_; 
v_res_6109_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6102_, v_x_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
lean_dec(v___y_6107_);
lean_dec_ref(v___y_6106_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
lean_dec_ref(v_x_6103_);
return v_res_6109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6110_, lean_object* v___x_6111_, lean_object* v___f_6112_, uint8_t v___x_6113_, lean_object* v_fst_6114_, lean_object* v___x_6115_, lean_object* v___x_6116_, lean_object* v___x_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_){
_start:
{
lean_object* v___x_6123_; 
v___x_6123_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v___x_6110_, v___x_6111_, v___f_6112_, v___x_6113_, v___x_6113_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_);
if (lean_obj_tag(v___x_6123_) == 0)
{
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6136_; 
v_a_6124_ = lean_ctor_get(v___x_6123_, 0);
v_isSharedCheck_6136_ = !lean_is_exclusive(v___x_6123_);
if (v_isSharedCheck_6136_ == 0)
{
v___x_6126_ = v___x_6123_;
v_isShared_6127_ = v_isSharedCheck_6136_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6123_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6136_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6134_; 
v___x_6128_ = lean_array_push(v_fst_6114_, v_a_6124_);
v___x_6129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6129_, 0, v___x_6115_);
lean_ctor_set(v___x_6129_, 1, v___x_6116_);
v___x_6130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6130_, 0, v___x_6117_);
lean_ctor_set(v___x_6130_, 1, v___x_6129_);
v___x_6131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6131_, 0, v___x_6128_);
lean_ctor_set(v___x_6131_, 1, v___x_6130_);
v___x_6132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6132_, 0, v___x_6131_);
if (v_isShared_6127_ == 0)
{
lean_ctor_set(v___x_6126_, 0, v___x_6132_);
v___x_6134_ = v___x_6126_;
goto v_reusejp_6133_;
}
else
{
lean_object* v_reuseFailAlloc_6135_; 
v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6135_, 0, v___x_6132_);
v___x_6134_ = v_reuseFailAlloc_6135_;
goto v_reusejp_6133_;
}
v_reusejp_6133_:
{
return v___x_6134_;
}
}
}
else
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6144_; 
lean_dec_ref(v___x_6117_);
lean_dec_ref(v___x_6116_);
lean_dec_ref(v___x_6115_);
lean_dec(v_fst_6114_);
v_a_6137_ = lean_ctor_get(v___x_6123_, 0);
v_isSharedCheck_6144_ = !lean_is_exclusive(v___x_6123_);
if (v_isSharedCheck_6144_ == 0)
{
v___x_6139_ = v___x_6123_;
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v___x_6123_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v___x_6142_; 
if (v_isShared_6140_ == 0)
{
v___x_6142_ = v___x_6139_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_a_6137_);
v___x_6142_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
return v___x_6142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6145_, lean_object* v___x_6146_, lean_object* v___f_6147_, lean_object* v___x_6148_, lean_object* v_fst_6149_, lean_object* v___x_6150_, lean_object* v___x_6151_, lean_object* v___x_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
uint8_t v___x_35056__boxed_6158_; lean_object* v_res_6159_; 
v___x_35056__boxed_6158_ = lean_unbox(v___x_6148_);
v_res_6159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6145_, v___x_6146_, v___f_6147_, v___x_35056__boxed_6158_, v_fst_6149_, v___x_6150_, v___x_6151_, v___x_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
lean_dec(v___y_6156_);
lean_dec_ref(v___y_6155_);
lean_dec(v___y_6154_);
lean_dec_ref(v___y_6153_);
return v_res_6159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6160_, lean_object* v_names_6161_, lean_object* v_k_6162_, lean_object* v___y_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_){
_start:
{
lean_object* v___x_6168_; 
v___x_6168_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6160_, v_names_6161_, v_k_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v_a_6169_; lean_object* v___x_6171_; uint8_t v_isShared_6172_; uint8_t v_isSharedCheck_6176_; 
v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6176_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6176_ == 0)
{
v___x_6171_ = v___x_6168_;
v_isShared_6172_ = v_isSharedCheck_6176_;
goto v_resetjp_6170_;
}
else
{
lean_inc(v_a_6169_);
lean_dec(v___x_6168_);
v___x_6171_ = lean_box(0);
v_isShared_6172_ = v_isSharedCheck_6176_;
goto v_resetjp_6170_;
}
v_resetjp_6170_:
{
lean_object* v___x_6174_; 
if (v_isShared_6172_ == 0)
{
v___x_6174_ = v___x_6171_;
goto v_reusejp_6173_;
}
else
{
lean_object* v_reuseFailAlloc_6175_; 
v_reuseFailAlloc_6175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6175_, 0, v_a_6169_);
v___x_6174_ = v_reuseFailAlloc_6175_;
goto v_reusejp_6173_;
}
v_reusejp_6173_:
{
return v___x_6174_;
}
}
}
else
{
lean_object* v_a_6177_; lean_object* v___x_6179_; uint8_t v_isShared_6180_; uint8_t v_isSharedCheck_6184_; 
v_a_6177_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6184_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6184_ == 0)
{
v___x_6179_ = v___x_6168_;
v_isShared_6180_ = v_isSharedCheck_6184_;
goto v_resetjp_6178_;
}
else
{
lean_inc(v_a_6177_);
lean_dec(v___x_6168_);
v___x_6179_ = lean_box(0);
v_isShared_6180_ = v_isSharedCheck_6184_;
goto v_resetjp_6178_;
}
v_resetjp_6178_:
{
lean_object* v___x_6182_; 
if (v_isShared_6180_ == 0)
{
v___x_6182_ = v___x_6179_;
goto v_reusejp_6181_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v_a_6177_);
v___x_6182_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6181_;
}
v_reusejp_6181_:
{
return v___x_6182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6185_, lean_object* v_names_6186_, lean_object* v_k_6187_, lean_object* v___y_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_){
_start:
{
lean_object* v_res_6193_; 
v_res_6193_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6185_, v_names_6186_, v_k_6187_, v___y_6188_, v___y_6189_, v___y_6190_, v___y_6191_);
lean_dec(v___y_6191_);
lean_dec_ref(v___y_6190_);
lean_dec(v___y_6189_);
lean_dec_ref(v___y_6188_);
lean_dec_ref(v_names_6186_);
lean_dec_ref(v_fvars_6185_);
return v_res_6193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6194_, lean_object* v_xs_6195_, lean_object* v_remaining_x27_6196_, lean_object* v_ys4_6197_, lean_object* v_onAlt_6198_, lean_object* v_a_6199_, lean_object* v_altType_6200_, uint8_t v___x_6201_, uint8_t v___x_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_){
_start:
{
lean_object* v___x_6208_; 
v___x_6208_ = l_Lean_Meta_instantiateLambda(v___x_6194_, v_xs_6195_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_);
if (lean_obj_tag(v___x_6208_) == 0)
{
lean_object* v_a_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; 
v_a_6209_ = lean_ctor_get(v___x_6208_, 0);
lean_inc(v_a_6209_);
lean_dec_ref_known(v___x_6208_, 1);
lean_inc_ref(v_ys4_6197_);
lean_inc_ref(v_remaining_x27_6196_);
lean_inc_ref_n(v_xs_6195_, 2);
v___x_6210_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6210_, 0, v_xs_6195_);
lean_ctor_set(v___x_6210_, 1, v_xs_6195_);
lean_ctor_set(v___x_6210_, 2, v_remaining_x27_6196_);
lean_ctor_set(v___x_6210_, 3, v_remaining_x27_6196_);
lean_ctor_set(v___x_6210_, 4, v_ys4_6197_);
lean_inc(v___y_6206_);
lean_inc_ref(v___y_6205_);
lean_inc(v___y_6204_);
lean_inc_ref(v___y_6203_);
v___x_6211_ = lean_apply_9(v_onAlt_6198_, v_a_6199_, v_altType_6200_, v___x_6210_, v_a_6209_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_, lean_box(0));
if (lean_obj_tag(v___x_6211_) == 0)
{
lean_object* v_a_6212_; lean_object* v___x_6213_; uint8_t v___x_6214_; lean_object* v___x_6215_; 
v_a_6212_ = lean_ctor_get(v___x_6211_, 0);
lean_inc(v_a_6212_);
lean_dec_ref_known(v___x_6211_, 1);
v___x_6213_ = l_Array_append___redArg(v_xs_6195_, v_ys4_6197_);
lean_dec_ref(v_ys4_6197_);
v___x_6214_ = 1;
v___x_6215_ = l_Lean_Meta_mkLambdaFVars(v___x_6213_, v_a_6212_, v___x_6201_, v___x_6202_, v___x_6201_, v___x_6202_, v___x_6214_, v___y_6203_, v___y_6204_, v___y_6205_, v___y_6206_);
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec_ref(v___x_6213_);
return v___x_6215_;
}
else
{
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec_ref(v_ys4_6197_);
lean_dec_ref(v_xs_6195_);
return v___x_6211_;
}
}
else
{
lean_dec(v___y_6206_);
lean_dec_ref(v___y_6205_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec_ref(v_altType_6200_);
lean_dec(v_a_6199_);
lean_dec_ref(v_onAlt_6198_);
lean_dec_ref(v_ys4_6197_);
lean_dec_ref(v_remaining_x27_6196_);
lean_dec_ref(v_xs_6195_);
return v___x_6208_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6216_, lean_object* v_xs_6217_, lean_object* v_remaining_x27_6218_, lean_object* v_ys4_6219_, lean_object* v_onAlt_6220_, lean_object* v_a_6221_, lean_object* v_altType_6222_, lean_object* v___x_6223_, lean_object* v___x_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_){
_start:
{
uint8_t v___x_35183__boxed_6230_; uint8_t v___x_35184__boxed_6231_; lean_object* v_res_6232_; 
v___x_35183__boxed_6230_ = lean_unbox(v___x_6223_);
v___x_35184__boxed_6231_ = lean_unbox(v___x_6224_);
v_res_6232_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6216_, v_xs_6217_, v_remaining_x27_6218_, v_ys4_6219_, v_onAlt_6220_, v_a_6221_, v_altType_6222_, v___x_35183__boxed_6230_, v___x_35184__boxed_6231_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
return v_res_6232_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6233_, lean_object* v_xs_6234_, lean_object* v_remaining_x27_6235_, lean_object* v_onAlt_6236_, lean_object* v_a_6237_, uint8_t v___x_6238_, uint8_t v___x_6239_, lean_object* v___f_6240_, lean_object* v_ys4_6241_, lean_object* v_altType_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_, lean_object* v___y_6245_, lean_object* v___y_6246_){
_start:
{
lean_object* v___x_6248_; lean_object* v___x_6249_; lean_object* v___f_6250_; lean_object* v___x_6251_; 
v___x_6248_ = lean_box(v___x_6238_);
v___x_6249_ = lean_box(v___x_6239_);
lean_inc_ref(v_xs_6234_);
lean_inc_ref(v___x_6233_);
v___f_6250_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6250_, 0, v___x_6233_);
lean_closure_set(v___f_6250_, 1, v_xs_6234_);
lean_closure_set(v___f_6250_, 2, v_remaining_x27_6235_);
lean_closure_set(v___f_6250_, 3, v_ys4_6241_);
lean_closure_set(v___f_6250_, 4, v_onAlt_6236_);
lean_closure_set(v___f_6250_, 5, v_a_6237_);
lean_closure_set(v___f_6250_, 6, v_altType_6242_);
lean_closure_set(v___f_6250_, 7, v___x_6248_);
lean_closure_set(v___f_6250_, 8, v___x_6249_);
v___x_6251_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6233_, v___f_6240_, v___x_6238_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
if (lean_obj_tag(v___x_6251_) == 0)
{
lean_object* v_a_6252_; lean_object* v___x_6253_; 
v_a_6252_ = lean_ctor_get(v___x_6251_, 0);
lean_inc(v_a_6252_);
lean_dec_ref_known(v___x_6251_, 1);
v___x_6253_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6234_, v_a_6252_, v___f_6250_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
lean_dec(v_a_6252_);
lean_dec_ref(v_xs_6234_);
return v___x_6253_;
}
else
{
lean_object* v_a_6254_; lean_object* v___x_6256_; uint8_t v_isShared_6257_; uint8_t v_isSharedCheck_6261_; 
lean_dec_ref(v___f_6250_);
lean_dec_ref(v_xs_6234_);
v_a_6254_ = lean_ctor_get(v___x_6251_, 0);
v_isSharedCheck_6261_ = !lean_is_exclusive(v___x_6251_);
if (v_isSharedCheck_6261_ == 0)
{
v___x_6256_ = v___x_6251_;
v_isShared_6257_ = v_isSharedCheck_6261_;
goto v_resetjp_6255_;
}
else
{
lean_inc(v_a_6254_);
lean_dec(v___x_6251_);
v___x_6256_ = lean_box(0);
v_isShared_6257_ = v_isSharedCheck_6261_;
goto v_resetjp_6255_;
}
v_resetjp_6255_:
{
lean_object* v___x_6259_; 
if (v_isShared_6257_ == 0)
{
v___x_6259_ = v___x_6256_;
goto v_reusejp_6258_;
}
else
{
lean_object* v_reuseFailAlloc_6260_; 
v_reuseFailAlloc_6260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6254_);
v___x_6259_ = v_reuseFailAlloc_6260_;
goto v_reusejp_6258_;
}
v_reusejp_6258_:
{
return v___x_6259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6262_, lean_object* v_xs_6263_, lean_object* v_remaining_x27_6264_, lean_object* v_onAlt_6265_, lean_object* v_a_6266_, lean_object* v___x_6267_, lean_object* v___x_6268_, lean_object* v___f_6269_, lean_object* v_ys4_6270_, lean_object* v_altType_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_){
_start:
{
uint8_t v___x_35225__boxed_6277_; uint8_t v___x_35226__boxed_6278_; lean_object* v_res_6279_; 
v___x_35225__boxed_6277_ = lean_unbox(v___x_6267_);
v___x_35226__boxed_6278_ = lean_unbox(v___x_6268_);
v_res_6279_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6262_, v_xs_6263_, v_remaining_x27_6264_, v_onAlt_6265_, v_a_6266_, v___x_35225__boxed_6277_, v___x_35226__boxed_6278_, v___f_6269_, v_ys4_6270_, v_altType_6271_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
return v_res_6279_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6280_, lean_object* v_remaining_x27_6281_, lean_object* v_onAlt_6282_, lean_object* v_a_6283_, uint8_t v___x_6284_, uint8_t v___x_6285_, lean_object* v___f_6286_, lean_object* v_extraEqualities_6287_, lean_object* v_xs_6288_, lean_object* v_altType_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_){
_start:
{
lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___f_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; 
v___x_6295_ = lean_box(v___x_6284_);
v___x_6296_ = lean_box(v___x_6285_);
v___f_6297_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6297_, 0, v___x_6280_);
lean_closure_set(v___f_6297_, 1, v_xs_6288_);
lean_closure_set(v___f_6297_, 2, v_remaining_x27_6281_);
lean_closure_set(v___f_6297_, 3, v_onAlt_6282_);
lean_closure_set(v___f_6297_, 4, v_a_6283_);
lean_closure_set(v___f_6297_, 5, v___x_6295_);
lean_closure_set(v___f_6297_, 6, v___x_6296_);
lean_closure_set(v___f_6297_, 7, v___f_6286_);
v___x_6298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6298_, 0, v_extraEqualities_6287_);
v___x_6299_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_6289_, v___x_6298_, v___f_6297_, v___x_6284_, v___x_6284_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
return v___x_6299_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6300_, lean_object* v_remaining_x27_6301_, lean_object* v_onAlt_6302_, lean_object* v_a_6303_, lean_object* v___x_6304_, lean_object* v___x_6305_, lean_object* v___f_6306_, lean_object* v_extraEqualities_6307_, lean_object* v_xs_6308_, lean_object* v_altType_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_){
_start:
{
uint8_t v___x_35280__boxed_6315_; uint8_t v___x_35281__boxed_6316_; lean_object* v_res_6317_; 
v___x_35280__boxed_6315_ = lean_unbox(v___x_6304_);
v___x_35281__boxed_6316_ = lean_unbox(v___x_6305_);
v_res_6317_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6300_, v_remaining_x27_6301_, v_onAlt_6302_, v_a_6303_, v___x_35280__boxed_6315_, v___x_35281__boxed_6316_, v___f_6306_, v_extraEqualities_6307_, v_xs_6308_, v_altType_6309_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_);
lean_dec(v___y_6313_);
lean_dec_ref(v___y_6312_);
lean_dec(v___y_6311_);
lean_dec_ref(v___y_6310_);
return v_res_6317_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6319_, lean_object* v_onAlt_6320_, lean_object* v_extraEqualities_6321_, lean_object* v_a_6322_, lean_object* v_b_6323_, lean_object* v___y_6324_, lean_object* v___y_6325_, lean_object* v___y_6326_, lean_object* v___y_6327_){
_start:
{
lean_object* v___y_6330_; uint8_t v___x_6353_; 
v___x_6353_ = lean_nat_dec_lt(v_a_6322_, v_upperBound_6319_);
if (v___x_6353_ == 0)
{
lean_object* v___x_6354_; 
lean_dec(v_a_6322_);
lean_dec(v_extraEqualities_6321_);
lean_dec_ref(v_onAlt_6320_);
v___x_6354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6354_, 0, v_b_6323_);
return v___x_6354_;
}
else
{
lean_object* v_snd_6355_; lean_object* v_snd_6356_; lean_object* v_snd_6357_; lean_object* v_fst_6358_; lean_object* v___x_6360_; uint8_t v_isShared_6361_; uint8_t v_isSharedCheck_6465_; 
v_snd_6355_ = lean_ctor_get(v_b_6323_, 1);
lean_inc(v_snd_6355_);
v_snd_6356_ = lean_ctor_get(v_snd_6355_, 1);
lean_inc(v_snd_6356_);
v_snd_6357_ = lean_ctor_get(v_snd_6356_, 1);
lean_inc(v_snd_6357_);
v_fst_6358_ = lean_ctor_get(v_b_6323_, 0);
v_isSharedCheck_6465_ = !lean_is_exclusive(v_b_6323_);
if (v_isSharedCheck_6465_ == 0)
{
lean_object* v_unused_6466_; 
v_unused_6466_ = lean_ctor_get(v_b_6323_, 1);
lean_dec(v_unused_6466_);
v___x_6360_ = v_b_6323_;
v_isShared_6361_ = v_isSharedCheck_6465_;
goto v_resetjp_6359_;
}
else
{
lean_inc(v_fst_6358_);
lean_dec(v_b_6323_);
v___x_6360_ = lean_box(0);
v_isShared_6361_ = v_isSharedCheck_6465_;
goto v_resetjp_6359_;
}
v_resetjp_6359_:
{
lean_object* v_fst_6362_; lean_object* v___x_6364_; uint8_t v_isShared_6365_; uint8_t v_isSharedCheck_6463_; 
v_fst_6362_ = lean_ctor_get(v_snd_6355_, 0);
v_isSharedCheck_6463_ = !lean_is_exclusive(v_snd_6355_);
if (v_isSharedCheck_6463_ == 0)
{
lean_object* v_unused_6464_; 
v_unused_6464_ = lean_ctor_get(v_snd_6355_, 1);
lean_dec(v_unused_6464_);
v___x_6364_ = v_snd_6355_;
v_isShared_6365_ = v_isSharedCheck_6463_;
goto v_resetjp_6363_;
}
else
{
lean_inc(v_fst_6362_);
lean_dec(v_snd_6355_);
v___x_6364_ = lean_box(0);
v_isShared_6365_ = v_isSharedCheck_6463_;
goto v_resetjp_6363_;
}
v_resetjp_6363_:
{
lean_object* v_fst_6366_; lean_object* v___x_6368_; uint8_t v_isShared_6369_; uint8_t v_isSharedCheck_6461_; 
v_fst_6366_ = lean_ctor_get(v_snd_6356_, 0);
v_isSharedCheck_6461_ = !lean_is_exclusive(v_snd_6356_);
if (v_isSharedCheck_6461_ == 0)
{
lean_object* v_unused_6462_; 
v_unused_6462_ = lean_ctor_get(v_snd_6356_, 1);
lean_dec(v_unused_6462_);
v___x_6368_ = v_snd_6356_;
v_isShared_6369_ = v_isSharedCheck_6461_;
goto v_resetjp_6367_;
}
else
{
lean_inc(v_fst_6366_);
lean_dec(v_snd_6356_);
v___x_6368_ = lean_box(0);
v_isShared_6369_ = v_isSharedCheck_6461_;
goto v_resetjp_6367_;
}
v_resetjp_6367_:
{
lean_object* v_array_6370_; lean_object* v_start_6371_; lean_object* v_stop_6372_; uint8_t v___x_6373_; 
v_array_6370_ = lean_ctor_get(v_snd_6357_, 0);
v_start_6371_ = lean_ctor_get(v_snd_6357_, 1);
v_stop_6372_ = lean_ctor_get(v_snd_6357_, 2);
v___x_6373_ = lean_nat_dec_lt(v_start_6371_, v_stop_6372_);
if (v___x_6373_ == 0)
{
lean_object* v___x_6375_; 
if (v_isShared_6369_ == 0)
{
v___x_6375_ = v___x_6368_;
goto v_reusejp_6374_;
}
else
{
lean_object* v_reuseFailAlloc_6384_; 
v_reuseFailAlloc_6384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6384_, 0, v_fst_6366_);
lean_ctor_set(v_reuseFailAlloc_6384_, 1, v_snd_6357_);
v___x_6375_ = v_reuseFailAlloc_6384_;
goto v_reusejp_6374_;
}
v_reusejp_6374_:
{
lean_object* v___x_6377_; 
if (v_isShared_6365_ == 0)
{
lean_ctor_set(v___x_6364_, 1, v___x_6375_);
v___x_6377_ = v___x_6364_;
goto v_reusejp_6376_;
}
else
{
lean_object* v_reuseFailAlloc_6383_; 
v_reuseFailAlloc_6383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_fst_6362_);
lean_ctor_set(v_reuseFailAlloc_6383_, 1, v___x_6375_);
v___x_6377_ = v_reuseFailAlloc_6383_;
goto v_reusejp_6376_;
}
v_reusejp_6376_:
{
lean_object* v___x_6379_; 
if (v_isShared_6361_ == 0)
{
lean_ctor_set(v___x_6360_, 1, v___x_6377_);
v___x_6379_ = v___x_6360_;
goto v_reusejp_6378_;
}
else
{
lean_object* v_reuseFailAlloc_6382_; 
v_reuseFailAlloc_6382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_fst_6358_);
lean_ctor_set(v_reuseFailAlloc_6382_, 1, v___x_6377_);
v___x_6379_ = v_reuseFailAlloc_6382_;
goto v_reusejp_6378_;
}
v_reusejp_6378_:
{
lean_object* v___x_6380_; lean_object* v___f_6381_; 
v___x_6380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6380_, 0, v___x_6379_);
v___f_6381_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6381_, 0, v___x_6380_);
v___y_6330_ = v___f_6381_;
goto v___jp_6329_;
}
}
}
}
else
{
lean_object* v___x_6386_; uint8_t v_isShared_6387_; uint8_t v_isSharedCheck_6457_; 
lean_inc(v_stop_6372_);
lean_inc(v_start_6371_);
lean_inc_ref(v_array_6370_);
v_isSharedCheck_6457_ = !lean_is_exclusive(v_snd_6357_);
if (v_isSharedCheck_6457_ == 0)
{
lean_object* v_unused_6458_; lean_object* v_unused_6459_; lean_object* v_unused_6460_; 
v_unused_6458_ = lean_ctor_get(v_snd_6357_, 2);
lean_dec(v_unused_6458_);
v_unused_6459_ = lean_ctor_get(v_snd_6357_, 1);
lean_dec(v_unused_6459_);
v_unused_6460_ = lean_ctor_get(v_snd_6357_, 0);
lean_dec(v_unused_6460_);
v___x_6386_ = v_snd_6357_;
v_isShared_6387_ = v_isSharedCheck_6457_;
goto v_resetjp_6385_;
}
else
{
lean_dec(v_snd_6357_);
v___x_6386_ = lean_box(0);
v_isShared_6387_ = v_isSharedCheck_6457_;
goto v_resetjp_6385_;
}
v_resetjp_6385_:
{
lean_object* v_array_6388_; lean_object* v_start_6389_; lean_object* v_stop_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6395_; 
v_array_6388_ = lean_ctor_get(v_fst_6366_, 0);
v_start_6389_ = lean_ctor_get(v_fst_6366_, 1);
v_stop_6390_ = lean_ctor_get(v_fst_6366_, 2);
v___x_6391_ = lean_array_fget(v_array_6370_, v_start_6371_);
v___x_6392_ = lean_unsigned_to_nat(1u);
v___x_6393_ = lean_nat_add(v_start_6371_, v___x_6392_);
lean_dec(v_start_6371_);
if (v_isShared_6387_ == 0)
{
lean_ctor_set(v___x_6386_, 1, v___x_6393_);
v___x_6395_ = v___x_6386_;
goto v_reusejp_6394_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_array_6370_);
lean_ctor_set(v_reuseFailAlloc_6456_, 1, v___x_6393_);
lean_ctor_set(v_reuseFailAlloc_6456_, 2, v_stop_6372_);
v___x_6395_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6394_;
}
v_reusejp_6394_:
{
uint8_t v___x_6396_; 
v___x_6396_ = lean_nat_dec_lt(v_start_6389_, v_stop_6390_);
if (v___x_6396_ == 0)
{
lean_object* v___x_6398_; 
lean_dec(v___x_6391_);
if (v_isShared_6369_ == 0)
{
lean_ctor_set(v___x_6368_, 1, v___x_6395_);
v___x_6398_ = v___x_6368_;
goto v_reusejp_6397_;
}
else
{
lean_object* v_reuseFailAlloc_6407_; 
v_reuseFailAlloc_6407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6407_, 0, v_fst_6366_);
lean_ctor_set(v_reuseFailAlloc_6407_, 1, v___x_6395_);
v___x_6398_ = v_reuseFailAlloc_6407_;
goto v_reusejp_6397_;
}
v_reusejp_6397_:
{
lean_object* v___x_6400_; 
if (v_isShared_6365_ == 0)
{
lean_ctor_set(v___x_6364_, 1, v___x_6398_);
v___x_6400_ = v___x_6364_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6406_; 
v_reuseFailAlloc_6406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6406_, 0, v_fst_6362_);
lean_ctor_set(v_reuseFailAlloc_6406_, 1, v___x_6398_);
v___x_6400_ = v_reuseFailAlloc_6406_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
lean_object* v___x_6402_; 
if (v_isShared_6361_ == 0)
{
lean_ctor_set(v___x_6360_, 1, v___x_6400_);
v___x_6402_ = v___x_6360_;
goto v_reusejp_6401_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v_fst_6358_);
lean_ctor_set(v_reuseFailAlloc_6405_, 1, v___x_6400_);
v___x_6402_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6401_;
}
v_reusejp_6401_:
{
lean_object* v___x_6403_; lean_object* v___f_6404_; 
v___x_6403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6403_, 0, v___x_6402_);
v___f_6404_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6404_, 0, v___x_6403_);
v___y_6330_ = v___f_6404_;
goto v___jp_6329_;
}
}
}
}
else
{
lean_object* v___x_6409_; uint8_t v_isShared_6410_; uint8_t v_isSharedCheck_6452_; 
lean_inc(v_stop_6390_);
lean_inc(v_start_6389_);
lean_inc_ref(v_array_6388_);
v_isSharedCheck_6452_ = !lean_is_exclusive(v_fst_6366_);
if (v_isSharedCheck_6452_ == 0)
{
lean_object* v_unused_6453_; lean_object* v_unused_6454_; lean_object* v_unused_6455_; 
v_unused_6453_ = lean_ctor_get(v_fst_6366_, 2);
lean_dec(v_unused_6453_);
v_unused_6454_ = lean_ctor_get(v_fst_6366_, 1);
lean_dec(v_unused_6454_);
v_unused_6455_ = lean_ctor_get(v_fst_6366_, 0);
lean_dec(v_unused_6455_);
v___x_6409_ = v_fst_6366_;
v_isShared_6410_ = v_isSharedCheck_6452_;
goto v_resetjp_6408_;
}
else
{
lean_dec(v_fst_6366_);
v___x_6409_ = lean_box(0);
v_isShared_6410_ = v_isSharedCheck_6452_;
goto v_resetjp_6408_;
}
v_resetjp_6408_:
{
lean_object* v_array_6411_; lean_object* v_start_6412_; lean_object* v_stop_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6417_; 
v_array_6411_ = lean_ctor_get(v_fst_6362_, 0);
v_start_6412_ = lean_ctor_get(v_fst_6362_, 1);
v_stop_6413_ = lean_ctor_get(v_fst_6362_, 2);
v___x_6414_ = lean_array_fget(v_array_6388_, v_start_6389_);
v___x_6415_ = lean_nat_add(v_start_6389_, v___x_6392_);
lean_dec(v_start_6389_);
if (v_isShared_6410_ == 0)
{
lean_ctor_set(v___x_6409_, 1, v___x_6415_);
v___x_6417_ = v___x_6409_;
goto v_reusejp_6416_;
}
else
{
lean_object* v_reuseFailAlloc_6451_; 
v_reuseFailAlloc_6451_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6451_, 0, v_array_6388_);
lean_ctor_set(v_reuseFailAlloc_6451_, 1, v___x_6415_);
lean_ctor_set(v_reuseFailAlloc_6451_, 2, v_stop_6390_);
v___x_6417_ = v_reuseFailAlloc_6451_;
goto v_reusejp_6416_;
}
v_reusejp_6416_:
{
uint8_t v___x_6418_; 
v___x_6418_ = lean_nat_dec_lt(v_start_6412_, v_stop_6413_);
if (v___x_6418_ == 0)
{
lean_object* v___x_6420_; 
lean_dec(v___x_6414_);
lean_dec(v___x_6391_);
if (v_isShared_6369_ == 0)
{
lean_ctor_set(v___x_6368_, 1, v___x_6395_);
lean_ctor_set(v___x_6368_, 0, v___x_6417_);
v___x_6420_ = v___x_6368_;
goto v_reusejp_6419_;
}
else
{
lean_object* v_reuseFailAlloc_6429_; 
v_reuseFailAlloc_6429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6429_, 0, v___x_6417_);
lean_ctor_set(v_reuseFailAlloc_6429_, 1, v___x_6395_);
v___x_6420_ = v_reuseFailAlloc_6429_;
goto v_reusejp_6419_;
}
v_reusejp_6419_:
{
lean_object* v___x_6422_; 
if (v_isShared_6365_ == 0)
{
lean_ctor_set(v___x_6364_, 1, v___x_6420_);
v___x_6422_ = v___x_6364_;
goto v_reusejp_6421_;
}
else
{
lean_object* v_reuseFailAlloc_6428_; 
v_reuseFailAlloc_6428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6428_, 0, v_fst_6362_);
lean_ctor_set(v_reuseFailAlloc_6428_, 1, v___x_6420_);
v___x_6422_ = v_reuseFailAlloc_6428_;
goto v_reusejp_6421_;
}
v_reusejp_6421_:
{
lean_object* v___x_6424_; 
if (v_isShared_6361_ == 0)
{
lean_ctor_set(v___x_6360_, 1, v___x_6422_);
v___x_6424_ = v___x_6360_;
goto v_reusejp_6423_;
}
else
{
lean_object* v_reuseFailAlloc_6427_; 
v_reuseFailAlloc_6427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6427_, 0, v_fst_6358_);
lean_ctor_set(v_reuseFailAlloc_6427_, 1, v___x_6422_);
v___x_6424_ = v_reuseFailAlloc_6427_;
goto v_reusejp_6423_;
}
v_reusejp_6423_:
{
lean_object* v___x_6425_; lean_object* v___f_6426_; 
v___x_6425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6425_, 0, v___x_6424_);
v___f_6426_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6426_, 0, v___x_6425_);
v___y_6330_ = v___f_6426_;
goto v___jp_6329_;
}
}
}
}
else
{
lean_object* v___x_6431_; uint8_t v_isShared_6432_; uint8_t v_isSharedCheck_6447_; 
lean_inc(v_stop_6413_);
lean_inc(v_start_6412_);
lean_inc_ref(v_array_6411_);
lean_del_object(v___x_6368_);
lean_del_object(v___x_6364_);
lean_del_object(v___x_6360_);
v_isSharedCheck_6447_ = !lean_is_exclusive(v_fst_6362_);
if (v_isSharedCheck_6447_ == 0)
{
lean_object* v_unused_6448_; lean_object* v_unused_6449_; lean_object* v_unused_6450_; 
v_unused_6448_ = lean_ctor_get(v_fst_6362_, 2);
lean_dec(v_unused_6448_);
v_unused_6449_ = lean_ctor_get(v_fst_6362_, 1);
lean_dec(v_unused_6449_);
v_unused_6450_ = lean_ctor_get(v_fst_6362_, 0);
lean_dec(v_unused_6450_);
v___x_6431_ = v_fst_6362_;
v_isShared_6432_ = v_isSharedCheck_6447_;
goto v_resetjp_6430_;
}
else
{
lean_dec(v_fst_6362_);
v___x_6431_ = lean_box(0);
v_isShared_6432_ = v_isSharedCheck_6447_;
goto v_resetjp_6430_;
}
v_resetjp_6430_:
{
lean_object* v___f_6433_; uint8_t v___x_6434_; lean_object* v_remaining_x27_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___f_6439_; lean_object* v___x_6440_; lean_object* v___x_6442_; 
v___f_6433_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6434_ = 0;
v_remaining_x27_6435_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6436_ = lean_array_fget_borrowed(v_array_6411_, v_start_6412_);
v___x_6437_ = lean_box(v___x_6434_);
v___x_6438_ = lean_box(v___x_6418_);
lean_inc(v_extraEqualities_6321_);
lean_inc(v_a_6322_);
lean_inc_ref(v_onAlt_6320_);
lean_inc(v___x_6436_);
v___f_6439_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6439_, 0, v___x_6436_);
lean_closure_set(v___f_6439_, 1, v_remaining_x27_6435_);
lean_closure_set(v___f_6439_, 2, v_onAlt_6320_);
lean_closure_set(v___f_6439_, 3, v_a_6322_);
lean_closure_set(v___f_6439_, 4, v___x_6437_);
lean_closure_set(v___f_6439_, 5, v___x_6438_);
lean_closure_set(v___f_6439_, 6, v___f_6433_);
lean_closure_set(v___f_6439_, 7, v_extraEqualities_6321_);
v___x_6440_ = lean_nat_add(v_start_6412_, v___x_6392_);
lean_dec(v_start_6412_);
if (v_isShared_6432_ == 0)
{
lean_ctor_set(v___x_6431_, 1, v___x_6440_);
v___x_6442_ = v___x_6431_;
goto v_reusejp_6441_;
}
else
{
lean_object* v_reuseFailAlloc_6446_; 
v_reuseFailAlloc_6446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_array_6411_);
lean_ctor_set(v_reuseFailAlloc_6446_, 1, v___x_6440_);
lean_ctor_set(v_reuseFailAlloc_6446_, 2, v_stop_6413_);
v___x_6442_ = v_reuseFailAlloc_6446_;
goto v_reusejp_6441_;
}
v_reusejp_6441_:
{
lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___f_6445_; 
v___x_6443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6443_, 0, v___x_6414_);
v___x_6444_ = lean_box(v___x_6434_);
v___f_6445_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6445_, 0, v___x_6391_);
lean_closure_set(v___f_6445_, 1, v___x_6443_);
lean_closure_set(v___f_6445_, 2, v___f_6439_);
lean_closure_set(v___f_6445_, 3, v___x_6444_);
lean_closure_set(v___f_6445_, 4, v_fst_6358_);
lean_closure_set(v___f_6445_, 5, v___x_6417_);
lean_closure_set(v___f_6445_, 6, v___x_6395_);
lean_closure_set(v___f_6445_, 7, v___x_6442_);
v___y_6330_ = v___f_6445_;
goto v___jp_6329_;
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
v___jp_6329_:
{
lean_object* v___x_6331_; 
lean_inc(v___y_6327_);
lean_inc_ref(v___y_6326_);
lean_inc(v___y_6325_);
lean_inc_ref(v___y_6324_);
v___x_6331_ = lean_apply_5(v___y_6330_, v___y_6324_, v___y_6325_, v___y_6326_, v___y_6327_, lean_box(0));
if (lean_obj_tag(v___x_6331_) == 0)
{
lean_object* v_a_6332_; lean_object* v___x_6334_; uint8_t v_isShared_6335_; uint8_t v_isSharedCheck_6344_; 
v_a_6332_ = lean_ctor_get(v___x_6331_, 0);
v_isSharedCheck_6344_ = !lean_is_exclusive(v___x_6331_);
if (v_isSharedCheck_6344_ == 0)
{
v___x_6334_ = v___x_6331_;
v_isShared_6335_ = v_isSharedCheck_6344_;
goto v_resetjp_6333_;
}
else
{
lean_inc(v_a_6332_);
lean_dec(v___x_6331_);
v___x_6334_ = lean_box(0);
v_isShared_6335_ = v_isSharedCheck_6344_;
goto v_resetjp_6333_;
}
v_resetjp_6333_:
{
if (lean_obj_tag(v_a_6332_) == 0)
{
lean_object* v_a_6336_; lean_object* v___x_6338_; 
lean_dec(v_a_6322_);
lean_dec(v_extraEqualities_6321_);
lean_dec_ref(v_onAlt_6320_);
v_a_6336_ = lean_ctor_get(v_a_6332_, 0);
lean_inc(v_a_6336_);
lean_dec_ref_known(v_a_6332_, 1);
if (v_isShared_6335_ == 0)
{
lean_ctor_set(v___x_6334_, 0, v_a_6336_);
v___x_6338_ = v___x_6334_;
goto v_reusejp_6337_;
}
else
{
lean_object* v_reuseFailAlloc_6339_; 
v_reuseFailAlloc_6339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6336_);
v___x_6338_ = v_reuseFailAlloc_6339_;
goto v_reusejp_6337_;
}
v_reusejp_6337_:
{
return v___x_6338_;
}
}
else
{
lean_object* v_a_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; 
lean_del_object(v___x_6334_);
v_a_6340_ = lean_ctor_get(v_a_6332_, 0);
lean_inc(v_a_6340_);
lean_dec_ref_known(v_a_6332_, 1);
v___x_6341_ = lean_unsigned_to_nat(1u);
v___x_6342_ = lean_nat_add(v_a_6322_, v___x_6341_);
lean_dec(v_a_6322_);
v_a_6322_ = v___x_6342_;
v_b_6323_ = v_a_6340_;
goto _start;
}
}
}
else
{
lean_object* v_a_6345_; lean_object* v___x_6347_; uint8_t v_isShared_6348_; uint8_t v_isSharedCheck_6352_; 
lean_dec(v_a_6322_);
lean_dec(v_extraEqualities_6321_);
lean_dec_ref(v_onAlt_6320_);
v_a_6345_ = lean_ctor_get(v___x_6331_, 0);
v_isSharedCheck_6352_ = !lean_is_exclusive(v___x_6331_);
if (v_isSharedCheck_6352_ == 0)
{
v___x_6347_ = v___x_6331_;
v_isShared_6348_ = v_isSharedCheck_6352_;
goto v_resetjp_6346_;
}
else
{
lean_inc(v_a_6345_);
lean_dec(v___x_6331_);
v___x_6347_ = lean_box(0);
v_isShared_6348_ = v_isSharedCheck_6352_;
goto v_resetjp_6346_;
}
v_resetjp_6346_:
{
lean_object* v___x_6350_; 
if (v_isShared_6348_ == 0)
{
v___x_6350_ = v___x_6347_;
goto v_reusejp_6349_;
}
else
{
lean_object* v_reuseFailAlloc_6351_; 
v_reuseFailAlloc_6351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6351_, 0, v_a_6345_);
v___x_6350_ = v_reuseFailAlloc_6351_;
goto v_reusejp_6349_;
}
v_reusejp_6349_:
{
return v___x_6350_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6467_, lean_object* v_onAlt_6468_, lean_object* v_extraEqualities_6469_, lean_object* v_a_6470_, lean_object* v_b_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_, lean_object* v___y_6474_, lean_object* v___y_6475_, lean_object* v___y_6476_){
_start:
{
lean_object* v_res_6477_; 
v_res_6477_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6467_, v_onAlt_6468_, v_extraEqualities_6469_, v_a_6470_, v_b_6471_, v___y_6472_, v___y_6473_, v___y_6474_, v___y_6475_);
lean_dec(v___y_6475_);
lean_dec_ref(v___y_6474_);
lean_dec(v___y_6473_);
lean_dec_ref(v___y_6472_);
lean_dec(v_upperBound_6467_);
return v_res_6477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6478_, size_t v_sz_6479_, size_t v_i_6480_, lean_object* v_bs_6481_, lean_object* v___y_6482_, lean_object* v___y_6483_, lean_object* v___y_6484_, lean_object* v___y_6485_){
_start:
{
uint8_t v___x_6487_; 
v___x_6487_ = lean_usize_dec_lt(v_i_6480_, v_sz_6479_);
if (v___x_6487_ == 0)
{
lean_object* v___x_6488_; 
lean_dec_ref(v_onParams_6478_);
v___x_6488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6488_, 0, v_bs_6481_);
return v___x_6488_;
}
else
{
lean_object* v_v_6489_; lean_object* v___x_6490_; lean_object* v_bs_x27_6491_; lean_object* v___x_6492_; 
v_v_6489_ = lean_array_uget(v_bs_6481_, v_i_6480_);
v___x_6490_ = lean_unsigned_to_nat(0u);
v_bs_x27_6491_ = lean_array_uset(v_bs_6481_, v_i_6480_, v___x_6490_);
lean_inc_ref(v_onParams_6478_);
lean_inc(v___y_6485_);
lean_inc_ref(v___y_6484_);
lean_inc(v___y_6483_);
lean_inc_ref(v___y_6482_);
v___x_6492_ = lean_apply_6(v_onParams_6478_, v_v_6489_, v___y_6482_, v___y_6483_, v___y_6484_, v___y_6485_, lean_box(0));
if (lean_obj_tag(v___x_6492_) == 0)
{
lean_object* v_a_6493_; size_t v___x_6494_; size_t v___x_6495_; lean_object* v___x_6496_; 
v_a_6493_ = lean_ctor_get(v___x_6492_, 0);
lean_inc(v_a_6493_);
lean_dec_ref_known(v___x_6492_, 1);
v___x_6494_ = ((size_t)1ULL);
v___x_6495_ = lean_usize_add(v_i_6480_, v___x_6494_);
v___x_6496_ = lean_array_uset(v_bs_x27_6491_, v_i_6480_, v_a_6493_);
v_i_6480_ = v___x_6495_;
v_bs_6481_ = v___x_6496_;
goto _start;
}
else
{
lean_object* v_a_6498_; lean_object* v___x_6500_; uint8_t v_isShared_6501_; uint8_t v_isSharedCheck_6505_; 
lean_dec_ref(v_bs_x27_6491_);
lean_dec_ref(v_onParams_6478_);
v_a_6498_ = lean_ctor_get(v___x_6492_, 0);
v_isSharedCheck_6505_ = !lean_is_exclusive(v___x_6492_);
if (v_isSharedCheck_6505_ == 0)
{
v___x_6500_ = v___x_6492_;
v_isShared_6501_ = v_isSharedCheck_6505_;
goto v_resetjp_6499_;
}
else
{
lean_inc(v_a_6498_);
lean_dec(v___x_6492_);
v___x_6500_ = lean_box(0);
v_isShared_6501_ = v_isSharedCheck_6505_;
goto v_resetjp_6499_;
}
v_resetjp_6499_:
{
lean_object* v___x_6503_; 
if (v_isShared_6501_ == 0)
{
v___x_6503_ = v___x_6500_;
goto v_reusejp_6502_;
}
else
{
lean_object* v_reuseFailAlloc_6504_; 
v_reuseFailAlloc_6504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6504_, 0, v_a_6498_);
v___x_6503_ = v_reuseFailAlloc_6504_;
goto v_reusejp_6502_;
}
v_reusejp_6502_:
{
return v___x_6503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6506_, lean_object* v_sz_6507_, lean_object* v_i_6508_, lean_object* v_bs_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_){
_start:
{
size_t v_sz_boxed_6515_; size_t v_i_boxed_6516_; lean_object* v_res_6517_; 
v_sz_boxed_6515_ = lean_unbox_usize(v_sz_6507_);
lean_dec(v_sz_6507_);
v_i_boxed_6516_ = lean_unbox_usize(v_i_6508_);
lean_dec(v_i_6508_);
v_res_6517_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6506_, v_sz_boxed_6515_, v_i_boxed_6516_, v_bs_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_);
lean_dec(v___y_6513_);
lean_dec_ref(v___y_6512_);
lean_dec(v___y_6511_);
lean_dec_ref(v___y_6510_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6518_, lean_object* v___y_6519_){
_start:
{
lean_object* v___x_6521_; lean_object* v_env_6522_; lean_object* v___x_6523_; lean_object* v___x_6524_; 
v___x_6521_ = lean_st_ref_get(v___y_6519_);
v_env_6522_ = lean_ctor_get(v___x_6521_, 0);
lean_inc_ref(v_env_6522_);
lean_dec(v___x_6521_);
v___x_6523_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6522_, v_declName_6518_);
v___x_6524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6524_, 0, v___x_6523_);
return v___x_6524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_){
_start:
{
lean_object* v_res_6528_; 
v_res_6528_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6525_, v___y_6526_);
lean_dec(v___y_6526_);
return v_res_6528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6531_, uint8_t v_useSplitter_6532_, uint8_t v_addEqualities_6533_, lean_object* v_onParams_6534_, lean_object* v_onMotive_6535_, lean_object* v_onAlt_6536_, lean_object* v_onRemaining_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_){
_start:
{
lean_object* v___x_6543_; lean_object* v_env_6544_; lean_object* v_toMatcherInfo_6545_; lean_object* v_matcherName_6546_; lean_object* v_matcherLevels_6547_; lean_object* v_params_6548_; lean_object* v_motive_6549_; lean_object* v_discrs_6550_; lean_object* v_alts_6551_; lean_object* v_remaining_6552_; lean_object* v___y_6554_; lean_object* v___y_6555_; lean_object* v___y_6556_; lean_object* v___y_6557_; lean_object* v___y_6558_; lean_object* v___y_6559_; lean_object* v___y_6560_; lean_object* v___y_6561_; lean_object* v___y_6562_; lean_object* v___y_6563_; lean_object* v___y_6564_; lean_object* v___y_6565_; lean_object* v___y_6566_; uint8_t v_isCasesOn_6651_; lean_object* v___y_6653_; size_t v___y_6654_; lean_object* v___y_6655_; lean_object* v___y_6656_; lean_object* v___y_6657_; lean_object* v___y_6658_; lean_object* v___y_6659_; lean_object* v_matcherLevels_6660_; lean_object* v___y_6661_; lean_object* v___y_6662_; lean_object* v___y_6663_; lean_object* v___y_6664_; lean_object* v_numDiscrEqs_6858_; lean_object* v___y_6859_; lean_object* v___y_6860_; lean_object* v___y_6861_; lean_object* v___y_6862_; 
v___x_6543_ = lean_st_ref_get(v___y_6541_);
v_env_6544_ = lean_ctor_get(v___x_6543_, 0);
lean_inc_ref(v_env_6544_);
lean_dec(v___x_6543_);
v_toMatcherInfo_6545_ = lean_ctor_get(v_matcherApp_6531_, 0);
lean_inc_ref(v_toMatcherInfo_6545_);
v_matcherName_6546_ = lean_ctor_get(v_matcherApp_6531_, 1);
lean_inc_n(v_matcherName_6546_, 2);
v_matcherLevels_6547_ = lean_ctor_get(v_matcherApp_6531_, 2);
v_params_6548_ = lean_ctor_get(v_matcherApp_6531_, 3);
v_motive_6549_ = lean_ctor_get(v_matcherApp_6531_, 4);
v_discrs_6550_ = lean_ctor_get(v_matcherApp_6531_, 5);
v_alts_6551_ = lean_ctor_get(v_matcherApp_6531_, 6);
lean_inc_ref(v_alts_6551_);
v_remaining_6552_ = lean_ctor_get(v_matcherApp_6531_, 7);
lean_inc_ref(v_remaining_6552_);
v_isCasesOn_6651_ = l_Lean_isCasesOnRecursor(v_env_6544_, v_matcherName_6546_);
if (v_isCasesOn_6651_ == 0)
{
lean_object* v___x_6912_; lean_object* v_a_6913_; 
lean_inc(v_matcherName_6546_);
v___x_6912_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6546_, v___y_6541_);
v_a_6913_ = lean_ctor_get(v___x_6912_, 0);
lean_inc(v_a_6913_);
lean_dec_ref(v___x_6912_);
if (lean_obj_tag(v_a_6913_) == 0)
{
lean_object* v___x_6914_; lean_object* v___x_6915_; lean_object* v___x_6916_; lean_object* v___x_6917_; lean_object* v___x_6918_; lean_object* v___x_6919_; lean_object* v_a_6920_; lean_object* v___x_6922_; uint8_t v_isShared_6923_; uint8_t v_isSharedCheck_6927_; 
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
lean_dec_ref(v_onMotive_6535_);
lean_dec_ref(v_onParams_6534_);
lean_dec_ref(v_matcherApp_6531_);
v___x_6914_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6915_ = l_Lean_MessageData_ofName(v_matcherName_6546_);
v___x_6916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6916_, 0, v___x_6914_);
lean_ctor_set(v___x_6916_, 1, v___x_6915_);
v___x_6917_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6918_, 0, v___x_6916_);
lean_ctor_set(v___x_6918_, 1, v___x_6917_);
v___x_6919_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6918_, v___y_6538_, v___y_6539_, v___y_6540_, v___y_6541_);
v_a_6920_ = lean_ctor_get(v___x_6919_, 0);
v_isSharedCheck_6927_ = !lean_is_exclusive(v___x_6919_);
if (v_isSharedCheck_6927_ == 0)
{
v___x_6922_ = v___x_6919_;
v_isShared_6923_ = v_isSharedCheck_6927_;
goto v_resetjp_6921_;
}
else
{
lean_inc(v_a_6920_);
lean_dec(v___x_6919_);
v___x_6922_ = lean_box(0);
v_isShared_6923_ = v_isSharedCheck_6927_;
goto v_resetjp_6921_;
}
v_resetjp_6921_:
{
lean_object* v___x_6925_; 
if (v_isShared_6923_ == 0)
{
v___x_6925_ = v___x_6922_;
goto v_reusejp_6924_;
}
else
{
lean_object* v_reuseFailAlloc_6926_; 
v_reuseFailAlloc_6926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6926_, 0, v_a_6920_);
v___x_6925_ = v_reuseFailAlloc_6926_;
goto v_reusejp_6924_;
}
v_reusejp_6924_:
{
return v___x_6925_;
}
}
}
else
{
lean_object* v_val_6928_; lean_object* v___x_6929_; 
v_val_6928_ = lean_ctor_get(v_a_6913_, 0);
lean_inc(v_val_6928_);
lean_dec_ref_known(v_a_6913_, 1);
v___x_6929_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6928_);
lean_dec(v_val_6928_);
v_numDiscrEqs_6858_ = v___x_6929_;
v___y_6859_ = v___y_6538_;
v___y_6860_ = v___y_6539_;
v___y_6861_ = v___y_6540_;
v___y_6862_ = v___y_6541_;
goto v___jp_6857_;
}
}
else
{
lean_object* v___x_6930_; 
v___x_6930_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6858_ = v___x_6930_;
v___y_6859_ = v___y_6538_;
v___y_6860_ = v___y_6539_;
v___y_6861_ = v___y_6540_;
v___y_6862_ = v___y_6541_;
goto v___jp_6857_;
}
v___jp_6553_:
{
lean_object* v___x_6567_; lean_object* v___x_6568_; lean_object* v_aux_6569_; lean_object* v_aux_6570_; lean_object* v_aux_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; lean_object* v___x_6574_; lean_object* v___f_6575_; uint8_t v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; 
lean_inc_ref(v___y_6558_);
v___x_6567_ = lean_array_to_list(v___y_6558_);
lean_inc(v_matcherName_6546_);
v___x_6568_ = l_Lean_mkConst(v_matcherName_6546_, v___x_6567_);
v_aux_6569_ = l_Lean_mkAppN(v___x_6568_, v___y_6564_);
lean_inc_ref(v___y_6566_);
v_aux_6570_ = l_Lean_Expr_app___override(v_aux_6569_, v___y_6566_);
v_aux_6571_ = l_Lean_mkAppN(v_aux_6570_, v___y_6563_);
v___x_6572_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6571_, 2);
v___x_6573_ = l_Lean_indentExpr(v_aux_6571_);
v___x_6574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6574_, 0, v___x_6572_);
lean_ctor_set(v___x_6574_, 1, v___x_6573_);
v___f_6575_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6575_, 0, v___x_6574_);
v___x_6576_ = 0;
v___x_6577_ = lean_box(v___x_6576_);
v___x_6578_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6578_, 0, v_aux_6571_);
lean_closure_set(v___x_6578_, 1, v___x_6577_);
v___x_6579_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6578_, v___f_6575_, v___y_6554_, v___y_6555_, v___y_6559_, v___y_6557_);
if (lean_obj_tag(v___x_6579_) == 0)
{
lean_object* v___x_6580_; lean_object* v___x_6581_; 
lean_dec_ref_known(v___x_6579_, 1);
v___x_6580_ = lean_array_get_size(v_alts_6551_);
v___x_6581_ = l_Lean_Meta_inferArgumentTypesN(v___x_6580_, v_aux_6571_, v___y_6554_, v___y_6555_, v___y_6559_, v___y_6557_);
if (lean_obj_tag(v___x_6581_) == 0)
{
lean_object* v_a_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; lean_object* v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; 
v_a_6582_ = lean_ctor_get(v___x_6581_, 0);
lean_inc(v_a_6582_);
lean_dec_ref_known(v___x_6581_, 1);
v___x_6583_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6531_);
v___x_6584_ = lean_array_get_size(v___x_6583_);
v___x_6585_ = lean_array_get_size(v_a_6582_);
lean_inc_n(v___y_6560_, 3);
v___x_6586_ = l_Array_toSubarray___redArg(v_alts_6551_, v___y_6560_, v___x_6580_);
v___x_6587_ = l_Array_toSubarray___redArg(v___x_6583_, v___y_6560_, v___x_6584_);
v___x_6588_ = l_Array_toSubarray___redArg(v_a_6582_, v___y_6560_, v___x_6585_);
v___x_6589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6589_, 0, v___x_6587_);
lean_ctor_set(v___x_6589_, 1, v___x_6588_);
v___x_6590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6590_, 0, v___x_6586_);
lean_ctor_set(v___x_6590_, 1, v___x_6589_);
lean_inc_ref(v___y_6561_);
v___x_6591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6591_, 0, v___y_6561_);
lean_ctor_set(v___x_6591_, 1, v___x_6590_);
v___x_6592_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6580_, v_onAlt_6536_, v___y_6556_, v___y_6560_, v___x_6591_, v___y_6554_, v___y_6555_, v___y_6559_, v___y_6557_);
if (lean_obj_tag(v___x_6592_) == 0)
{
lean_object* v_a_6593_; lean_object* v_fst_6594_; lean_object* v___x_6595_; 
v_a_6593_ = lean_ctor_get(v___x_6592_, 0);
lean_inc(v_a_6593_);
lean_dec_ref_known(v___x_6592_, 1);
v_fst_6594_ = lean_ctor_get(v_a_6593_, 0);
lean_inc(v_fst_6594_);
lean_dec(v_a_6593_);
lean_inc(v___y_6557_);
lean_inc_ref(v___y_6559_);
lean_inc(v___y_6555_);
lean_inc_ref(v___y_6554_);
v___x_6595_ = lean_apply_6(v_onRemaining_6537_, v_remaining_6552_, v___y_6554_, v___y_6555_, v___y_6559_, v___y_6557_, lean_box(0));
if (lean_obj_tag(v___x_6595_) == 0)
{
lean_object* v_a_6596_; lean_object* v___x_6598_; uint8_t v_isShared_6599_; uint8_t v_isSharedCheck_6618_; 
v_a_6596_ = lean_ctor_get(v___x_6595_, 0);
v_isSharedCheck_6618_ = !lean_is_exclusive(v___x_6595_);
if (v_isSharedCheck_6618_ == 0)
{
v___x_6598_ = v___x_6595_;
v_isShared_6599_ = v_isSharedCheck_6618_;
goto v_resetjp_6597_;
}
else
{
lean_inc(v_a_6596_);
lean_dec(v___x_6595_);
v___x_6598_ = lean_box(0);
v_isShared_6599_ = v_isSharedCheck_6618_;
goto v_resetjp_6597_;
}
v_resetjp_6597_:
{
lean_object* v_numParams_6600_; lean_object* v_numDiscrs_6601_; lean_object* v_altInfos_6602_; lean_object* v_uElimPos_x3f_6603_; lean_object* v_overlaps_6604_; lean_object* v___x_6606_; uint8_t v_isShared_6607_; uint8_t v_isSharedCheck_6616_; 
v_numParams_6600_ = lean_ctor_get(v_toMatcherInfo_6545_, 0);
v_numDiscrs_6601_ = lean_ctor_get(v_toMatcherInfo_6545_, 1);
v_altInfos_6602_ = lean_ctor_get(v_toMatcherInfo_6545_, 2);
v_uElimPos_x3f_6603_ = lean_ctor_get(v_toMatcherInfo_6545_, 3);
v_overlaps_6604_ = lean_ctor_get(v_toMatcherInfo_6545_, 5);
v_isSharedCheck_6616_ = !lean_is_exclusive(v_toMatcherInfo_6545_);
if (v_isSharedCheck_6616_ == 0)
{
lean_object* v_unused_6617_; 
v_unused_6617_ = lean_ctor_get(v_toMatcherInfo_6545_, 4);
lean_dec(v_unused_6617_);
v___x_6606_ = v_toMatcherInfo_6545_;
v_isShared_6607_ = v_isSharedCheck_6616_;
goto v_resetjp_6605_;
}
else
{
lean_inc(v_overlaps_6604_);
lean_inc(v_uElimPos_x3f_6603_);
lean_inc(v_altInfos_6602_);
lean_inc(v_numDiscrs_6601_);
lean_inc(v_numParams_6600_);
lean_dec(v_toMatcherInfo_6545_);
v___x_6606_ = lean_box(0);
v_isShared_6607_ = v_isSharedCheck_6616_;
goto v_resetjp_6605_;
}
v_resetjp_6605_:
{
lean_object* v_remaining_x27_6608_; lean_object* v___x_6610_; 
v_remaining_x27_6608_ = l_Array_append___redArg(v___y_6565_, v_a_6596_);
lean_dec(v_a_6596_);
if (v_isShared_6607_ == 0)
{
lean_ctor_set(v___x_6606_, 4, v___y_6562_);
v___x_6610_ = v___x_6606_;
goto v_reusejp_6609_;
}
else
{
lean_object* v_reuseFailAlloc_6615_; 
v_reuseFailAlloc_6615_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6615_, 0, v_numParams_6600_);
lean_ctor_set(v_reuseFailAlloc_6615_, 1, v_numDiscrs_6601_);
lean_ctor_set(v_reuseFailAlloc_6615_, 2, v_altInfos_6602_);
lean_ctor_set(v_reuseFailAlloc_6615_, 3, v_uElimPos_x3f_6603_);
lean_ctor_set(v_reuseFailAlloc_6615_, 4, v___y_6562_);
lean_ctor_set(v_reuseFailAlloc_6615_, 5, v_overlaps_6604_);
v___x_6610_ = v_reuseFailAlloc_6615_;
goto v_reusejp_6609_;
}
v_reusejp_6609_:
{
lean_object* v___x_6611_; lean_object* v___x_6613_; 
v___x_6611_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6611_, 0, v___x_6610_);
lean_ctor_set(v___x_6611_, 1, v_matcherName_6546_);
lean_ctor_set(v___x_6611_, 2, v___y_6558_);
lean_ctor_set(v___x_6611_, 3, v___y_6564_);
lean_ctor_set(v___x_6611_, 4, v___y_6566_);
lean_ctor_set(v___x_6611_, 5, v___y_6563_);
lean_ctor_set(v___x_6611_, 6, v_fst_6594_);
lean_ctor_set(v___x_6611_, 7, v_remaining_x27_6608_);
if (v_isShared_6599_ == 0)
{
lean_ctor_set(v___x_6598_, 0, v___x_6611_);
v___x_6613_ = v___x_6598_;
goto v_reusejp_6612_;
}
else
{
lean_object* v_reuseFailAlloc_6614_; 
v_reuseFailAlloc_6614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6614_, 0, v___x_6611_);
v___x_6613_ = v_reuseFailAlloc_6614_;
goto v_reusejp_6612_;
}
v_reusejp_6612_:
{
return v___x_6613_;
}
}
}
}
}
else
{
lean_object* v_a_6619_; lean_object* v___x_6621_; uint8_t v_isShared_6622_; uint8_t v_isSharedCheck_6626_; 
lean_dec(v_fst_6594_);
lean_dec_ref(v___y_6566_);
lean_dec(v___y_6565_);
lean_dec_ref(v___y_6564_);
lean_dec_ref(v___y_6563_);
lean_dec_ref(v___y_6562_);
lean_dec_ref(v___y_6558_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
v_a_6619_ = lean_ctor_get(v___x_6595_, 0);
v_isSharedCheck_6626_ = !lean_is_exclusive(v___x_6595_);
if (v_isSharedCheck_6626_ == 0)
{
v___x_6621_ = v___x_6595_;
v_isShared_6622_ = v_isSharedCheck_6626_;
goto v_resetjp_6620_;
}
else
{
lean_inc(v_a_6619_);
lean_dec(v___x_6595_);
v___x_6621_ = lean_box(0);
v_isShared_6622_ = v_isSharedCheck_6626_;
goto v_resetjp_6620_;
}
v_resetjp_6620_:
{
lean_object* v___x_6624_; 
if (v_isShared_6622_ == 0)
{
v___x_6624_ = v___x_6621_;
goto v_reusejp_6623_;
}
else
{
lean_object* v_reuseFailAlloc_6625_; 
v_reuseFailAlloc_6625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6625_, 0, v_a_6619_);
v___x_6624_ = v_reuseFailAlloc_6625_;
goto v_reusejp_6623_;
}
v_reusejp_6623_:
{
return v___x_6624_;
}
}
}
}
else
{
lean_object* v_a_6627_; lean_object* v___x_6629_; uint8_t v_isShared_6630_; uint8_t v_isSharedCheck_6634_; 
lean_dec_ref(v___y_6566_);
lean_dec(v___y_6565_);
lean_dec_ref(v___y_6564_);
lean_dec_ref(v___y_6563_);
lean_dec_ref(v___y_6562_);
lean_dec_ref(v___y_6558_);
lean_dec_ref(v_remaining_6552_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
v_a_6627_ = lean_ctor_get(v___x_6592_, 0);
v_isSharedCheck_6634_ = !lean_is_exclusive(v___x_6592_);
if (v_isSharedCheck_6634_ == 0)
{
v___x_6629_ = v___x_6592_;
v_isShared_6630_ = v_isSharedCheck_6634_;
goto v_resetjp_6628_;
}
else
{
lean_inc(v_a_6627_);
lean_dec(v___x_6592_);
v___x_6629_ = lean_box(0);
v_isShared_6630_ = v_isSharedCheck_6634_;
goto v_resetjp_6628_;
}
v_resetjp_6628_:
{
lean_object* v___x_6632_; 
if (v_isShared_6630_ == 0)
{
v___x_6632_ = v___x_6629_;
goto v_reusejp_6631_;
}
else
{
lean_object* v_reuseFailAlloc_6633_; 
v_reuseFailAlloc_6633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6633_, 0, v_a_6627_);
v___x_6632_ = v_reuseFailAlloc_6633_;
goto v_reusejp_6631_;
}
v_reusejp_6631_:
{
return v___x_6632_;
}
}
}
}
else
{
lean_object* v_a_6635_; lean_object* v___x_6637_; uint8_t v_isShared_6638_; uint8_t v_isSharedCheck_6642_; 
lean_dec_ref(v___y_6566_);
lean_dec(v___y_6565_);
lean_dec_ref(v___y_6564_);
lean_dec_ref(v___y_6563_);
lean_dec_ref(v___y_6562_);
lean_dec(v___y_6560_);
lean_dec_ref(v___y_6558_);
lean_dec(v___y_6556_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
lean_dec_ref(v_matcherApp_6531_);
v_a_6635_ = lean_ctor_get(v___x_6581_, 0);
v_isSharedCheck_6642_ = !lean_is_exclusive(v___x_6581_);
if (v_isSharedCheck_6642_ == 0)
{
v___x_6637_ = v___x_6581_;
v_isShared_6638_ = v_isSharedCheck_6642_;
goto v_resetjp_6636_;
}
else
{
lean_inc(v_a_6635_);
lean_dec(v___x_6581_);
v___x_6637_ = lean_box(0);
v_isShared_6638_ = v_isSharedCheck_6642_;
goto v_resetjp_6636_;
}
v_resetjp_6636_:
{
lean_object* v___x_6640_; 
if (v_isShared_6638_ == 0)
{
v___x_6640_ = v___x_6637_;
goto v_reusejp_6639_;
}
else
{
lean_object* v_reuseFailAlloc_6641_; 
v_reuseFailAlloc_6641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6641_, 0, v_a_6635_);
v___x_6640_ = v_reuseFailAlloc_6641_;
goto v_reusejp_6639_;
}
v_reusejp_6639_:
{
return v___x_6640_;
}
}
}
}
else
{
lean_object* v_a_6643_; lean_object* v___x_6645_; uint8_t v_isShared_6646_; uint8_t v_isSharedCheck_6650_; 
lean_dec_ref(v_aux_6571_);
lean_dec_ref(v___y_6566_);
lean_dec(v___y_6565_);
lean_dec_ref(v___y_6564_);
lean_dec_ref(v___y_6563_);
lean_dec_ref(v___y_6562_);
lean_dec(v___y_6560_);
lean_dec_ref(v___y_6558_);
lean_dec(v___y_6556_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
lean_dec_ref(v_matcherApp_6531_);
v_a_6643_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6650_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6650_ == 0)
{
v___x_6645_ = v___x_6579_;
v_isShared_6646_ = v_isSharedCheck_6650_;
goto v_resetjp_6644_;
}
else
{
lean_inc(v_a_6643_);
lean_dec(v___x_6579_);
v___x_6645_ = lean_box(0);
v_isShared_6646_ = v_isSharedCheck_6650_;
goto v_resetjp_6644_;
}
v_resetjp_6644_:
{
lean_object* v___x_6648_; 
if (v_isShared_6646_ == 0)
{
v___x_6648_ = v___x_6645_;
goto v_reusejp_6647_;
}
else
{
lean_object* v_reuseFailAlloc_6649_; 
v_reuseFailAlloc_6649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6649_, 0, v_a_6643_);
v___x_6648_ = v_reuseFailAlloc_6649_;
goto v_reusejp_6647_;
}
v_reusejp_6647_:
{
return v___x_6648_;
}
}
}
}
v___jp_6652_:
{
lean_object* v___x_6665_; lean_object* v_remaining_x27_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; size_t v_sz_6673_; lean_object* v___x_6674_; 
v___x_6665_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6666_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6667_ = l_Array_reverse___redArg(v___y_6659_);
v___x_6668_ = lean_array_get_size(v___x_6667_);
v___x_6669_ = l_Array_toSubarray___redArg(v___x_6667_, v___x_6665_, v___x_6668_);
lean_inc_ref(v___y_6655_);
v___x_6670_ = l_Array_reverse___redArg(v___y_6655_);
v___x_6671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6671_, 0, v___x_6665_);
lean_ctor_set(v___x_6671_, 1, v___x_6669_);
v___x_6672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6672_, 0, v_remaining_x27_6666_);
lean_ctor_set(v___x_6672_, 1, v___x_6671_);
v_sz_6673_ = lean_array_size(v___x_6670_);
v___x_6674_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6670_, v_sz_6673_, v___y_6654_, v___x_6672_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_);
lean_dec_ref(v___x_6670_);
if (lean_obj_tag(v___x_6674_) == 0)
{
lean_object* v_a_6675_; lean_object* v_snd_6676_; 
v_a_6675_ = lean_ctor_get(v___x_6674_, 0);
lean_inc(v_a_6675_);
lean_dec_ref_known(v___x_6674_, 1);
v_snd_6676_ = lean_ctor_get(v_a_6675_, 1);
lean_inc(v_snd_6676_);
if (v_useSplitter_6532_ == 0)
{
lean_object* v_fst_6677_; lean_object* v_fst_6678_; 
lean_dec(v___y_6657_);
v_fst_6677_ = lean_ctor_get(v_a_6675_, 0);
lean_inc(v_fst_6677_);
lean_dec(v_a_6675_);
v_fst_6678_ = lean_ctor_get(v_snd_6676_, 0);
lean_inc(v_fst_6678_);
lean_dec(v_snd_6676_);
v___y_6554_ = v___y_6661_;
v___y_6555_ = v___y_6662_;
v___y_6556_ = v_fst_6678_;
v___y_6557_ = v___y_6664_;
v___y_6558_ = v_matcherLevels_6660_;
v___y_6559_ = v___y_6663_;
v___y_6560_ = v___x_6665_;
v___y_6561_ = v_remaining_x27_6666_;
v___y_6562_ = v___y_6653_;
v___y_6563_ = v___y_6655_;
v___y_6564_ = v___y_6656_;
v___y_6565_ = v_fst_6677_;
v___y_6566_ = v___y_6658_;
goto v___jp_6553_;
}
else
{
if (v_isCasesOn_6651_ == 0)
{
lean_object* v___x_6680_; uint8_t v_isShared_6681_; uint8_t v_isSharedCheck_6838_; 
v_isSharedCheck_6838_ = !lean_is_exclusive(v_matcherApp_6531_);
if (v_isSharedCheck_6838_ == 0)
{
lean_object* v_unused_6839_; lean_object* v_unused_6840_; lean_object* v_unused_6841_; lean_object* v_unused_6842_; lean_object* v_unused_6843_; lean_object* v_unused_6844_; lean_object* v_unused_6845_; lean_object* v_unused_6846_; 
v_unused_6839_ = lean_ctor_get(v_matcherApp_6531_, 7);
lean_dec(v_unused_6839_);
v_unused_6840_ = lean_ctor_get(v_matcherApp_6531_, 6);
lean_dec(v_unused_6840_);
v_unused_6841_ = lean_ctor_get(v_matcherApp_6531_, 5);
lean_dec(v_unused_6841_);
v_unused_6842_ = lean_ctor_get(v_matcherApp_6531_, 4);
lean_dec(v_unused_6842_);
v_unused_6843_ = lean_ctor_get(v_matcherApp_6531_, 3);
lean_dec(v_unused_6843_);
v_unused_6844_ = lean_ctor_get(v_matcherApp_6531_, 2);
lean_dec(v_unused_6844_);
v_unused_6845_ = lean_ctor_get(v_matcherApp_6531_, 1);
lean_dec(v_unused_6845_);
v_unused_6846_ = lean_ctor_get(v_matcherApp_6531_, 0);
lean_dec(v_unused_6846_);
v___x_6680_ = v_matcherApp_6531_;
v_isShared_6681_ = v_isSharedCheck_6838_;
goto v_resetjp_6679_;
}
else
{
lean_dec(v_matcherApp_6531_);
v___x_6680_ = lean_box(0);
v_isShared_6681_ = v_isSharedCheck_6838_;
goto v_resetjp_6679_;
}
v_resetjp_6679_:
{
lean_object* v_fst_6682_; lean_object* v___x_6684_; uint8_t v_isShared_6685_; uint8_t v_isSharedCheck_6836_; 
v_fst_6682_ = lean_ctor_get(v_a_6675_, 0);
v_isSharedCheck_6836_ = !lean_is_exclusive(v_a_6675_);
if (v_isSharedCheck_6836_ == 0)
{
lean_object* v_unused_6837_; 
v_unused_6837_ = lean_ctor_get(v_a_6675_, 1);
lean_dec(v_unused_6837_);
v___x_6684_ = v_a_6675_;
v_isShared_6685_ = v_isSharedCheck_6836_;
goto v_resetjp_6683_;
}
else
{
lean_inc(v_fst_6682_);
lean_dec(v_a_6675_);
v___x_6684_ = lean_box(0);
v_isShared_6685_ = v_isSharedCheck_6836_;
goto v_resetjp_6683_;
}
v_resetjp_6683_:
{
lean_object* v_fst_6686_; lean_object* v___x_6688_; uint8_t v_isShared_6689_; uint8_t v_isSharedCheck_6834_; 
v_fst_6686_ = lean_ctor_get(v_snd_6676_, 0);
v_isSharedCheck_6834_ = !lean_is_exclusive(v_snd_6676_);
if (v_isSharedCheck_6834_ == 0)
{
lean_object* v_unused_6835_; 
v_unused_6835_ = lean_ctor_get(v_snd_6676_, 1);
lean_dec(v_unused_6835_);
v___x_6688_ = v_snd_6676_;
v_isShared_6689_ = v_isSharedCheck_6834_;
goto v_resetjp_6687_;
}
else
{
lean_inc(v_fst_6686_);
lean_dec(v_snd_6676_);
v___x_6688_ = lean_box(0);
v_isShared_6689_ = v_isSharedCheck_6834_;
goto v_resetjp_6687_;
}
v_resetjp_6687_:
{
lean_object* v___x_6690_; lean_object* v___x_6691_; lean_object* v_aux1_6692_; lean_object* v_aux1_6693_; lean_object* v_aux1_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; lean_object* v___x_6697_; lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___f_6700_; uint8_t v___x_6701_; lean_object* v___x_6702_; lean_object* v___x_6703_; lean_object* v___x_6704_; 
lean_inc_ref(v_matcherLevels_6660_);
v___x_6690_ = lean_array_to_list(v_matcherLevels_6660_);
lean_inc(v___x_6690_);
lean_inc(v_matcherName_6546_);
v___x_6691_ = l_Lean_mkConst(v_matcherName_6546_, v___x_6690_);
v_aux1_6692_ = l_Lean_mkAppN(v___x_6691_, v___y_6656_);
lean_inc_ref(v___y_6658_);
v_aux1_6693_ = l_Lean_Expr_app___override(v_aux1_6692_, v___y_6658_);
v_aux1_6694_ = l_Lean_mkAppN(v_aux1_6693_, v___y_6655_);
v___x_6695_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6694_, 2);
v___x_6696_ = l_Lean_indentExpr(v_aux1_6694_);
v___x_6697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6697_, 0, v___x_6695_);
lean_ctor_set(v___x_6697_, 1, v___x_6696_);
v___x_6698_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6699_, 0, v___x_6697_);
lean_ctor_set(v___x_6699_, 1, v___x_6698_);
v___f_6700_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6700_, 0, v___x_6699_);
v___x_6701_ = 0;
v___x_6702_ = lean_box(v___x_6701_);
v___x_6703_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6703_, 0, v_aux1_6694_);
lean_closure_set(v___x_6703_, 1, v___x_6702_);
v___x_6704_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6703_, v___f_6700_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_);
if (lean_obj_tag(v___x_6704_) == 0)
{
lean_object* v___x_6705_; lean_object* v___x_6706_; 
lean_dec_ref_known(v___x_6704_, 1);
v___x_6705_ = lean_array_get_size(v_alts_6551_);
v___x_6706_ = l_Lean_Meta_inferArgumentTypesN(v___x_6705_, v_aux1_6694_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_);
if (lean_obj_tag(v___x_6706_) == 0)
{
lean_object* v_a_6707_; lean_object* v___x_6708_; 
v_a_6707_ = lean_ctor_get(v___x_6706_, 0);
lean_inc(v_a_6707_);
lean_dec_ref_known(v___x_6706_, 1);
lean_inc(v___y_6664_);
lean_inc_ref(v___y_6663_);
lean_inc(v___y_6662_);
lean_inc_ref(v___y_6661_);
v___x_6708_ = lean_get_match_equations_for(v_matcherName_6546_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_);
if (lean_obj_tag(v___x_6708_) == 0)
{
lean_object* v_a_6709_; lean_object* v_splitterName_6710_; lean_object* v_splitterMatchInfo_6711_; lean_object* v___x_6712_; lean_object* v_aux2_6713_; lean_object* v_aux2_6714_; lean_object* v_aux2_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; lean_object* v___f_6720_; lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; 
v_a_6709_ = lean_ctor_get(v___x_6708_, 0);
lean_inc(v_a_6709_);
lean_dec_ref_known(v___x_6708_, 1);
v_splitterName_6710_ = lean_ctor_get(v_a_6709_, 1);
lean_inc_n(v_splitterName_6710_, 2);
v_splitterMatchInfo_6711_ = lean_ctor_get(v_a_6709_, 2);
lean_inc_ref(v_splitterMatchInfo_6711_);
lean_dec(v_a_6709_);
v___x_6712_ = l_Lean_mkConst(v_splitterName_6710_, v___x_6690_);
v_aux2_6713_ = l_Lean_mkAppN(v___x_6712_, v___y_6656_);
lean_inc_ref(v___y_6658_);
v_aux2_6714_ = l_Lean_Expr_app___override(v_aux2_6713_, v___y_6658_);
v_aux2_6715_ = l_Lean_mkAppN(v_aux2_6714_, v___y_6655_);
v___x_6716_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6715_, 2);
v___x_6717_ = l_Lean_indentExpr(v_aux2_6715_);
v___x_6718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6718_, 0, v___x_6716_);
lean_ctor_set(v___x_6718_, 1, v___x_6717_);
v___x_6719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6719_, 0, v___x_6718_);
lean_ctor_set(v___x_6719_, 1, v___x_6698_);
v___f_6720_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6720_, 0, v___x_6719_);
v___x_6721_ = lean_box(v___x_6701_);
v___x_6722_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6722_, 0, v_aux2_6715_);
lean_closure_set(v___x_6722_, 1, v___x_6721_);
v___x_6723_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6722_, v___f_6720_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_);
if (lean_obj_tag(v___x_6723_) == 0)
{
lean_object* v___x_6724_; 
lean_dec_ref_known(v___x_6723_, 1);
v___x_6724_ = l_Lean_Meta_inferArgumentTypesN(v___x_6705_, v_aux2_6715_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_);
if (lean_obj_tag(v___x_6724_) == 0)
{
lean_object* v_a_6725_; lean_object* v_numParams_6726_; lean_object* v_numDiscrs_6727_; lean_object* v_altInfos_6728_; lean_object* v_uElimPos_x3f_6729_; lean_object* v_overlaps_6730_; lean_object* v_altInfos_6731_; lean_object* v___x_6733_; uint8_t v_isShared_6734_; uint8_t v_isSharedCheck_6788_; 
v_a_6725_ = lean_ctor_get(v___x_6724_, 0);
lean_inc(v_a_6725_);
lean_dec_ref_known(v___x_6724_, 1);
v_numParams_6726_ = lean_ctor_get(v_toMatcherInfo_6545_, 0);
lean_inc(v_numParams_6726_);
v_numDiscrs_6727_ = lean_ctor_get(v_toMatcherInfo_6545_, 1);
lean_inc(v_numDiscrs_6727_);
v_altInfos_6728_ = lean_ctor_get(v_toMatcherInfo_6545_, 2);
lean_inc_ref(v_altInfos_6728_);
v_uElimPos_x3f_6729_ = lean_ctor_get(v_toMatcherInfo_6545_, 3);
lean_inc(v_uElimPos_x3f_6729_);
v_overlaps_6730_ = lean_ctor_get(v_toMatcherInfo_6545_, 5);
lean_inc_ref(v_overlaps_6730_);
lean_dec_ref(v_toMatcherInfo_6545_);
v_altInfos_6731_ = lean_ctor_get(v_splitterMatchInfo_6711_, 2);
v_isSharedCheck_6788_ = !lean_is_exclusive(v_splitterMatchInfo_6711_);
if (v_isSharedCheck_6788_ == 0)
{
lean_object* v_unused_6789_; lean_object* v_unused_6790_; lean_object* v_unused_6791_; lean_object* v_unused_6792_; lean_object* v_unused_6793_; 
v_unused_6789_ = lean_ctor_get(v_splitterMatchInfo_6711_, 5);
lean_dec(v_unused_6789_);
v_unused_6790_ = lean_ctor_get(v_splitterMatchInfo_6711_, 4);
lean_dec(v_unused_6790_);
v_unused_6791_ = lean_ctor_get(v_splitterMatchInfo_6711_, 3);
lean_dec(v_unused_6791_);
v_unused_6792_ = lean_ctor_get(v_splitterMatchInfo_6711_, 1);
lean_dec(v_unused_6792_);
v_unused_6793_ = lean_ctor_get(v_splitterMatchInfo_6711_, 0);
lean_dec(v_unused_6793_);
v___x_6733_ = v_splitterMatchInfo_6711_;
v_isShared_6734_ = v_isSharedCheck_6788_;
goto v_resetjp_6732_;
}
else
{
lean_inc(v_altInfos_6731_);
lean_dec(v_splitterMatchInfo_6711_);
v___x_6733_ = lean_box(0);
v_isShared_6734_ = v_isSharedCheck_6788_;
goto v_resetjp_6732_;
}
v_resetjp_6732_:
{
lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6741_; lean_object* v___x_6742_; lean_object* v___x_6743_; lean_object* v___x_6745_; 
v___x_6735_ = lean_array_get_size(v_altInfos_6728_);
v___x_6736_ = lean_array_get_size(v_altInfos_6731_);
v___x_6737_ = lean_array_get_size(v_a_6707_);
v___x_6738_ = lean_array_get_size(v_a_6725_);
v___x_6739_ = l_Array_toSubarray___redArg(v_alts_6551_, v___x_6665_, v___x_6705_);
lean_inc_ref(v_altInfos_6728_);
v___x_6740_ = l_Array_toSubarray___redArg(v_altInfos_6728_, v___x_6665_, v___x_6735_);
v___x_6741_ = l_Array_toSubarray___redArg(v_altInfos_6731_, v___x_6665_, v___x_6736_);
v___x_6742_ = l_Array_toSubarray___redArg(v_a_6707_, v___x_6665_, v___x_6737_);
v___x_6743_ = l_Array_toSubarray___redArg(v_a_6725_, v___x_6665_, v___x_6738_);
if (v_isShared_6689_ == 0)
{
lean_ctor_set(v___x_6688_, 1, v___x_6743_);
lean_ctor_set(v___x_6688_, 0, v___x_6742_);
v___x_6745_ = v___x_6688_;
goto v_reusejp_6744_;
}
else
{
lean_object* v_reuseFailAlloc_6787_; 
v_reuseFailAlloc_6787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6787_, 0, v___x_6742_);
lean_ctor_set(v_reuseFailAlloc_6787_, 1, v___x_6743_);
v___x_6745_ = v_reuseFailAlloc_6787_;
goto v_reusejp_6744_;
}
v_reusejp_6744_:
{
lean_object* v___x_6747_; 
if (v_isShared_6685_ == 0)
{
lean_ctor_set(v___x_6684_, 1, v___x_6745_);
lean_ctor_set(v___x_6684_, 0, v___x_6741_);
v___x_6747_ = v___x_6684_;
goto v_reusejp_6746_;
}
else
{
lean_object* v_reuseFailAlloc_6786_; 
v_reuseFailAlloc_6786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6786_, 0, v___x_6741_);
lean_ctor_set(v_reuseFailAlloc_6786_, 1, v___x_6745_);
v___x_6747_ = v_reuseFailAlloc_6786_;
goto v_reusejp_6746_;
}
v_reusejp_6746_:
{
lean_object* v___x_6748_; lean_object* v___x_6749_; lean_object* v___x_6750_; lean_object* v___x_6751_; 
v___x_6748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6748_, 0, v___x_6740_);
lean_ctor_set(v___x_6748_, 1, v___x_6747_);
v___x_6749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6749_, 0, v___x_6739_);
lean_ctor_set(v___x_6749_, 1, v___x_6748_);
v___x_6750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6750_, 0, v_remaining_x27_6666_);
lean_ctor_set(v___x_6750_, 1, v___x_6749_);
v___x_6751_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6705_, v_onAlt_6536_, v_useSplitter_6532_, v_fst_6686_, v___y_6657_, v___x_6665_, v___x_6750_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_);
if (lean_obj_tag(v___x_6751_) == 0)
{
lean_object* v_a_6752_; lean_object* v_fst_6753_; lean_object* v___x_6754_; 
v_a_6752_ = lean_ctor_get(v___x_6751_, 0);
lean_inc(v_a_6752_);
lean_dec_ref_known(v___x_6751_, 1);
v_fst_6753_ = lean_ctor_get(v_a_6752_, 0);
lean_inc(v_fst_6753_);
lean_dec(v_a_6752_);
lean_inc(v___y_6664_);
lean_inc_ref(v___y_6663_);
lean_inc(v___y_6662_);
lean_inc_ref(v___y_6661_);
v___x_6754_ = lean_apply_6(v_onRemaining_6537_, v_remaining_6552_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_, lean_box(0));
if (lean_obj_tag(v___x_6754_) == 0)
{
lean_object* v_a_6755_; lean_object* v___x_6757_; uint8_t v_isShared_6758_; uint8_t v_isSharedCheck_6769_; 
v_a_6755_ = lean_ctor_get(v___x_6754_, 0);
v_isSharedCheck_6769_ = !lean_is_exclusive(v___x_6754_);
if (v_isSharedCheck_6769_ == 0)
{
v___x_6757_ = v___x_6754_;
v_isShared_6758_ = v_isSharedCheck_6769_;
goto v_resetjp_6756_;
}
else
{
lean_inc(v_a_6755_);
lean_dec(v___x_6754_);
v___x_6757_ = lean_box(0);
v_isShared_6758_ = v_isSharedCheck_6769_;
goto v_resetjp_6756_;
}
v_resetjp_6756_:
{
lean_object* v_remaining_x27_6759_; lean_object* v___x_6761_; 
v_remaining_x27_6759_ = l_Array_append___redArg(v_fst_6682_, v_a_6755_);
lean_dec(v_a_6755_);
if (v_isShared_6734_ == 0)
{
lean_ctor_set(v___x_6733_, 5, v_overlaps_6730_);
lean_ctor_set(v___x_6733_, 4, v___y_6653_);
lean_ctor_set(v___x_6733_, 3, v_uElimPos_x3f_6729_);
lean_ctor_set(v___x_6733_, 2, v_altInfos_6728_);
lean_ctor_set(v___x_6733_, 1, v_numDiscrs_6727_);
lean_ctor_set(v___x_6733_, 0, v_numParams_6726_);
v___x_6761_ = v___x_6733_;
goto v_reusejp_6760_;
}
else
{
lean_object* v_reuseFailAlloc_6768_; 
v_reuseFailAlloc_6768_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6768_, 0, v_numParams_6726_);
lean_ctor_set(v_reuseFailAlloc_6768_, 1, v_numDiscrs_6727_);
lean_ctor_set(v_reuseFailAlloc_6768_, 2, v_altInfos_6728_);
lean_ctor_set(v_reuseFailAlloc_6768_, 3, v_uElimPos_x3f_6729_);
lean_ctor_set(v_reuseFailAlloc_6768_, 4, v___y_6653_);
lean_ctor_set(v_reuseFailAlloc_6768_, 5, v_overlaps_6730_);
v___x_6761_ = v_reuseFailAlloc_6768_;
goto v_reusejp_6760_;
}
v_reusejp_6760_:
{
lean_object* v___x_6763_; 
if (v_isShared_6681_ == 0)
{
lean_ctor_set(v___x_6680_, 7, v_remaining_x27_6759_);
lean_ctor_set(v___x_6680_, 6, v_fst_6753_);
lean_ctor_set(v___x_6680_, 5, v___y_6655_);
lean_ctor_set(v___x_6680_, 4, v___y_6658_);
lean_ctor_set(v___x_6680_, 3, v___y_6656_);
lean_ctor_set(v___x_6680_, 2, v_matcherLevels_6660_);
lean_ctor_set(v___x_6680_, 1, v_splitterName_6710_);
lean_ctor_set(v___x_6680_, 0, v___x_6761_);
v___x_6763_ = v___x_6680_;
goto v_reusejp_6762_;
}
else
{
lean_object* v_reuseFailAlloc_6767_; 
v_reuseFailAlloc_6767_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6767_, 0, v___x_6761_);
lean_ctor_set(v_reuseFailAlloc_6767_, 1, v_splitterName_6710_);
lean_ctor_set(v_reuseFailAlloc_6767_, 2, v_matcherLevels_6660_);
lean_ctor_set(v_reuseFailAlloc_6767_, 3, v___y_6656_);
lean_ctor_set(v_reuseFailAlloc_6767_, 4, v___y_6658_);
lean_ctor_set(v_reuseFailAlloc_6767_, 5, v___y_6655_);
lean_ctor_set(v_reuseFailAlloc_6767_, 6, v_fst_6753_);
lean_ctor_set(v_reuseFailAlloc_6767_, 7, v_remaining_x27_6759_);
v___x_6763_ = v_reuseFailAlloc_6767_;
goto v_reusejp_6762_;
}
v_reusejp_6762_:
{
lean_object* v___x_6765_; 
if (v_isShared_6758_ == 0)
{
lean_ctor_set(v___x_6757_, 0, v___x_6763_);
v___x_6765_ = v___x_6757_;
goto v_reusejp_6764_;
}
else
{
lean_object* v_reuseFailAlloc_6766_; 
v_reuseFailAlloc_6766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6766_, 0, v___x_6763_);
v___x_6765_ = v_reuseFailAlloc_6766_;
goto v_reusejp_6764_;
}
v_reusejp_6764_:
{
return v___x_6765_;
}
}
}
}
}
else
{
lean_object* v_a_6770_; lean_object* v___x_6772_; uint8_t v_isShared_6773_; uint8_t v_isSharedCheck_6777_; 
lean_dec(v_fst_6753_);
lean_del_object(v___x_6733_);
lean_dec_ref(v_overlaps_6730_);
lean_dec(v_uElimPos_x3f_6729_);
lean_dec_ref(v_altInfos_6728_);
lean_dec(v_numDiscrs_6727_);
lean_dec(v_numParams_6726_);
lean_dec(v_splitterName_6710_);
lean_dec(v_fst_6682_);
lean_del_object(v___x_6680_);
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
v_a_6770_ = lean_ctor_get(v___x_6754_, 0);
v_isSharedCheck_6777_ = !lean_is_exclusive(v___x_6754_);
if (v_isSharedCheck_6777_ == 0)
{
v___x_6772_ = v___x_6754_;
v_isShared_6773_ = v_isSharedCheck_6777_;
goto v_resetjp_6771_;
}
else
{
lean_inc(v_a_6770_);
lean_dec(v___x_6754_);
v___x_6772_ = lean_box(0);
v_isShared_6773_ = v_isSharedCheck_6777_;
goto v_resetjp_6771_;
}
v_resetjp_6771_:
{
lean_object* v___x_6775_; 
if (v_isShared_6773_ == 0)
{
v___x_6775_ = v___x_6772_;
goto v_reusejp_6774_;
}
else
{
lean_object* v_reuseFailAlloc_6776_; 
v_reuseFailAlloc_6776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6776_, 0, v_a_6770_);
v___x_6775_ = v_reuseFailAlloc_6776_;
goto v_reusejp_6774_;
}
v_reusejp_6774_:
{
return v___x_6775_;
}
}
}
}
else
{
lean_object* v_a_6778_; lean_object* v___x_6780_; uint8_t v_isShared_6781_; uint8_t v_isSharedCheck_6785_; 
lean_del_object(v___x_6733_);
lean_dec_ref(v_overlaps_6730_);
lean_dec(v_uElimPos_x3f_6729_);
lean_dec_ref(v_altInfos_6728_);
lean_dec(v_numDiscrs_6727_);
lean_dec(v_numParams_6726_);
lean_dec(v_splitterName_6710_);
lean_dec(v_fst_6682_);
lean_del_object(v___x_6680_);
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_onRemaining_6537_);
v_a_6778_ = lean_ctor_get(v___x_6751_, 0);
v_isSharedCheck_6785_ = !lean_is_exclusive(v___x_6751_);
if (v_isSharedCheck_6785_ == 0)
{
v___x_6780_ = v___x_6751_;
v_isShared_6781_ = v_isSharedCheck_6785_;
goto v_resetjp_6779_;
}
else
{
lean_inc(v_a_6778_);
lean_dec(v___x_6751_);
v___x_6780_ = lean_box(0);
v_isShared_6781_ = v_isSharedCheck_6785_;
goto v_resetjp_6779_;
}
v_resetjp_6779_:
{
lean_object* v___x_6783_; 
if (v_isShared_6781_ == 0)
{
v___x_6783_ = v___x_6780_;
goto v_reusejp_6782_;
}
else
{
lean_object* v_reuseFailAlloc_6784_; 
v_reuseFailAlloc_6784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6784_, 0, v_a_6778_);
v___x_6783_ = v_reuseFailAlloc_6784_;
goto v_reusejp_6782_;
}
v_reusejp_6782_:
{
return v___x_6783_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6794_; lean_object* v___x_6796_; uint8_t v_isShared_6797_; uint8_t v_isSharedCheck_6801_; 
lean_dec_ref(v_splitterMatchInfo_6711_);
lean_dec(v_splitterName_6710_);
lean_dec(v_a_6707_);
lean_del_object(v___x_6688_);
lean_dec(v_fst_6686_);
lean_del_object(v___x_6684_);
lean_dec(v_fst_6682_);
lean_del_object(v___x_6680_);
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
v_a_6794_ = lean_ctor_get(v___x_6724_, 0);
v_isSharedCheck_6801_ = !lean_is_exclusive(v___x_6724_);
if (v_isSharedCheck_6801_ == 0)
{
v___x_6796_ = v___x_6724_;
v_isShared_6797_ = v_isSharedCheck_6801_;
goto v_resetjp_6795_;
}
else
{
lean_inc(v_a_6794_);
lean_dec(v___x_6724_);
v___x_6796_ = lean_box(0);
v_isShared_6797_ = v_isSharedCheck_6801_;
goto v_resetjp_6795_;
}
v_resetjp_6795_:
{
lean_object* v___x_6799_; 
if (v_isShared_6797_ == 0)
{
v___x_6799_ = v___x_6796_;
goto v_reusejp_6798_;
}
else
{
lean_object* v_reuseFailAlloc_6800_; 
v_reuseFailAlloc_6800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6800_, 0, v_a_6794_);
v___x_6799_ = v_reuseFailAlloc_6800_;
goto v_reusejp_6798_;
}
v_reusejp_6798_:
{
return v___x_6799_;
}
}
}
}
else
{
lean_object* v_a_6802_; lean_object* v___x_6804_; uint8_t v_isShared_6805_; uint8_t v_isSharedCheck_6809_; 
lean_dec_ref(v_aux2_6715_);
lean_dec_ref(v_splitterMatchInfo_6711_);
lean_dec(v_splitterName_6710_);
lean_dec(v_a_6707_);
lean_del_object(v___x_6688_);
lean_dec(v_fst_6686_);
lean_del_object(v___x_6684_);
lean_dec(v_fst_6682_);
lean_del_object(v___x_6680_);
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
v_a_6802_ = lean_ctor_get(v___x_6723_, 0);
v_isSharedCheck_6809_ = !lean_is_exclusive(v___x_6723_);
if (v_isSharedCheck_6809_ == 0)
{
v___x_6804_ = v___x_6723_;
v_isShared_6805_ = v_isSharedCheck_6809_;
goto v_resetjp_6803_;
}
else
{
lean_inc(v_a_6802_);
lean_dec(v___x_6723_);
v___x_6804_ = lean_box(0);
v_isShared_6805_ = v_isSharedCheck_6809_;
goto v_resetjp_6803_;
}
v_resetjp_6803_:
{
lean_object* v___x_6807_; 
if (v_isShared_6805_ == 0)
{
v___x_6807_ = v___x_6804_;
goto v_reusejp_6806_;
}
else
{
lean_object* v_reuseFailAlloc_6808_; 
v_reuseFailAlloc_6808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6808_, 0, v_a_6802_);
v___x_6807_ = v_reuseFailAlloc_6808_;
goto v_reusejp_6806_;
}
v_reusejp_6806_:
{
return v___x_6807_;
}
}
}
}
else
{
lean_object* v_a_6810_; lean_object* v___x_6812_; uint8_t v_isShared_6813_; uint8_t v_isSharedCheck_6817_; 
lean_dec(v_a_6707_);
lean_dec(v___x_6690_);
lean_del_object(v___x_6688_);
lean_dec(v_fst_6686_);
lean_del_object(v___x_6684_);
lean_dec(v_fst_6682_);
lean_del_object(v___x_6680_);
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
v_a_6810_ = lean_ctor_get(v___x_6708_, 0);
v_isSharedCheck_6817_ = !lean_is_exclusive(v___x_6708_);
if (v_isSharedCheck_6817_ == 0)
{
v___x_6812_ = v___x_6708_;
v_isShared_6813_ = v_isSharedCheck_6817_;
goto v_resetjp_6811_;
}
else
{
lean_inc(v_a_6810_);
lean_dec(v___x_6708_);
v___x_6812_ = lean_box(0);
v_isShared_6813_ = v_isSharedCheck_6817_;
goto v_resetjp_6811_;
}
v_resetjp_6811_:
{
lean_object* v___x_6815_; 
if (v_isShared_6813_ == 0)
{
v___x_6815_ = v___x_6812_;
goto v_reusejp_6814_;
}
else
{
lean_object* v_reuseFailAlloc_6816_; 
v_reuseFailAlloc_6816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6816_, 0, v_a_6810_);
v___x_6815_ = v_reuseFailAlloc_6816_;
goto v_reusejp_6814_;
}
v_reusejp_6814_:
{
return v___x_6815_;
}
}
}
}
else
{
lean_object* v_a_6818_; lean_object* v___x_6820_; uint8_t v_isShared_6821_; uint8_t v_isSharedCheck_6825_; 
lean_dec(v___x_6690_);
lean_del_object(v___x_6688_);
lean_dec(v_fst_6686_);
lean_del_object(v___x_6684_);
lean_dec(v_fst_6682_);
lean_del_object(v___x_6680_);
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
v_a_6818_ = lean_ctor_get(v___x_6706_, 0);
v_isSharedCheck_6825_ = !lean_is_exclusive(v___x_6706_);
if (v_isSharedCheck_6825_ == 0)
{
v___x_6820_ = v___x_6706_;
v_isShared_6821_ = v_isSharedCheck_6825_;
goto v_resetjp_6819_;
}
else
{
lean_inc(v_a_6818_);
lean_dec(v___x_6706_);
v___x_6820_ = lean_box(0);
v_isShared_6821_ = v_isSharedCheck_6825_;
goto v_resetjp_6819_;
}
v_resetjp_6819_:
{
lean_object* v___x_6823_; 
if (v_isShared_6821_ == 0)
{
v___x_6823_ = v___x_6820_;
goto v_reusejp_6822_;
}
else
{
lean_object* v_reuseFailAlloc_6824_; 
v_reuseFailAlloc_6824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6824_, 0, v_a_6818_);
v___x_6823_ = v_reuseFailAlloc_6824_;
goto v_reusejp_6822_;
}
v_reusejp_6822_:
{
return v___x_6823_;
}
}
}
}
else
{
lean_object* v_a_6826_; lean_object* v___x_6828_; uint8_t v_isShared_6829_; uint8_t v_isSharedCheck_6833_; 
lean_dec_ref(v_aux1_6694_);
lean_dec(v___x_6690_);
lean_del_object(v___x_6688_);
lean_dec(v_fst_6686_);
lean_del_object(v___x_6684_);
lean_dec(v_fst_6682_);
lean_del_object(v___x_6680_);
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
v_a_6826_ = lean_ctor_get(v___x_6704_, 0);
v_isSharedCheck_6833_ = !lean_is_exclusive(v___x_6704_);
if (v_isSharedCheck_6833_ == 0)
{
v___x_6828_ = v___x_6704_;
v_isShared_6829_ = v_isSharedCheck_6833_;
goto v_resetjp_6827_;
}
else
{
lean_inc(v_a_6826_);
lean_dec(v___x_6704_);
v___x_6828_ = lean_box(0);
v_isShared_6829_ = v_isSharedCheck_6833_;
goto v_resetjp_6827_;
}
v_resetjp_6827_:
{
lean_object* v___x_6831_; 
if (v_isShared_6829_ == 0)
{
v___x_6831_ = v___x_6828_;
goto v_reusejp_6830_;
}
else
{
lean_object* v_reuseFailAlloc_6832_; 
v_reuseFailAlloc_6832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6832_, 0, v_a_6826_);
v___x_6831_ = v_reuseFailAlloc_6832_;
goto v_reusejp_6830_;
}
v_reusejp_6830_:
{
return v___x_6831_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6847_; lean_object* v_fst_6848_; 
lean_dec(v___y_6657_);
v_fst_6847_ = lean_ctor_get(v_a_6675_, 0);
lean_inc(v_fst_6847_);
lean_dec(v_a_6675_);
v_fst_6848_ = lean_ctor_get(v_snd_6676_, 0);
lean_inc(v_fst_6848_);
lean_dec(v_snd_6676_);
v___y_6554_ = v___y_6661_;
v___y_6555_ = v___y_6662_;
v___y_6556_ = v_fst_6848_;
v___y_6557_ = v___y_6664_;
v___y_6558_ = v_matcherLevels_6660_;
v___y_6559_ = v___y_6663_;
v___y_6560_ = v___x_6665_;
v___y_6561_ = v_remaining_x27_6666_;
v___y_6562_ = v___y_6653_;
v___y_6563_ = v___y_6655_;
v___y_6564_ = v___y_6656_;
v___y_6565_ = v_fst_6847_;
v___y_6566_ = v___y_6658_;
goto v___jp_6553_;
}
}
}
else
{
lean_object* v_a_6849_; lean_object* v___x_6851_; uint8_t v_isShared_6852_; uint8_t v_isSharedCheck_6856_; 
lean_dec_ref(v_matcherLevels_6660_);
lean_dec_ref(v___y_6658_);
lean_dec(v___y_6657_);
lean_dec_ref(v___y_6656_);
lean_dec_ref(v___y_6655_);
lean_dec_ref(v___y_6653_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
lean_dec_ref(v_matcherApp_6531_);
v_a_6849_ = lean_ctor_get(v___x_6674_, 0);
v_isSharedCheck_6856_ = !lean_is_exclusive(v___x_6674_);
if (v_isSharedCheck_6856_ == 0)
{
v___x_6851_ = v___x_6674_;
v_isShared_6852_ = v_isSharedCheck_6856_;
goto v_resetjp_6850_;
}
else
{
lean_inc(v_a_6849_);
lean_dec(v___x_6674_);
v___x_6851_ = lean_box(0);
v_isShared_6852_ = v_isSharedCheck_6856_;
goto v_resetjp_6850_;
}
v_resetjp_6850_:
{
lean_object* v___x_6854_; 
if (v_isShared_6852_ == 0)
{
v___x_6854_ = v___x_6851_;
goto v_reusejp_6853_;
}
else
{
lean_object* v_reuseFailAlloc_6855_; 
v_reuseFailAlloc_6855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6855_, 0, v_a_6849_);
v___x_6854_ = v_reuseFailAlloc_6855_;
goto v_reusejp_6853_;
}
v_reusejp_6853_:
{
return v___x_6854_;
}
}
}
}
v___jp_6857_:
{
size_t v_sz_6863_; size_t v___x_6864_; lean_object* v___x_6865_; 
v_sz_6863_ = lean_array_size(v_params_6548_);
v___x_6864_ = ((size_t)0ULL);
lean_inc_ref(v_params_6548_);
lean_inc_ref(v_onParams_6534_);
v___x_6865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6534_, v_sz_6863_, v___x_6864_, v_params_6548_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_);
if (lean_obj_tag(v___x_6865_) == 0)
{
lean_object* v_a_6866_; size_t v_sz_6867_; lean_object* v___x_6868_; 
v_a_6866_ = lean_ctor_get(v___x_6865_, 0);
lean_inc(v_a_6866_);
lean_dec_ref_known(v___x_6865_, 1);
v_sz_6867_ = lean_array_size(v_discrs_6550_);
lean_inc_ref(v_discrs_6550_);
v___x_6868_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6534_, v_sz_6867_, v___x_6864_, v_discrs_6550_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_);
if (lean_obj_tag(v___x_6868_) == 0)
{
lean_object* v_a_6869_; lean_object* v___x_6870_; lean_object* v___x_6871_; lean_object* v___f_6872_; uint8_t v___x_6873_; lean_object* v___x_6874_; 
v_a_6869_ = lean_ctor_get(v___x_6868_, 0);
lean_inc_n(v_a_6869_, 2);
lean_dec_ref_known(v___x_6868_, 1);
v___x_6870_ = lean_box(v_addEqualities_6533_);
v___x_6871_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6550_);
lean_inc_ref(v_toMatcherInfo_6545_);
v___f_6872_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6872_, 0, v_onMotive_6535_);
lean_closure_set(v___f_6872_, 1, v_toMatcherInfo_6545_);
lean_closure_set(v___f_6872_, 2, v_a_6869_);
lean_closure_set(v___f_6872_, 3, v___x_6870_);
lean_closure_set(v___f_6872_, 4, v___x_6871_);
lean_closure_set(v___f_6872_, 5, v_discrs_6550_);
v___x_6873_ = 0;
lean_inc_ref(v_motive_6549_);
v___x_6874_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6549_, v___f_6872_, v___x_6873_, v___y_6859_, v___y_6860_, v___y_6861_, v___y_6862_);
if (lean_obj_tag(v___x_6874_) == 0)
{
lean_object* v_a_6875_; lean_object* v_snd_6876_; lean_object* v_snd_6877_; lean_object* v_uElimPos_x3f_6878_; 
v_a_6875_ = lean_ctor_get(v___x_6874_, 0);
lean_inc(v_a_6875_);
lean_dec_ref_known(v___x_6874_, 1);
v_snd_6876_ = lean_ctor_get(v_a_6875_, 1);
v_snd_6877_ = lean_ctor_get(v_snd_6876_, 1);
lean_inc(v_snd_6877_);
v_uElimPos_x3f_6878_ = lean_ctor_get(v_toMatcherInfo_6545_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6878_) == 0)
{
lean_object* v_fst_6879_; lean_object* v_fst_6880_; lean_object* v_snd_6881_; 
v_fst_6879_ = lean_ctor_get(v_a_6875_, 0);
lean_inc(v_fst_6879_);
lean_dec(v_a_6875_);
v_fst_6880_ = lean_ctor_get(v_snd_6877_, 0);
lean_inc(v_fst_6880_);
v_snd_6881_ = lean_ctor_get(v_snd_6877_, 1);
lean_inc(v_snd_6881_);
lean_dec(v_snd_6877_);
lean_inc_ref(v_matcherLevels_6547_);
v___y_6653_ = v_snd_6881_;
v___y_6654_ = v___x_6864_;
v___y_6655_ = v_a_6869_;
v___y_6656_ = v_a_6866_;
v___y_6657_ = v_numDiscrEqs_6858_;
v___y_6658_ = v_fst_6879_;
v___y_6659_ = v_fst_6880_;
v_matcherLevels_6660_ = v_matcherLevels_6547_;
v___y_6661_ = v___y_6859_;
v___y_6662_ = v___y_6860_;
v___y_6663_ = v___y_6861_;
v___y_6664_ = v___y_6862_;
goto v___jp_6652_;
}
else
{
lean_object* v_fst_6882_; lean_object* v_fst_6883_; lean_object* v_fst_6884_; lean_object* v_snd_6885_; lean_object* v_val_6886_; lean_object* v___x_6887_; 
lean_inc(v_snd_6876_);
v_fst_6882_ = lean_ctor_get(v_a_6875_, 0);
lean_inc(v_fst_6882_);
lean_dec(v_a_6875_);
v_fst_6883_ = lean_ctor_get(v_snd_6876_, 0);
lean_inc(v_fst_6883_);
lean_dec(v_snd_6876_);
v_fst_6884_ = lean_ctor_get(v_snd_6877_, 0);
lean_inc(v_fst_6884_);
v_snd_6885_ = lean_ctor_get(v_snd_6877_, 1);
lean_inc(v_snd_6885_);
lean_dec(v_snd_6877_);
v_val_6886_ = lean_ctor_get(v_uElimPos_x3f_6878_, 0);
lean_inc_ref(v_matcherLevels_6547_);
v___x_6887_ = lean_array_set(v_matcherLevels_6547_, v_val_6886_, v_fst_6883_);
v___y_6653_ = v_snd_6885_;
v___y_6654_ = v___x_6864_;
v___y_6655_ = v_a_6869_;
v___y_6656_ = v_a_6866_;
v___y_6657_ = v_numDiscrEqs_6858_;
v___y_6658_ = v_fst_6882_;
v___y_6659_ = v_fst_6884_;
v_matcherLevels_6660_ = v___x_6887_;
v___y_6661_ = v___y_6859_;
v___y_6662_ = v___y_6860_;
v___y_6663_ = v___y_6861_;
v___y_6664_ = v___y_6862_;
goto v___jp_6652_;
}
}
else
{
lean_object* v_a_6888_; lean_object* v___x_6890_; uint8_t v_isShared_6891_; uint8_t v_isSharedCheck_6895_; 
lean_dec(v_a_6869_);
lean_dec(v_a_6866_);
lean_dec(v_numDiscrEqs_6858_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
lean_dec_ref(v_matcherApp_6531_);
v_a_6888_ = lean_ctor_get(v___x_6874_, 0);
v_isSharedCheck_6895_ = !lean_is_exclusive(v___x_6874_);
if (v_isSharedCheck_6895_ == 0)
{
v___x_6890_ = v___x_6874_;
v_isShared_6891_ = v_isSharedCheck_6895_;
goto v_resetjp_6889_;
}
else
{
lean_inc(v_a_6888_);
lean_dec(v___x_6874_);
v___x_6890_ = lean_box(0);
v_isShared_6891_ = v_isSharedCheck_6895_;
goto v_resetjp_6889_;
}
v_resetjp_6889_:
{
lean_object* v___x_6893_; 
if (v_isShared_6891_ == 0)
{
v___x_6893_ = v___x_6890_;
goto v_reusejp_6892_;
}
else
{
lean_object* v_reuseFailAlloc_6894_; 
v_reuseFailAlloc_6894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6894_, 0, v_a_6888_);
v___x_6893_ = v_reuseFailAlloc_6894_;
goto v_reusejp_6892_;
}
v_reusejp_6892_:
{
return v___x_6893_;
}
}
}
}
else
{
lean_object* v_a_6896_; lean_object* v___x_6898_; uint8_t v_isShared_6899_; uint8_t v_isSharedCheck_6903_; 
lean_dec(v_a_6866_);
lean_dec(v_numDiscrEqs_6858_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
lean_dec_ref(v_onMotive_6535_);
lean_dec_ref(v_matcherApp_6531_);
v_a_6896_ = lean_ctor_get(v___x_6868_, 0);
v_isSharedCheck_6903_ = !lean_is_exclusive(v___x_6868_);
if (v_isSharedCheck_6903_ == 0)
{
v___x_6898_ = v___x_6868_;
v_isShared_6899_ = v_isSharedCheck_6903_;
goto v_resetjp_6897_;
}
else
{
lean_inc(v_a_6896_);
lean_dec(v___x_6868_);
v___x_6898_ = lean_box(0);
v_isShared_6899_ = v_isSharedCheck_6903_;
goto v_resetjp_6897_;
}
v_resetjp_6897_:
{
lean_object* v___x_6901_; 
if (v_isShared_6899_ == 0)
{
v___x_6901_ = v___x_6898_;
goto v_reusejp_6900_;
}
else
{
lean_object* v_reuseFailAlloc_6902_; 
v_reuseFailAlloc_6902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6902_, 0, v_a_6896_);
v___x_6901_ = v_reuseFailAlloc_6902_;
goto v_reusejp_6900_;
}
v_reusejp_6900_:
{
return v___x_6901_;
}
}
}
}
else
{
lean_object* v_a_6904_; lean_object* v___x_6906_; uint8_t v_isShared_6907_; uint8_t v_isSharedCheck_6911_; 
lean_dec(v_numDiscrEqs_6858_);
lean_dec_ref(v_remaining_6552_);
lean_dec_ref(v_alts_6551_);
lean_dec(v_matcherName_6546_);
lean_dec_ref(v_toMatcherInfo_6545_);
lean_dec_ref(v_onRemaining_6537_);
lean_dec_ref(v_onAlt_6536_);
lean_dec_ref(v_onMotive_6535_);
lean_dec_ref(v_onParams_6534_);
lean_dec_ref(v_matcherApp_6531_);
v_a_6904_ = lean_ctor_get(v___x_6865_, 0);
v_isSharedCheck_6911_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6911_ == 0)
{
v___x_6906_ = v___x_6865_;
v_isShared_6907_ = v_isSharedCheck_6911_;
goto v_resetjp_6905_;
}
else
{
lean_inc(v_a_6904_);
lean_dec(v___x_6865_);
v___x_6906_ = lean_box(0);
v_isShared_6907_ = v_isSharedCheck_6911_;
goto v_resetjp_6905_;
}
v_resetjp_6905_:
{
lean_object* v___x_6909_; 
if (v_isShared_6907_ == 0)
{
v___x_6909_ = v___x_6906_;
goto v_reusejp_6908_;
}
else
{
lean_object* v_reuseFailAlloc_6910_; 
v_reuseFailAlloc_6910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6910_, 0, v_a_6904_);
v___x_6909_ = v_reuseFailAlloc_6910_;
goto v_reusejp_6908_;
}
v_reusejp_6908_:
{
return v___x_6909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6931_, lean_object* v_useSplitter_6932_, lean_object* v_addEqualities_6933_, lean_object* v_onParams_6934_, lean_object* v_onMotive_6935_, lean_object* v_onAlt_6936_, lean_object* v_onRemaining_6937_, lean_object* v___y_6938_, lean_object* v___y_6939_, lean_object* v___y_6940_, lean_object* v___y_6941_, lean_object* v___y_6942_){
_start:
{
uint8_t v_useSplitter_boxed_6943_; uint8_t v_addEqualities_boxed_6944_; lean_object* v_res_6945_; 
v_useSplitter_boxed_6943_ = lean_unbox(v_useSplitter_6932_);
v_addEqualities_boxed_6944_ = lean_unbox(v_addEqualities_6933_);
v_res_6945_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6931_, v_useSplitter_boxed_6943_, v_addEqualities_boxed_6944_, v_onParams_6934_, v_onMotive_6935_, v_onAlt_6936_, v_onRemaining_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_);
lean_dec(v___y_6941_);
lean_dec_ref(v___y_6940_);
lean_dec(v___y_6939_);
lean_dec_ref(v___y_6938_);
return v_res_6945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6951_, lean_object* v_a_6952_, lean_object* v_a_6953_, lean_object* v_a_6954_, lean_object* v_a_6955_){
_start:
{
lean_object* v_toMatcherInfo_6957_; lean_object* v_matcherName_6958_; lean_object* v_matcherLevels_6959_; lean_object* v_params_6960_; lean_object* v_alts_6961_; lean_object* v_remaining_6962_; lean_object* v___f_6963_; lean_object* v___f_6964_; lean_object* v_nExtra_6965_; uint8_t v___x_6966_; lean_object* v___f_6967_; uint8_t v___x_6968_; lean_object* v___x_6969_; lean_object* v___x_6970_; lean_object* v___f_6971_; lean_object* v___x_6972_; 
v_toMatcherInfo_6957_ = lean_ctor_get(v_matcherApp_6951_, 0);
v_matcherName_6958_ = lean_ctor_get(v_matcherApp_6951_, 1);
v_matcherLevels_6959_ = lean_ctor_get(v_matcherApp_6951_, 2);
v_params_6960_ = lean_ctor_get(v_matcherApp_6951_, 3);
v_alts_6961_ = lean_ctor_get(v_matcherApp_6951_, 6);
v_remaining_6962_ = lean_ctor_get(v_matcherApp_6951_, 7);
v___f_6963_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6964_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6965_ = lean_array_get_size(v_remaining_6962_);
v___x_6966_ = 1;
v___f_6967_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6968_ = 0;
v___x_6969_ = lean_box(v___x_6968_);
v___x_6970_ = lean_box(v___x_6966_);
lean_inc_ref(v_matcherLevels_6959_);
lean_inc_ref(v_params_6960_);
lean_inc(v_matcherName_6958_);
lean_inc_ref(v_toMatcherInfo_6957_);
lean_inc_ref(v_alts_6961_);
v___f_6971_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6971_, 0, v_nExtra_6965_);
lean_closure_set(v___f_6971_, 1, v___x_6969_);
lean_closure_set(v___f_6971_, 2, v___x_6970_);
lean_closure_set(v___f_6971_, 3, v_alts_6961_);
lean_closure_set(v___f_6971_, 4, v_toMatcherInfo_6957_);
lean_closure_set(v___f_6971_, 5, v_matcherName_6958_);
lean_closure_set(v___f_6971_, 6, v_params_6960_);
lean_closure_set(v___f_6971_, 7, v_matcherLevels_6959_);
v___x_6972_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6951_, v___x_6966_, v___x_6968_, v___f_6963_, v___f_6971_, v___f_6967_, v___f_6964_, v_a_6952_, v_a_6953_, v_a_6954_, v_a_6955_);
return v___x_6972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6973_, lean_object* v_a_6974_, lean_object* v_a_6975_, lean_object* v_a_6976_, lean_object* v_a_6977_, lean_object* v_a_6978_){
_start:
{
lean_object* v_res_6979_; 
v_res_6979_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6973_, v_a_6974_, v_a_6975_, v_a_6976_, v_a_6977_);
lean_dec(v_a_6977_);
lean_dec_ref(v_a_6976_);
lean_dec(v_a_6975_);
lean_dec_ref(v_a_6974_);
return v_res_6979_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6980_, lean_object* v_termAlt_6981_, lean_object* v_inst_6982_, lean_object* v_R_6983_, lean_object* v_a_6984_, lean_object* v_b_6985_, lean_object* v_c_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_){
_start:
{
lean_object* v___x_6992_; 
v___x_6992_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6980_, v_termAlt_6981_, v_a_6984_, v_b_6985_, v___y_6987_, v___y_6988_, v___y_6989_, v___y_6990_);
return v___x_6992_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6993_, lean_object* v_termAlt_6994_, lean_object* v_inst_6995_, lean_object* v_R_6996_, lean_object* v_a_6997_, lean_object* v_b_6998_, lean_object* v_c_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_, lean_object* v___y_7002_, lean_object* v___y_7003_, lean_object* v___y_7004_){
_start:
{
lean_object* v_res_7005_; 
v_res_7005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6993_, v_termAlt_6994_, v_inst_6995_, v_R_6996_, v_a_6997_, v_b_6998_, v_c_6999_, v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_);
lean_dec(v___y_7003_);
lean_dec_ref(v___y_7002_);
lean_dec(v___y_7001_);
lean_dec_ref(v___y_7000_);
return v_res_7005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_7006_, lean_object* v_fvars_7007_, lean_object* v_names_7008_, lean_object* v_k_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_, lean_object* v___y_7013_){
_start:
{
lean_object* v___x_7015_; 
v___x_7015_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_7007_, v_names_7008_, v_k_7009_, v___y_7010_, v___y_7011_, v___y_7012_, v___y_7013_);
return v___x_7015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_7016_, lean_object* v_fvars_7017_, lean_object* v_names_7018_, lean_object* v_k_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_){
_start:
{
lean_object* v_res_7025_; 
v_res_7025_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_7016_, v_fvars_7017_, v_names_7018_, v_k_7019_, v___y_7020_, v___y_7021_, v___y_7022_, v___y_7023_);
lean_dec(v___y_7023_);
lean_dec_ref(v___y_7022_);
lean_dec(v___y_7021_);
lean_dec_ref(v___y_7020_);
lean_dec_ref(v_names_7018_);
lean_dec_ref(v_fvars_7017_);
return v_res_7025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7026_, lean_object* v_origAltType_7027_, lean_object* v_altInfo_7028_, lean_object* v_k_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_, lean_object* v___y_7032_, lean_object* v___y_7033_){
_start:
{
lean_object* v___x_7035_; 
v___x_7035_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7027_, v_altInfo_7028_, v_k_7029_, v___y_7030_, v___y_7031_, v___y_7032_, v___y_7033_);
return v___x_7035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7036_, lean_object* v_origAltType_7037_, lean_object* v_altInfo_7038_, lean_object* v_k_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_, lean_object* v___y_7042_, lean_object* v___y_7043_, lean_object* v___y_7044_){
_start:
{
lean_object* v_res_7045_; 
v_res_7045_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7036_, v_origAltType_7037_, v_altInfo_7038_, v_k_7039_, v___y_7040_, v___y_7041_, v___y_7042_, v___y_7043_);
lean_dec(v___y_7043_);
lean_dec_ref(v___y_7042_);
lean_dec(v___y_7041_);
lean_dec_ref(v___y_7040_);
return v_res_7045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_){
_start:
{
lean_object* v___x_7052_; 
v___x_7052_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7046_, v___y_7050_);
return v___x_7052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7053_, lean_object* v___y_7054_, lean_object* v___y_7055_, lean_object* v___y_7056_, lean_object* v___y_7057_, lean_object* v___y_7058_){
_start:
{
lean_object* v_res_7059_; 
v_res_7059_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7053_, v___y_7054_, v___y_7055_, v___y_7056_, v___y_7057_);
lean_dec(v___y_7057_);
lean_dec_ref(v___y_7056_);
lean_dec(v___y_7055_);
lean_dec_ref(v___y_7054_);
return v_res_7059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7060_, size_t v_i_7061_, lean_object* v_bs_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_, lean_object* v___y_7065_, lean_object* v___y_7066_){
_start:
{
lean_object* v___x_7068_; 
v___x_7068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7060_, v_i_7061_, v_bs_7062_, v___y_7063_, v___y_7065_, v___y_7066_);
return v___x_7068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7069_, lean_object* v_i_7070_, lean_object* v_bs_7071_, lean_object* v___y_7072_, lean_object* v___y_7073_, lean_object* v___y_7074_, lean_object* v___y_7075_, lean_object* v___y_7076_){
_start:
{
size_t v_sz_boxed_7077_; size_t v_i_boxed_7078_; lean_object* v_res_7079_; 
v_sz_boxed_7077_ = lean_unbox_usize(v_sz_7069_);
lean_dec(v_sz_7069_);
v_i_boxed_7078_ = lean_unbox_usize(v_i_7070_);
lean_dec(v_i_7070_);
v_res_7079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7077_, v_i_boxed_7078_, v_bs_7071_, v___y_7072_, v___y_7073_, v___y_7074_, v___y_7075_);
lean_dec(v___y_7075_);
lean_dec_ref(v___y_7074_);
lean_dec(v___y_7073_);
lean_dec_ref(v___y_7072_);
return v_res_7079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7080_, lean_object* v_onAlt_7081_, lean_object* v_extraEqualities_7082_, lean_object* v_inst_7083_, lean_object* v_R_7084_, lean_object* v_a_7085_, lean_object* v_b_7086_, lean_object* v_c_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_, lean_object* v___y_7090_, lean_object* v___y_7091_){
_start:
{
lean_object* v___x_7093_; 
v___x_7093_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7080_, v_onAlt_7081_, v_extraEqualities_7082_, v_a_7085_, v_b_7086_, v___y_7088_, v___y_7089_, v___y_7090_, v___y_7091_);
return v___x_7093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7094_, lean_object* v_onAlt_7095_, lean_object* v_extraEqualities_7096_, lean_object* v_inst_7097_, lean_object* v_R_7098_, lean_object* v_a_7099_, lean_object* v_b_7100_, lean_object* v_c_7101_, lean_object* v___y_7102_, lean_object* v___y_7103_, lean_object* v___y_7104_, lean_object* v___y_7105_, lean_object* v___y_7106_){
_start:
{
lean_object* v_res_7107_; 
v_res_7107_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7094_, v_onAlt_7095_, v_extraEqualities_7096_, v_inst_7097_, v_R_7098_, v_a_7099_, v_b_7100_, v_c_7101_, v___y_7102_, v___y_7103_, v___y_7104_, v___y_7105_);
lean_dec(v___y_7105_);
lean_dec_ref(v___y_7104_);
lean_dec(v___y_7103_);
lean_dec_ref(v___y_7102_);
lean_dec(v_upperBound_7094_);
return v_res_7107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7108_, lean_object* v_onAlt_7109_, uint8_t v_useSplitter_7110_, lean_object* v_extraEqualities_7111_, lean_object* v_numDiscrEqs_7112_, lean_object* v_inst_7113_, lean_object* v_R_7114_, lean_object* v_a_7115_, lean_object* v_b_7116_, lean_object* v_c_7117_, lean_object* v___y_7118_, lean_object* v___y_7119_, lean_object* v___y_7120_, lean_object* v___y_7121_){
_start:
{
lean_object* v___x_7123_; 
v___x_7123_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7108_, v_onAlt_7109_, v_useSplitter_7110_, v_extraEqualities_7111_, v_numDiscrEqs_7112_, v_a_7115_, v_b_7116_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_);
return v___x_7123_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7124_, lean_object* v_onAlt_7125_, lean_object* v_useSplitter_7126_, lean_object* v_extraEqualities_7127_, lean_object* v_numDiscrEqs_7128_, lean_object* v_inst_7129_, lean_object* v_R_7130_, lean_object* v_a_7131_, lean_object* v_b_7132_, lean_object* v_c_7133_, lean_object* v___y_7134_, lean_object* v___y_7135_, lean_object* v___y_7136_, lean_object* v___y_7137_, lean_object* v___y_7138_){
_start:
{
uint8_t v_useSplitter_boxed_7139_; lean_object* v_res_7140_; 
v_useSplitter_boxed_7139_ = lean_unbox(v_useSplitter_7126_);
v_res_7140_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7124_, v_onAlt_7125_, v_useSplitter_boxed_7139_, v_extraEqualities_7127_, v_numDiscrEqs_7128_, v_inst_7129_, v_R_7130_, v_a_7131_, v_b_7132_, v_c_7133_, v___y_7134_, v___y_7135_, v___y_7136_, v___y_7137_);
lean_dec(v___y_7137_);
lean_dec_ref(v___y_7136_);
lean_dec(v___y_7135_);
lean_dec_ref(v___y_7134_);
lean_dec(v_upperBound_7124_);
return v_res_7140_;
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
