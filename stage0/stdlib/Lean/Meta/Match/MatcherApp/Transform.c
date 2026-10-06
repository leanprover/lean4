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
uint8_t v___x_3876__boxed_142_; uint8_t v_refined_boxed_143_; lean_object* v_res_144_; 
v___x_3876__boxed_142_ = lean_unbox(v___x_132_);
v_refined_boxed_143_ = lean_unbox(v_refined_133_);
v_res_144_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_xs_130_, v_alt_131_, v___x_3876__boxed_142_, v_refined_boxed_143_, v_unrefinedArgType_134_, v_binderType_135_, v_x_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
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
lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; lean_object* v___y_257_; uint8_t v___y_258_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = lean_array_get_size(v_xs_211_);
v___x_267_ = lean_nat_dec_eq(v___x_266_, v_numParams_210_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_268_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5);
v___x_269_ = l_Nat_reprFast(v_numParams_210_);
v___x_270_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
v___x_271_ = l_Lean_MessageData_ofFormat(v___x_270_);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_268_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_274_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref_known(v___x_275_, 1);
goto v___jp_261_;
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_binderType_209_);
lean_dec_ref(v_unrefinedArgType_208_);
v_a_276_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_275_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
lean_dec(v_numParams_210_);
goto v___jp_261_;
}
v___jp_218_:
{
if (lean_obj_tag(v___y_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; 
v_a_224_ = lean_ctor_get(v___y_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___y_223_, 1);
v___x_225_ = l_Lean_Meta_whnfForall(v_a_224_, v___y_220_, v___y_219_, v___y_221_, v___y_222_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
if (lean_obj_tag(v_a_226_) == 7)
{
lean_object* v_binderName_227_; lean_object* v_binderType_228_; uint8_t v_binderInfo_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___f_232_; lean_object* v___x_233_; 
v_binderName_227_ = lean_ctor_get(v_a_226_, 0);
lean_inc(v_binderName_227_);
v_binderType_228_ = lean_ctor_get(v_a_226_, 1);
lean_inc_ref_n(v_binderType_228_, 2);
v_binderInfo_229_ = lean_ctor_get_uint8(v_a_226_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_226_, 3);
v___x_230_ = lean_box(v___x_206_);
v___x_231_ = lean_box(v_refined_207_);
v___f_232_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 6);
lean_closure_set(v___f_232_, 0, v_xs_211_);
lean_closure_set(v___f_232_, 1, v_alt_212_);
lean_closure_set(v___f_232_, 2, v___x_230_);
lean_closure_set(v___f_232_, 3, v___x_231_);
lean_closure_set(v___f_232_, 4, v_unrefinedArgType_208_);
lean_closure_set(v___f_232_, 5, v_binderType_228_);
v___x_233_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_227_, v_binderInfo_229_, v_binderType_228_, v___f_232_, v___y_220_, v___y_219_, v___y_221_, v___y_222_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_a_226_);
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
v___x_234_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_235_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_234_, v___y_220_, v___y_219_, v___y_221_, v___y_222_);
return v___x_235_;
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
v_a_236_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_225_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_225_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v_alt_212_);
lean_dec_ref(v_xs_211_);
lean_dec_ref(v_unrefinedArgType_208_);
v_a_244_ = lean_ctor_get(v___y_223_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___y_223_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___y_223_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___y_223_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
v___jp_252_:
{
if (v___y_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref(v___y_255_);
v___x_259_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_260_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_259_, v___y_254_, v___y_253_, v___y_256_, v___y_257_);
v___y_219_ = v___y_253_;
v___y_220_ = v___y_254_;
v___y_221_ = v___y_256_;
v___y_222_ = v___y_257_;
v___y_223_ = v___x_260_;
goto v___jp_218_;
}
else
{
v___y_219_ = v___y_253_;
v___y_220_ = v___y_254_;
v___y_221_ = v___y_256_;
v___y_222_ = v___y_257_;
v___y_223_ = v___y_255_;
goto v___jp_218_;
}
}
v___jp_261_:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Meta_instantiateForall(v_binderType_209_, v_xs_211_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_262_) == 0)
{
v___y_219_ = v___y_214_;
v___y_220_ = v___y_213_;
v___y_221_ = v___y_215_;
v___y_222_ = v___y_216_;
v___y_223_ = v___x_262_;
goto v___jp_218_;
}
else
{
lean_object* v_a_263_; uint8_t v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
v___x_264_ = l_Lean_Exception_isInterrupt(v_a_263_);
if (v___x_264_ == 0)
{
uint8_t v___x_265_; 
lean_inc(v_a_263_);
v___x_265_ = l_Lean_Exception_isRuntime(v_a_263_);
v___y_253_ = v___y_214_;
v___y_254_ = v___y_213_;
v___y_255_ = v___x_262_;
v___y_256_ = v___y_215_;
v___y_257_ = v___y_216_;
v___y_258_ = v___x_265_;
goto v___jp_252_;
}
else
{
v___y_253_ = v___y_214_;
v___y_254_ = v___y_213_;
v___y_255_ = v___x_262_;
v___y_256_ = v___y_215_;
v___y_257_ = v___y_216_;
v___y_258_ = v___x_264_;
goto v___jp_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* v___x_284_, lean_object* v_refined_285_, lean_object* v_unrefinedArgType_286_, lean_object* v_binderType_287_, lean_object* v_numParams_288_, lean_object* v_xs_289_, lean_object* v_alt_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v___x_4052__boxed_296_; uint8_t v_refined_boxed_297_; lean_object* v_res_298_; 
v___x_4052__boxed_296_ = lean_unbox(v___x_284_);
v_refined_boxed_297_ = lean_unbox(v_refined_285_);
v_res_298_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4052__boxed_296_, v_refined_boxed_297_, v_unrefinedArgType_286_, v_binderType_287_, v_numParams_288_, v_xs_289_, v_alt_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
v___x_301_ = l_Lean_stringToMessageData(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* v_unrefinedArgType_302_, lean_object* v_typeNew_303_, lean_object* v_altNumParams_304_, lean_object* v_alts_305_, uint8_t v_refined_306_, lean_object* v_i_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_array_get_size(v_alts_305_);
v___x_314_ = lean_nat_dec_lt(v_i_307_, v___x_313_);
if (v___x_314_ == 0)
{
lean_dec(v_i_307_);
lean_dec_ref(v_typeNew_303_);
lean_dec_ref(v_unrefinedArgType_302_);
if (v_refined_306_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec_ref(v_alts_305_);
v___x_315_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
v___x_316_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_315_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
return v___x_316_;
}
else
{
lean_object* v___x_317_; 
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v_alts_305_);
return v___x_317_;
}
}
else
{
lean_object* v___x_318_; lean_object* v_alt_319_; lean_object* v_numParams_320_; lean_object* v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v_alt_319_ = lean_array_fget_borrowed(v_alts_305_, v_i_307_);
v_numParams_320_ = lean_array_get_borrowed(v___x_318_, v_altNumParams_304_, v_i_307_);
v___x_321_ = l_Lean_Meta_whnfD(v_typeNew_303_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_321_) == 0)
{
lean_object* v_a_322_; 
v_a_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v___x_321_, 1);
if (lean_obj_tag(v_a_322_) == 7)
{
lean_object* v_binderType_323_; lean_object* v_body_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___f_327_; uint8_t v___x_328_; lean_object* v___x_329_; 
v_binderType_323_ = lean_ctor_get(v_a_322_, 1);
lean_inc_ref(v_binderType_323_);
v_body_324_ = lean_ctor_get(v_a_322_, 2);
lean_inc_ref(v_body_324_);
lean_dec_ref_known(v_a_322_, 3);
v___x_325_ = lean_box(v___x_314_);
v___x_326_ = lean_box(v_refined_306_);
lean_inc_n(v_numParams_320_, 2);
lean_inc_ref(v_unrefinedArgType_302_);
v___f_327_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(v___f_327_, 0, v___x_325_);
lean_closure_set(v___f_327_, 1, v___x_326_);
lean_closure_set(v___f_327_, 2, v_unrefinedArgType_302_);
lean_closure_set(v___f_327_, 3, v_binderType_323_);
lean_closure_set(v___f_327_, 4, v_numParams_320_);
v___x_328_ = 0;
lean_inc(v_alt_319_);
v___x_329_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_alt_319_, v_numParams_320_, v___f_327_, v___x_328_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
if (lean_obj_tag(v___x_329_) == 0)
{
lean_object* v_a_330_; lean_object* v_fst_331_; lean_object* v_snd_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v_a_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_a_330_);
lean_dec_ref_known(v___x_329_, 1);
v_fst_331_ = lean_ctor_get(v_a_330_, 0);
lean_inc(v_fst_331_);
v_snd_332_ = lean_ctor_get(v_a_330_, 1);
lean_inc(v_snd_332_);
lean_dec(v_a_330_);
v___x_333_ = lean_expr_instantiate1(v_body_324_, v_fst_331_);
lean_dec_ref(v_body_324_);
v___x_334_ = lean_array_fset(v_alts_305_, v_i_307_, v_fst_331_);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_i_307_, v___x_335_);
lean_dec(v_i_307_);
v___x_337_ = lean_unbox(v_snd_332_);
lean_dec(v_snd_332_);
v_typeNew_303_ = v___x_333_;
v_alts_305_ = v___x_334_;
v_refined_306_ = v___x_337_;
v_i_307_ = v___x_336_;
goto _start;
}
else
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_346_; 
lean_dec_ref(v_body_324_);
lean_dec(v_i_307_);
lean_dec_ref(v_alts_305_);
lean_dec_ref(v_unrefinedArgType_302_);
v_a_339_ = lean_ctor_get(v___x_329_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v___x_329_);
if (v_isSharedCheck_346_ == 0)
{
v___x_341_ = v___x_329_;
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_329_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_346_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
v___x_344_ = v_reuseFailAlloc_345_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
return v___x_344_;
}
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_a_322_);
lean_dec(v_i_307_);
lean_dec_ref(v_alts_305_);
lean_dec_ref(v_unrefinedArgType_302_);
v___x_347_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_348_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_347_, v_a_308_, v_a_309_, v_a_310_, v_a_311_);
return v___x_348_;
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_i_307_);
lean_dec_ref(v_alts_305_);
lean_dec_ref(v_unrefinedArgType_302_);
v_a_349_ = lean_ctor_get(v___x_321_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_321_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_321_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_321_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* v_unrefinedArgType_357_, lean_object* v_typeNew_358_, lean_object* v_altNumParams_359_, lean_object* v_alts_360_, lean_object* v_refined_361_, lean_object* v_i_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
uint8_t v_refined_boxed_368_; lean_object* v_res_369_; 
v_refined_boxed_368_ = lean_unbox(v_refined_361_);
v_res_369_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_357_, v_typeNew_358_, v_altNumParams_359_, v_alts_360_, v_refined_boxed_368_, v_i_362_, v_a_363_, v_a_364_, v_a_365_, v_a_366_);
lean_dec(v_a_366_);
lean_dec_ref(v_a_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec_ref(v_altNumParams_359_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* v_00_u03b1_370_, lean_object* v_msg_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* v_00_u03b1_378_, lean_object* v_msg_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(v_00_u03b1_378_, v_msg_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* v_e_386_, lean_object* v_k_387_, uint8_t v_cleanupAnnotations_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___f_394_; uint8_t v___x_395_; uint8_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___f_394_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_394_, 0, v_k_387_);
v___x_395_ = 1;
v___x_396_ = 0;
v___x_397_ = lean_box(0);
v___x_398_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_386_, v___x_395_, v___x_396_, v___x_395_, v___x_396_, v___x_397_, v___f_394_, v_cleanupAnnotations_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_398_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_398_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
v_a_407_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_398_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_398_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* v_e_415_, lean_object* v_k_416_, lean_object* v_cleanupAnnotations_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_423_; lean_object* v_res_424_; 
v_cleanupAnnotations_boxed_423_ = lean_unbox(v_cleanupAnnotations_417_);
v_res_424_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_415_, v_k_416_, v_cleanupAnnotations_boxed_423_, v___y_418_, v___y_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* v_00_u03b1_425_, lean_object* v_e_426_, lean_object* v_k_427_, uint8_t v_cleanupAnnotations_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_426_, v_k_427_, v_cleanupAnnotations_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* v_00_u03b1_435_, lean_object* v_e_436_, lean_object* v_k_437_, lean_object* v_cleanupAnnotations_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_444_; lean_object* v_res_445_; 
v_cleanupAnnotations_boxed_444_ = lean_unbox(v_cleanupAnnotations_438_);
v_res_445_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(v_00_u03b1_435_, v_e_436_, v_k_437_, v_cleanupAnnotations_boxed_444_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* v___x_446_, lean_object* v_motiveArgs_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v_zero_450_; uint8_t v_isZero_451_; 
v_zero_450_ = lean_unsigned_to_nat(0u);
v_isZero_451_ = lean_nat_dec_eq(v_x_448_, v_zero_450_);
if (v_isZero_451_ == 1)
{
lean_dec(v_x_448_);
return v_x_449_;
}
else
{
lean_object* v_one_452_; lean_object* v_n_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v_one_452_ = lean_unsigned_to_nat(1u);
v_n_453_ = lean_nat_sub(v_x_448_, v_one_452_);
lean_dec(v_x_448_);
v___x_454_ = lean_array_fget_borrowed(v___x_446_, v_n_453_);
v___x_455_ = l_Lean_Expr_isFVar(v___x_454_);
if (v___x_455_ == 0)
{
v_x_448_ = v_n_453_;
goto _start;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = l_Lean_instInhabitedExpr;
v___x_458_ = lean_array_get_borrowed(v___x_457_, v_motiveArgs_447_, v_n_453_);
lean_inc(v___x_454_);
v___x_459_ = l_Lean_Expr_replaceFVar(v_x_449_, v___x_454_, v___x_458_);
lean_dec_ref(v_x_449_);
v_x_448_ = v_n_453_;
v_x_449_ = v___x_459_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* v___x_461_, lean_object* v_motiveArgs_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_461_, v_motiveArgs_462_, v_x_463_, v_x_464_);
lean_dec_ref(v_motiveArgs_462_);
lean_dec_ref(v___x_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* v___x_466_, lean_object* v_motiveArgs_467_, lean_object* v_x_468_, lean_object* v_x_469_){
_start:
{
lean_object* v_zero_470_; uint8_t v_isZero_471_; 
v_zero_470_ = lean_unsigned_to_nat(0u);
v_isZero_471_ = lean_nat_dec_eq(v_x_468_, v_zero_470_);
if (v_isZero_471_ == 1)
{
return v_x_469_;
}
else
{
lean_object* v_one_472_; lean_object* v_n_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_one_472_ = lean_unsigned_to_nat(1u);
v_n_473_ = lean_nat_sub(v_x_468_, v_one_472_);
v___x_474_ = lean_array_fget_borrowed(v___x_466_, v_n_473_);
v___x_475_ = l_Lean_Expr_isFVar(v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
v___x_476_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_466_, v_motiveArgs_467_, v_n_473_, v_x_469_);
return v___x_476_;
}
else
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = l_Lean_instInhabitedExpr;
v___x_478_ = lean_array_get_borrowed(v___x_477_, v_motiveArgs_467_, v_n_473_);
lean_inc(v___x_474_);
v___x_479_ = l_Lean_Expr_replaceFVar(v_x_469_, v___x_474_, v___x_478_);
lean_dec_ref(v_x_469_);
v___x_480_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_466_, v_motiveArgs_467_, v_n_473_, v___x_479_);
return v___x_480_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* v___x_481_, lean_object* v_motiveArgs_482_, lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v___x_481_, v_motiveArgs_482_, v_x_483_, v_x_484_);
lean_dec(v_x_483_);
lean_dec_ref(v_motiveArgs_482_);
lean_dec_ref(v___x_481_);
return v_res_485_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0));
v___x_488_ = l_Lean_stringToMessageData(v___x_487_);
return v___x_488_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2));
v___x_491_ = l_Lean_stringToMessageData(v___x_490_);
return v___x_491_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4));
v___x_494_ = l_Lean_stringToMessageData(v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_495_, lean_object* v_e_496_, lean_object* v_discrs_497_, lean_object* v_toMatcherInfo_498_, lean_object* v_remaining_499_, lean_object* v_matcherName_500_, lean_object* v_alts_501_, lean_object* v_params_502_, lean_object* v_matcherLevels_503_, lean_object* v_motiveArgs_504_, lean_object* v_motiveBody_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; uint8_t v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v_matcherLevels_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_array_get_size(v_motiveArgs_504_);
v___x_656_ = lean_array_get_size(v_discrs_497_);
v___x_657_ = lean_nat_dec_eq(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
lean_dec_ref(v_motiveBody_505_);
lean_dec_ref(v_matcherLevels_503_);
lean_dec_ref(v_params_502_);
lean_dec_ref(v_alts_501_);
lean_dec(v_matcherName_500_);
lean_dec_ref(v_toMatcherInfo_498_);
lean_dec_ref(v_discrs_497_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v___x_658_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_659_ = l_Nat_reprFast(v___x_656_);
v___x_660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
v___x_661_ = l_Lean_MessageData_ofFormat(v___x_660_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_658_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_664_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
else
{
v___y_615_ = v___y_506_;
v___y_616_ = v___y_507_;
v___y_617_ = v___y_508_;
v___y_618_ = v___y_509_;
goto v___jp_614_;
}
v___jp_511_:
{
lean_object* v___x_527_; 
lean_inc(v___y_526_);
lean_inc_ref(v___y_525_);
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
v___x_527_ = lean_infer_type(v___y_515_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref_known(v___x_527_, 1);
v___x_529_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_495_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_514_, v_a_528_, v___x_529_, v___y_521_, v___y_516_, v___x_530_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
lean_dec_ref(v___x_529_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_544_; 
v_a_532_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_544_ == 0)
{
v___x_534_ = v___x_531_;
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_531_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_544_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_542_; 
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_mk_empty_array_with_capacity(v___x_536_);
v___x_538_ = lean_array_push(v___x_537_, v_e_496_);
v___x_539_ = l_Array_append___redArg(v___x_538_, v___y_518_);
v___x_540_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_540_, 0, v___y_513_);
lean_ctor_set(v___x_540_, 1, v___y_520_);
lean_ctor_set(v___x_540_, 2, v___y_512_);
lean_ctor_set(v___x_540_, 3, v___y_522_);
lean_ctor_set(v___x_540_, 4, v___y_519_);
lean_ctor_set(v___x_540_, 5, v___y_517_);
lean_ctor_set(v___x_540_, 6, v_a_532_);
lean_ctor_set(v___x_540_, 7, v___x_539_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_540_);
v___x_542_ = v___x_534_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_540_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v___y_522_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_e_496_);
v_a_545_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_531_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_531_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v_a_553_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_527_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_527_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
v___jp_561_:
{
uint8_t v___x_575_; uint8_t v___x_576_; uint8_t v___x_577_; lean_object* v___x_578_; 
v___x_575_ = 0;
v___x_576_ = 1;
v___x_577_ = 1;
v___x_578_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_504_, v___y_564_, v___x_575_, v___x_576_, v___x_575_, v___x_576_, v___x_577_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc_n(v_a_579_, 2);
lean_dec_ref_known(v___x_578_, 1);
lean_inc_ref(v_matcherLevels_570_);
v___x_580_ = lean_array_to_list(v_matcherLevels_570_);
lean_inc(v___y_567_);
v___x_581_ = l_Lean_mkConst(v___y_567_, v___x_580_);
v___x_582_ = l_Lean_mkAppN(v___x_581_, v___y_569_);
v___x_583_ = l_Lean_Expr_app___override(v___x_582_, v_a_579_);
v___x_584_ = l_Lean_mkAppN(v___x_583_, v___y_565_);
lean_inc_ref(v___x_584_);
v___x_585_ = l_Lean_Meta_isTypeCorrect(v___x_584_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; uint8_t v___x_587_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = lean_unbox(v_a_586_);
lean_dec(v_a_586_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec_ref(v___x_584_);
lean_dec(v_a_579_);
lean_dec_ref(v_matcherLevels_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_565_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v___x_588_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_589_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_588_, v___y_571_, v___y_572_, v___y_573_, v___y_574_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
v___y_512_ = v_matcherLevels_570_;
v___y_513_ = v___y_562_;
v___y_514_ = v___y_563_;
v___y_515_ = v___x_584_;
v___y_516_ = v___x_575_;
v___y_517_ = v___y_565_;
v___y_518_ = v___y_566_;
v___y_519_ = v_a_579_;
v___y_520_ = v___y_567_;
v___y_521_ = v___y_568_;
v___y_522_ = v___y_569_;
v___y_523_ = v___y_571_;
v___y_524_ = v___y_572_;
v___y_525_ = v___y_573_;
v___y_526_ = v___y_574_;
goto v___jp_511_;
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec_ref(v___x_584_);
lean_dec(v_a_579_);
lean_dec_ref(v_matcherLevels_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_565_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v_a_598_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_585_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_585_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_matcherLevels_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_565_);
lean_dec_ref(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v_a_606_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_578_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_578_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
v___jp_614_:
{
lean_object* v___x_619_; 
lean_inc(v___y_618_);
lean_inc_ref(v___y_617_);
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc_ref(v_e_496_);
v___x_619_ = lean_infer_type(v_e_496_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_a_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc_n(v_a_620_, 2);
lean_dec_ref_known(v___x_619_, 1);
v___x_621_ = lean_array_get_size(v_discrs_497_);
v___x_622_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_497_, v_motiveArgs_504_, v___x_621_, v_a_620_);
v___x_623_ = l_Lean_mkArrow(v___x_622_, v_motiveBody_505_, v___y_617_, v___y_618_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_uElimPos_x3f_624_; 
v_uElimPos_x3f_624_ = lean_ctor_get(v_toMatcherInfo_498_, 3);
if (lean_obj_tag(v_uElimPos_x3f_624_) == 0)
{
lean_object* v_a_625_; 
v_a_625_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_a_625_);
lean_dec_ref_known(v___x_623_, 1);
v___y_562_ = v_toMatcherInfo_498_;
v___y_563_ = v_a_620_;
v___y_564_ = v_a_625_;
v___y_565_ = v_discrs_497_;
v___y_566_ = v_remaining_499_;
v___y_567_ = v_matcherName_500_;
v___y_568_ = v_alts_501_;
v___y_569_ = v_params_502_;
v_matcherLevels_570_ = v_matcherLevels_503_;
v___y_571_ = v___y_615_;
v___y_572_ = v___y_616_;
v___y_573_ = v___y_617_;
v___y_574_ = v___y_618_;
goto v___jp_561_;
}
else
{
lean_object* v_a_626_; lean_object* v_val_627_; lean_object* v___x_628_; 
v_a_626_ = lean_ctor_get(v___x_623_, 0);
lean_inc_n(v_a_626_, 2);
lean_dec_ref_known(v___x_623_, 1);
v_val_627_ = lean_ctor_get(v_uElimPos_x3f_624_, 0);
v___x_628_ = l_Lean_Meta_getLevel(v_a_626_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_630_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_a_629_);
lean_dec_ref_known(v___x_628_, 1);
v___x_630_ = lean_array_set(v_matcherLevels_503_, v_val_627_, v_a_629_);
v___y_562_ = v_toMatcherInfo_498_;
v___y_563_ = v_a_620_;
v___y_564_ = v_a_626_;
v___y_565_ = v_discrs_497_;
v___y_566_ = v_remaining_499_;
v___y_567_ = v_matcherName_500_;
v___y_568_ = v_alts_501_;
v___y_569_ = v_params_502_;
v_matcherLevels_570_ = v___x_630_;
v___y_571_ = v___y_615_;
v___y_572_ = v___y_616_;
v___y_573_ = v___y_617_;
v___y_574_ = v___y_618_;
goto v___jp_561_;
}
else
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_638_; 
lean_dec(v_a_626_);
lean_dec(v_a_620_);
lean_dec_ref(v_matcherLevels_503_);
lean_dec_ref(v_params_502_);
lean_dec_ref(v_alts_501_);
lean_dec(v_matcherName_500_);
lean_dec_ref(v_toMatcherInfo_498_);
lean_dec_ref(v_discrs_497_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v_a_631_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_638_ == 0)
{
v___x_633_ = v___x_628_;
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_628_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_638_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_636_; 
if (v_isShared_634_ == 0)
{
v___x_636_ = v___x_633_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_a_631_);
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
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v_a_620_);
lean_dec_ref(v_matcherLevels_503_);
lean_dec_ref(v_params_502_);
lean_dec_ref(v_alts_501_);
lean_dec(v_matcherName_500_);
lean_dec_ref(v_toMatcherInfo_498_);
lean_dec_ref(v_discrs_497_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v_a_639_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_623_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_623_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v_motiveBody_505_);
lean_dec_ref(v_matcherLevels_503_);
lean_dec_ref(v_params_502_);
lean_dec_ref(v_alts_501_);
lean_dec(v_matcherName_500_);
lean_dec_ref(v_toMatcherInfo_498_);
lean_dec_ref(v_discrs_497_);
lean_dec_ref(v_e_496_);
lean_dec_ref(v_matcherApp_495_);
v_a_647_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_619_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_619_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_674_, lean_object* v_e_675_, lean_object* v_discrs_676_, lean_object* v_toMatcherInfo_677_, lean_object* v_remaining_678_, lean_object* v_matcherName_679_, lean_object* v_alts_680_, lean_object* v_params_681_, lean_object* v_matcherLevels_682_, lean_object* v_motiveArgs_683_, lean_object* v_motiveBody_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_674_, v_e_675_, v_discrs_676_, v_toMatcherInfo_677_, v_remaining_678_, v_matcherName_679_, v_alts_680_, v_params_681_, v_matcherLevels_682_, v_motiveArgs_683_, v_motiveBody_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec_ref(v_motiveArgs_683_);
lean_dec_ref(v_remaining_678_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* v_matcherApp_691_, lean_object* v_e_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_toMatcherInfo_698_; lean_object* v_matcherName_699_; lean_object* v_matcherLevels_700_; lean_object* v_params_701_; lean_object* v_motive_702_; lean_object* v_discrs_703_; lean_object* v_alts_704_; lean_object* v_remaining_705_; lean_object* v___f_706_; uint8_t v___x_707_; lean_object* v___x_708_; 
v_toMatcherInfo_698_ = lean_ctor_get(v_matcherApp_691_, 0);
lean_inc_ref(v_toMatcherInfo_698_);
v_matcherName_699_ = lean_ctor_get(v_matcherApp_691_, 1);
lean_inc(v_matcherName_699_);
v_matcherLevels_700_ = lean_ctor_get(v_matcherApp_691_, 2);
lean_inc_ref(v_matcherLevels_700_);
v_params_701_ = lean_ctor_get(v_matcherApp_691_, 3);
lean_inc_ref(v_params_701_);
v_motive_702_ = lean_ctor_get(v_matcherApp_691_, 4);
lean_inc_ref(v_motive_702_);
v_discrs_703_ = lean_ctor_get(v_matcherApp_691_, 5);
lean_inc_ref(v_discrs_703_);
v_alts_704_ = lean_ctor_get(v_matcherApp_691_, 6);
lean_inc_ref(v_alts_704_);
v_remaining_705_ = lean_ctor_get(v_matcherApp_691_, 7);
lean_inc_ref(v_remaining_705_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_706_, 0, v_matcherApp_691_);
lean_closure_set(v___f_706_, 1, v_e_692_);
lean_closure_set(v___f_706_, 2, v_discrs_703_);
lean_closure_set(v___f_706_, 3, v_toMatcherInfo_698_);
lean_closure_set(v___f_706_, 4, v_remaining_705_);
lean_closure_set(v___f_706_, 5, v_matcherName_699_);
lean_closure_set(v___f_706_, 6, v_alts_704_);
lean_closure_set(v___f_706_, 7, v_params_701_);
lean_closure_set(v___f_706_, 8, v_matcherLevels_700_);
v___x_707_ = 0;
v___x_708_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_702_, v___f_706_, v___x_707_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* v_matcherApp_709_, lean_object* v_e_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_709_, v_e_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* v_matcherApp_717_, lean_object* v_e_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_717_, v_e_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_733_; 
v_a_725_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_733_ == 0)
{
v___x_727_ = v___x_724_;
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_724_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_733_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v_a_725_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_749_; 
v_a_734_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_749_ == 0)
{
v___x_736_ = v___x_724_;
v_isShared_737_ = v_isSharedCheck_749_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_724_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_749_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___y_739_; uint8_t v___x_747_; 
v___x_747_ = l_Lean_Exception_isInterrupt(v_a_734_);
if (v___x_747_ == 0)
{
uint8_t v___x_748_; 
lean_inc(v_a_734_);
v___x_748_ = l_Lean_Exception_isRuntime(v_a_734_);
v___y_739_ = v___x_748_;
goto v___jp_738_;
}
else
{
v___y_739_ = v___x_747_;
goto v___jp_738_;
}
v___jp_738_:
{
if (v___y_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_742_; 
lean_dec(v_a_734_);
v___x_740_ = lean_box(0);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
lean_ctor_set(v___x_736_, 0, v___x_740_);
v___x_742_ = v___x_736_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_740_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
}
}
else
{
lean_object* v___x_745_; 
if (v_isShared_737_ == 0)
{
v___x_745_ = v___x_736_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_734_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* v_matcherApp_750_, lean_object* v_e_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_750_, v_e_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(lean_object* v_type_758_, lean_object* v_maxFVars_x3f_759_, lean_object* v_k_760_, uint8_t v_cleanupAnnotations_761_, uint8_t v_whnfType_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___f_768_; lean_object* v___x_769_; 
v___f_768_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_768_, 0, v_k_760_);
v___x_769_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_758_, v_maxFVars_x3f_759_, v___f_768_, v_cleanupAnnotations_761_, v_whnfType_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
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
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
v_a_778_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_769_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_769_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg___boxed(lean_object* v_type_786_, lean_object* v_maxFVars_x3f_787_, lean_object* v_k_788_, lean_object* v_cleanupAnnotations_789_, lean_object* v_whnfType_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_796_; uint8_t v_whnfType_boxed_797_; lean_object* v_res_798_; 
v_cleanupAnnotations_boxed_796_ = lean_unbox(v_cleanupAnnotations_789_);
v_whnfType_boxed_797_ = lean_unbox(v_whnfType_790_);
v_res_798_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_786_, v_maxFVars_x3f_787_, v_k_788_, v_cleanupAnnotations_boxed_796_, v_whnfType_boxed_797_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(lean_object* v_00_u03b1_799_, lean_object* v_type_800_, lean_object* v_maxFVars_x3f_801_, lean_object* v_k_802_, uint8_t v_cleanupAnnotations_803_, uint8_t v_whnfType_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; 
v___x_810_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_800_, v_maxFVars_x3f_801_, v_k_802_, v_cleanupAnnotations_803_, v_whnfType_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* v_00_u03b1_811_, lean_object* v_type_812_, lean_object* v_maxFVars_x3f_813_, lean_object* v_k_814_, lean_object* v_cleanupAnnotations_815_, lean_object* v_whnfType_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_822_; uint8_t v_whnfType_boxed_823_; lean_object* v_res_824_; 
v_cleanupAnnotations_boxed_822_ = lean_unbox(v_cleanupAnnotations_815_);
v_whnfType_boxed_823_ = lean_unbox(v_whnfType_816_);
v_res_824_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_00_u03b1_811_, v_type_812_, v_maxFVars_x3f_813_, v_k_814_, v_cleanupAnnotations_boxed_822_, v_whnfType_boxed_823_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(lean_object* v_type_825_, lean_object* v_k_826_, uint8_t v_cleanupAnnotations_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___f_833_; uint8_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___f_833_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_833_, 0, v_k_826_);
v___x_834_ = 0;
v___x_835_ = lean_box(0);
v___x_836_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_834_, v___x_835_, v_type_825_, v___f_833_, v_cleanupAnnotations_827_, v___x_834_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_836_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_836_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_836_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_836_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg___boxed(lean_object* v_type_853_, lean_object* v_k_854_, lean_object* v_cleanupAnnotations_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_861_; lean_object* v_res_862_; 
v_cleanupAnnotations_boxed_861_ = lean_unbox(v_cleanupAnnotations_855_);
v_res_862_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_853_, v_k_854_, v_cleanupAnnotations_boxed_861_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(lean_object* v_00_u03b1_863_, lean_object* v_type_864_, lean_object* v_k_865_, uint8_t v_cleanupAnnotations_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_864_, v_k_865_, v_cleanupAnnotations_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___boxed(lean_object* v_00_u03b1_873_, lean_object* v_type_874_, lean_object* v_k_875_, lean_object* v_cleanupAnnotations_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_882_; lean_object* v_res_883_; 
v_cleanupAnnotations_boxed_882_ = lean_unbox(v_cleanupAnnotations_876_);
v_res_883_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(v_00_u03b1_873_, v_type_874_, v_k_875_, v_cleanupAnnotations_boxed_882_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(size_t v_sz_884_, size_t v_i_885_, lean_object* v_bs_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = lean_usize_dec_lt(v_i_885_, v_sz_884_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v_bs_886_);
return v___x_893_;
}
else
{
lean_object* v_v_894_; lean_object* v___x_895_; lean_object* v_bs_x27_896_; lean_object* v___x_897_; 
v_v_894_ = lean_array_uget(v_bs_886_, v_i_885_);
v___x_895_ = lean_unsigned_to_nat(0u);
v_bs_x27_896_ = lean_array_uset(v_bs_886_, v_i_885_, v___x_895_);
lean_inc(v___y_890_);
lean_inc_ref(v___y_889_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
v___x_897_ = lean_infer_type(v_v_894_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; size_t v___x_899_; size_t v___x_900_; lean_object* v___x_901_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = ((size_t)1ULL);
v___x_900_ = lean_usize_add(v_i_885_, v___x_899_);
v___x_901_ = lean_array_uset(v_bs_x27_896_, v_i_885_, v_a_898_);
v_i_885_ = v___x_900_;
v_bs_886_ = v___x_901_;
goto _start;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v_bs_x27_896_);
v_a_903_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_897_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_897_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* v_sz_911_, lean_object* v_i_912_, lean_object* v_bs_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_911_);
lean_dec(v_sz_911_);
v_i_boxed_920_ = lean_unbox_usize(v_i_912_);
lean_dec(v_i_912_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_boxed_919_, v_i_boxed_920_, v_bs_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_);
lean_dec(v___y_917_);
lean_dec_ref(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
return v_res_921_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__0));
v___x_924_ = l_Lean_stringToMessageData(v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(uint8_t v___x_925_, uint8_t v___x_926_, uint8_t v___x_927_, lean_object* v_a_928_, lean_object* v_fvs_929_, lean_object* v_body_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_array_get_size(v_fvs_929_);
v___x_945_ = lean_nat_dec_eq(v___x_944_, v_a_928_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
v___x_946_ = lean_obj_once(&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1, &l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1);
v___x_947_ = l_Nat_reprFast(v_a_928_);
v___x_948_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
v___x_949_ = l_Lean_MessageData_ofFormat(v___x_948_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_946_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_950_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_952_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
else
{
lean_dec(v_a_928_);
goto v___jp_936_;
}
v___jp_936_:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_937_ = lean_unsigned_to_nat(2u);
v___x_938_ = l_Lean_Expr_getAppNumArgs(v_body_930_);
v___x_939_ = lean_nat_sub(v___x_938_, v___x_937_);
lean_dec(v___x_938_);
v___x_940_ = lean_unsigned_to_nat(1u);
v___x_941_ = lean_nat_sub(v___x_939_, v___x_940_);
lean_dec(v___x_939_);
v___x_942_ = l_Lean_Expr_getRevArg_x21(v_body_930_, v___x_941_);
v___x_943_ = l_Lean_Meta_mkLambdaFVars(v_fvs_929_, v___x_942_, v___x_925_, v___x_926_, v___x_925_, v___x_926_, v___x_927_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed(lean_object* v___x_962_, lean_object* v___x_963_, lean_object* v___x_964_, lean_object* v_a_965_, lean_object* v_fvs_966_, lean_object* v_body_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_4175__boxed_973_; uint8_t v___x_4176__boxed_974_; uint8_t v___x_4177__boxed_975_; lean_object* v_res_976_; 
v___x_4175__boxed_973_ = lean_unbox(v___x_962_);
v___x_4176__boxed_974_ = lean_unbox(v___x_963_);
v___x_4177__boxed_975_ = lean_unbox(v___x_964_);
v_res_976_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(v___x_4175__boxed_973_, v___x_4176__boxed_974_, v___x_4177__boxed_975_, v_a_965_, v_fvs_966_, v_body_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec_ref(v_body_967_);
lean_dec_ref(v_fvs_966_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* v_as_977_, lean_object* v_bs_978_, lean_object* v_i_979_, lean_object* v_cs_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_array_get_size(v_as_977_);
v___x_987_ = lean_nat_dec_lt(v_i_979_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v_i_979_);
v___x_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_988_, 0, v_cs_980_);
return v___x_988_;
}
else
{
lean_object* v___x_989_; uint8_t v___x_990_; 
v___x_989_ = lean_array_get_size(v_bs_978_);
v___x_990_ = lean_nat_dec_lt(v_i_979_, v___x_989_);
if (v___x_990_ == 0)
{
lean_object* v___x_991_; 
lean_dec(v_i_979_);
v___x_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_991_, 0, v_cs_980_);
return v___x_991_;
}
else
{
uint8_t v___x_992_; uint8_t v___x_993_; lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v_b_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_992_ = 0;
v___x_993_ = 1;
v_a_994_ = lean_array_fget_borrowed(v_as_977_, v_i_979_);
v___x_995_ = lean_box(v___x_992_);
v___x_996_ = lean_box(v___x_990_);
v___x_997_ = lean_box(v___x_993_);
lean_inc_n(v_a_994_, 2);
v___f_998_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed), 11, 4);
lean_closure_set(v___f_998_, 0, v___x_995_);
lean_closure_set(v___f_998_, 1, v___x_996_);
lean_closure_set(v___f_998_, 2, v___x_997_);
lean_closure_set(v___f_998_, 3, v_a_994_);
v_b_999_ = lean_array_fget_borrowed(v_bs_978_, v_i_979_);
v___x_1000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1000_, 0, v_a_994_);
lean_inc(v_b_999_);
v___x_1001_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_b_999_, v___x_1000_, v___f_998_, v___x_992_, v___x_992_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_add(v_i_979_, v___x_1003_);
lean_dec(v_i_979_);
v___x_1005_ = lean_array_push(v_cs_980_, v_a_1002_);
v_i_979_ = v___x_1004_;
v_cs_980_ = v___x_1005_;
goto _start;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_cs_980_);
lean_dec(v_i_979_);
v_a_1007_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1001_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1001_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* v_as_1015_, lean_object* v_bs_1016_, lean_object* v_i_1017_, lean_object* v_cs_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_as_1015_, v_bs_1016_, v_i_1017_, v_cs_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec_ref(v_bs_1016_);
lean_dec_ref(v_as_1015_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* v_matcherApp_1027_, lean_object* v_altAuxs_1028_, lean_object* v_x_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_1037_; 
v_sz_1035_ = lean_array_size(v_altAuxs_1028_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_1035_, v___x_1036_, v_altAuxs_1028_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v___x_1037_, 1);
v___x_1039_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_1027_);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_1042_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v___x_1039_, v_a_1038_, v___x_1040_, v___x_1041_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
lean_dec(v_a_1038_);
lean_dec_ref(v___x_1039_);
return v___x_1042_;
}
else
{
lean_dec_ref(v_matcherApp_1027_);
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* v_matcherApp_1043_, lean_object* v_altAuxs_1044_, lean_object* v_x_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1043_, v_altAuxs_1044_, v_x_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v_x_1045_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* v_motiveArgs_1052_, lean_object* v___x_1053_, lean_object* v_i_1054_, lean_object* v_a_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_zero_1061_; uint8_t v_isZero_1062_; 
v_zero_1061_ = lean_unsigned_to_nat(0u);
v_isZero_1062_ = lean_nat_dec_eq(v_i_1054_, v_zero_1061_);
if (v_isZero_1062_ == 1)
{
lean_object* v___x_1063_; 
lean_dec(v_i_1054_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v_a_1055_);
return v___x_1063_;
}
else
{
lean_object* v___x_1064_; lean_object* v_one_1065_; lean_object* v_n_1066_; lean_object* v_motiveArg_1067_; lean_object* v_discr_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1064_ = l_Lean_instInhabitedExpr;
v_one_1065_ = lean_unsigned_to_nat(1u);
v_n_1066_ = lean_nat_sub(v_i_1054_, v_one_1065_);
lean_dec(v_i_1054_);
v_motiveArg_1067_ = lean_array_get_borrowed(v___x_1064_, v_motiveArgs_1052_, v_n_1066_);
v_discr_1068_ = lean_array_fget_borrowed(v___x_1053_, v_n_1066_);
v___x_1069_ = lean_box(0);
lean_inc(v_discr_1068_);
v___x_1070_ = l_Lean_Meta_kabstract(v_a_1055_, v_discr_1068_, v___x_1069_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1071_; lean_object* v___x_1072_; 
v_a_1071_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1071_);
lean_dec_ref_known(v___x_1070_, 1);
v___x_1072_ = lean_expr_instantiate1(v_a_1071_, v_motiveArg_1067_);
lean_dec(v_a_1071_);
v_i_1054_ = v_n_1066_;
v_a_1055_ = v___x_1072_;
goto _start;
}
else
{
if (lean_obj_tag(v___x_1070_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___x_1070_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1070_, 1);
v_i_1054_ = v_n_1066_;
v_a_1055_ = v_a_1074_;
goto _start;
}
else
{
lean_dec(v_n_1066_);
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* v_motiveArgs_1076_, lean_object* v___x_1077_, lean_object* v_i_1078_, lean_object* v_a_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1076_, v___x_1077_, v_i_1078_, v_a_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec_ref(v___x_1077_);
lean_dec_ref(v_motiveArgs_1076_);
return v_res_1085_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1092_, lean_object* v_discrs_1093_, lean_object* v_e_1094_, lean_object* v_toMatcherInfo_1095_, lean_object* v_params_1096_, lean_object* v_matcherName_1097_, lean_object* v_matcherLevels_1098_, lean_object* v_motiveArgs_1099_, lean_object* v___motiveBody_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v_matcherLevels_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___x_1205_; lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_array_get_size(v_motiveArgs_1099_);
v___x_1206_ = lean_array_get_size(v_discrs_1093_);
v___x_1207_ = lean_nat_dec_eq(v___x_1205_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v_matcherLevels_1098_);
lean_dec(v_matcherName_1097_);
lean_dec_ref(v_e_1094_);
lean_dec_ref(v___f_1092_);
v___x_1208_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
v___x_1209_ = l_Nat_reprFast(v___x_1206_);
v___x_1210_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
v___x_1211_ = l_Lean_MessageData_ofFormat(v___x_1210_);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1208_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_1214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1212_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
v___x_1215_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1214_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1215_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
v___y_1175_ = v___y_1101_;
v___y_1176_ = v___y_1102_;
v___y_1177_ = v___y_1103_;
v___y_1178_ = v___y_1104_;
goto v___jp_1174_;
}
v___jp_1106_:
{
lean_object* v___x_1114_; 
lean_inc(v___y_1113_);
lean_inc_ref(v___y_1112_);
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
v___x_1114_ = lean_infer_type(v___y_1108_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_a_1115_, v___y_1109_, v___y_1107_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1116_;
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v___y_1109_);
v_a_1117_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1114_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1114_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
v___jp_1125_:
{
uint8_t v___x_1135_; uint8_t v___x_1136_; uint8_t v___x_1137_; lean_object* v___x_1138_; 
v___x_1135_ = 0;
v___x_1136_ = 1;
v___x_1137_ = 1;
v___x_1138_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1099_, v___y_1126_, v___x_1135_, v___x_1136_, v___x_1135_, v___x_1136_, v___x_1137_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v___x_1140_ = lean_array_to_list(v_matcherLevels_1130_);
v___x_1141_ = l_Lean_mkConst(v___y_1129_, v___x_1140_);
v___x_1142_ = l_Lean_mkAppN(v___x_1141_, v___y_1127_);
v___x_1143_ = l_Lean_Expr_app___override(v___x_1142_, v_a_1139_);
v___x_1144_ = l_Lean_mkAppN(v___x_1143_, v___y_1128_);
lean_inc_ref(v___x_1144_);
v___x_1145_ = l_Lean_Meta_isTypeCorrect(v___x_1144_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; uint8_t v___x_1147_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v___x_1147_ = lean_unbox(v_a_1146_);
lean_dec(v_a_1146_);
if (v___x_1147_ == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___f_1092_);
v___x_1148_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
v___x_1149_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1148_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
v___y_1107_ = v___x_1135_;
v___y_1108_ = v___x_1144_;
v___y_1109_ = v___f_1092_;
v___y_1110_ = v___y_1131_;
v___y_1111_ = v___y_1132_;
v___y_1112_ = v___y_1133_;
v___y_1113_ = v___y_1134_;
goto v___jp_1106_;
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v___x_1144_);
lean_dec_ref(v___f_1092_);
v_a_1158_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1145_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1145_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_matcherLevels_1130_);
lean_dec(v___y_1129_);
lean_dec_ref(v___f_1092_);
v_a_1166_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1138_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1138_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
v___jp_1174_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_array_get_size(v_discrs_1093_);
v___x_1180_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1099_, v_discrs_1093_, v___x_1179_, v_e_1094_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v___x_1182_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc_n(v_a_1181_, 2);
lean_dec_ref_known(v___x_1180_, 1);
v___x_1182_ = l_Lean_Meta_mkEq(v_a_1181_, v_a_1181_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_uElimPos_x3f_1183_; 
v_uElimPos_x3f_1183_ = lean_ctor_get(v_toMatcherInfo_1095_, 3);
if (lean_obj_tag(v_uElimPos_x3f_1183_) == 0)
{
lean_object* v_a_1184_; 
v_a_1184_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1182_, 1);
v___y_1126_ = v_a_1184_;
v___y_1127_ = v_params_1096_;
v___y_1128_ = v_discrs_1093_;
v___y_1129_ = v_matcherName_1097_;
v_matcherLevels_1130_ = v_matcherLevels_1098_;
v___y_1131_ = v___y_1175_;
v___y_1132_ = v___y_1176_;
v___y_1133_ = v___y_1177_;
v___y_1134_ = v___y_1178_;
goto v___jp_1125_;
}
else
{
lean_object* v_a_1185_; lean_object* v_val_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v_a_1185_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1182_, 1);
v_val_1186_ = lean_ctor_get(v_uElimPos_x3f_1183_, 0);
v___x_1187_ = lean_box(0);
v___x_1188_ = lean_array_set(v_matcherLevels_1098_, v_val_1186_, v___x_1187_);
v___y_1126_ = v_a_1185_;
v___y_1127_ = v_params_1096_;
v___y_1128_ = v_discrs_1093_;
v___y_1129_ = v_matcherName_1097_;
v_matcherLevels_1130_ = v___x_1188_;
v___y_1131_ = v___y_1175_;
v___y_1132_ = v___y_1176_;
v___y_1133_ = v___y_1177_;
v___y_1134_ = v___y_1178_;
goto v___jp_1125_;
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec_ref(v_matcherLevels_1098_);
lean_dec(v_matcherName_1097_);
lean_dec_ref(v___f_1092_);
v_a_1189_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1182_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1182_);
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
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec_ref(v_matcherLevels_1098_);
lean_dec(v_matcherName_1097_);
lean_dec_ref(v___f_1092_);
v_a_1197_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1180_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1180_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1224_, lean_object* v_discrs_1225_, lean_object* v_e_1226_, lean_object* v_toMatcherInfo_1227_, lean_object* v_params_1228_, lean_object* v_matcherName_1229_, lean_object* v_matcherLevels_1230_, lean_object* v_motiveArgs_1231_, lean_object* v___motiveBody_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1224_, v_discrs_1225_, v_e_1226_, v_toMatcherInfo_1227_, v_params_1228_, v_matcherName_1229_, v_matcherLevels_1230_, v_motiveArgs_1231_, v___motiveBody_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec_ref(v___motiveBody_1232_);
lean_dec_ref(v_motiveArgs_1231_);
lean_dec_ref(v_params_1228_);
lean_dec_ref(v_toMatcherInfo_1227_);
lean_dec_ref(v_discrs_1225_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* v_matcherApp_1239_, lean_object* v_e_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_toMatcherInfo_1246_; lean_object* v_matcherName_1247_; lean_object* v_matcherLevels_1248_; lean_object* v_params_1249_; lean_object* v_motive_1250_; lean_object* v_discrs_1251_; lean_object* v___f_1252_; lean_object* v___f_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; 
v_toMatcherInfo_1246_ = lean_ctor_get(v_matcherApp_1239_, 0);
lean_inc_ref(v_toMatcherInfo_1246_);
v_matcherName_1247_ = lean_ctor_get(v_matcherApp_1239_, 1);
lean_inc(v_matcherName_1247_);
v_matcherLevels_1248_ = lean_ctor_get(v_matcherApp_1239_, 2);
lean_inc_ref(v_matcherLevels_1248_);
v_params_1249_ = lean_ctor_get(v_matcherApp_1239_, 3);
lean_inc_ref(v_params_1249_);
v_motive_1250_ = lean_ctor_get(v_matcherApp_1239_, 4);
lean_inc_ref(v_motive_1250_);
v_discrs_1251_ = lean_ctor_get(v_matcherApp_1239_, 5);
lean_inc_ref(v_discrs_1251_);
v___f_1252_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1252_, 0, v_matcherApp_1239_);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1253_, 0, v___f_1252_);
lean_closure_set(v___f_1253_, 1, v_discrs_1251_);
lean_closure_set(v___f_1253_, 2, v_e_1240_);
lean_closure_set(v___f_1253_, 3, v_toMatcherInfo_1246_);
lean_closure_set(v___f_1253_, 4, v_params_1249_);
lean_closure_set(v___f_1253_, 5, v_matcherName_1247_);
lean_closure_set(v___f_1253_, 6, v_matcherLevels_1248_);
v___x_1254_ = 0;
v___x_1255_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_1250_, v___f_1253_, v___x_1254_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* v_matcherApp_1256_, lean_object* v_e_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1256_, v_e_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* v_motiveArgs_1264_, lean_object* v___x_1265_, lean_object* v_n_1266_, lean_object* v_i_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v___x_1275_; 
v___x_1275_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1264_, v___x_1265_, v_i_1267_, v_a_1269_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* v_motiveArgs_1276_, lean_object* v___x_1277_, lean_object* v_n_1278_, lean_object* v_i_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v_motiveArgs_1276_, v___x_1277_, v_n_1278_, v_i_1279_, v_a_1280_, v_a_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v_n_1278_);
lean_dec_ref(v___x_1277_);
lean_dec_ref(v_motiveArgs_1276_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* v_matcherApp_1288_, lean_object* v_e_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1288_, v_e_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1304_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1304_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1304_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_a_1296_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1300_);
v___x_1302_ = v___x_1298_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1320_; 
v_a_1305_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1307_ = v___x_1295_;
v_isShared_1308_ = v_isSharedCheck_1320_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1295_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1320_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
uint8_t v___y_1310_; uint8_t v___x_1318_; 
v___x_1318_ = l_Lean_Exception_isInterrupt(v_a_1305_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1319_; 
lean_inc(v_a_1305_);
v___x_1319_ = l_Lean_Exception_isRuntime(v_a_1305_);
v___y_1310_ = v___x_1319_;
goto v___jp_1309_;
}
else
{
v___y_1310_ = v___x_1318_;
goto v___jp_1309_;
}
v___jp_1309_:
{
if (v___y_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec(v_a_1305_);
v___x_1311_ = lean_box(0);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1311_);
v___x_1313_ = v___x_1307_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
else
{
lean_object* v___x_1316_; 
if (v_isShared_1308_ == 0)
{
v___x_1316_ = v___x_1307_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1305_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* v_matcherApp_1321_, lean_object* v_e_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1321_, v_e_1322_, v_a_1323_, v_a_1324_, v_a_1325_, v_a_1326_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1329_, lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_keyedConfig_1336_; uint8_t v_trackZetaDelta_1337_; lean_object* v_zetaDeltaSet_1338_; lean_object* v_localInstances_1339_; lean_object* v_defEqCtx_x3f_1340_; lean_object* v_synthPendingDepth_1341_; lean_object* v_customCanUnfoldPredicate_x3f_1342_; uint8_t v_univApprox_1343_; uint8_t v_inTypeClassResolution_1344_; uint8_t v_cacheInferType_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v_keyedConfig_1336_ = lean_ctor_get(v___y_1331_, 0);
v_trackZetaDelta_1337_ = lean_ctor_get_uint8(v___y_1331_, sizeof(void*)*7);
v_zetaDeltaSet_1338_ = lean_ctor_get(v___y_1331_, 1);
v_localInstances_1339_ = lean_ctor_get(v___y_1331_, 3);
v_defEqCtx_x3f_1340_ = lean_ctor_get(v___y_1331_, 4);
v_synthPendingDepth_1341_ = lean_ctor_get(v___y_1331_, 5);
v_customCanUnfoldPredicate_x3f_1342_ = lean_ctor_get(v___y_1331_, 6);
v_univApprox_1343_ = lean_ctor_get_uint8(v___y_1331_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1344_ = lean_ctor_get_uint8(v___y_1331_, sizeof(void*)*7 + 2);
v_cacheInferType_1345_ = lean_ctor_get_uint8(v___y_1331_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1342_);
lean_inc(v_synthPendingDepth_1341_);
lean_inc(v_defEqCtx_x3f_1340_);
lean_inc_ref(v_localInstances_1339_);
lean_inc(v_zetaDeltaSet_1338_);
lean_inc_ref(v_keyedConfig_1336_);
v___x_1346_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1346_, 0, v_keyedConfig_1336_);
lean_ctor_set(v___x_1346_, 1, v_zetaDeltaSet_1338_);
lean_ctor_set(v___x_1346_, 2, v_lctx_1329_);
lean_ctor_set(v___x_1346_, 3, v_localInstances_1339_);
lean_ctor_set(v___x_1346_, 4, v_defEqCtx_x3f_1340_);
lean_ctor_set(v___x_1346_, 5, v_synthPendingDepth_1341_);
lean_ctor_set(v___x_1346_, 6, v_customCanUnfoldPredicate_x3f_1342_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*7, v_trackZetaDelta_1337_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*7 + 1, v_univApprox_1343_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1344_);
lean_ctor_set_uint8(v___x_1346_, sizeof(void*)*7 + 3, v_cacheInferType_1345_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
lean_inc(v___y_1332_);
v___x_1347_ = lean_apply_5(v_x_1330_, v___x_1346_, v___y_1332_, v___y_1333_, v___y_1334_, lean_box(0));
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1348_, lean_object* v_x_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1348_, v_x_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1356_, lean_object* v_lctx_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1357_, v_x_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_lctx_1366_, lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1365_, v_lctx_1366_, v_x_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1374_, size_t v_i_1375_, size_t v_stop_1376_, lean_object* v_b_1377_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_eq(v_i_1375_, v_stop_1376_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; size_t v___x_1384_; size_t v___x_1385_; 
v___x_1379_ = lean_array_uget_borrowed(v_as_1374_, v_i_1375_);
v_fst_1380_ = lean_ctor_get(v___x_1379_, 0);
v_snd_1381_ = lean_ctor_get(v___x_1379_, 1);
v___x_1382_ = l_Lean_Expr_fvarId_x21(v_fst_1380_);
lean_inc(v_snd_1381_);
v___x_1383_ = l_Lean_LocalContext_setUserName(v_b_1377_, v___x_1382_, v_snd_1381_);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_add(v_i_1375_, v___x_1384_);
v_i_1375_ = v___x_1385_;
v_b_1377_ = v___x_1383_;
goto _start;
}
else
{
return v_b_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1387_, lean_object* v_i_1388_, lean_object* v_stop_1389_, lean_object* v_b_1390_){
_start:
{
size_t v_i_boxed_1391_; size_t v_stop_boxed_1392_; lean_object* v_res_1393_; 
v_i_boxed_1391_ = lean_unbox_usize(v_i_1388_);
lean_dec(v_i_1388_);
v_stop_boxed_1392_ = lean_unbox_usize(v_stop_1389_);
lean_dec(v_stop_1389_);
v_res_1393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1387_, v_i_boxed_1391_, v_stop_boxed_1392_, v_b_1390_);
lean_dec_ref(v_as_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1394_, lean_object* v_names_1395_, lean_object* v_k_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_lctx_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_lctx_1402_ = lean_ctor_get(v_a_1397_, 2);
v___x_1403_ = l_Array_zip___redArg(v_fvars_1394_, v_names_1395_);
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_array_get_size(v___x_1403_);
v___x_1406_ = lean_nat_dec_lt(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_dec_ref(v___x_1403_);
lean_inc_ref(v_lctx_1402_);
v___x_1407_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1402_, v_k_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
return v___x_1407_;
}
else
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_le(v___x_1405_, v___x_1405_);
if (v___x_1408_ == 0)
{
if (v___x_1406_ == 0)
{
lean_object* v___x_1409_; 
lean_dec_ref(v___x_1403_);
lean_inc_ref(v_lctx_1402_);
v___x_1409_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1402_, v_k_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
return v___x_1409_;
}
else
{
size_t v___x_1410_; size_t v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = ((size_t)0ULL);
v___x_1411_ = lean_usize_of_nat(v___x_1405_);
lean_inc_ref(v_lctx_1402_);
v___x_1412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1403_, v___x_1410_, v___x_1411_, v_lctx_1402_);
lean_dec_ref(v___x_1403_);
v___x_1413_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1412_, v_k_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
return v___x_1413_;
}
}
else
{
size_t v___x_1414_; size_t v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = ((size_t)0ULL);
v___x_1415_ = lean_usize_of_nat(v___x_1405_);
lean_inc_ref(v_lctx_1402_);
v___x_1416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1403_, v___x_1414_, v___x_1415_, v_lctx_1402_);
lean_dec_ref(v___x_1403_);
v___x_1417_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1416_, v_k_1396_, v_a_1397_, v_a_1398_, v_a_1399_, v_a_1400_);
return v___x_1417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* v_fvars_1418_, lean_object* v_names_1419_, lean_object* v_k_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_, lean_object* v_a_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1418_, v_names_1419_, v_k_1420_, v_a_1421_, v_a_1422_, v_a_1423_, v_a_1424_);
lean_dec(v_a_1424_);
lean_dec_ref(v_a_1423_);
lean_dec(v_a_1422_);
lean_dec_ref(v_a_1421_);
lean_dec_ref(v_names_1419_);
lean_dec_ref(v_fvars_1418_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* v_00_u03b1_1427_, lean_object* v_fvars_1428_, lean_object* v_names_1429_, lean_object* v_k_1430_, lean_object* v_a_1431_, lean_object* v_a_1432_, lean_object* v_a_1433_, lean_object* v_a_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1428_, v_names_1429_, v_k_1430_, v_a_1431_, v_a_1432_, v_a_1433_, v_a_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_fvars_1438_, lean_object* v_names_1439_, lean_object* v_k_1440_, lean_object* v_a_1441_, lean_object* v_a_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(v_00_u03b1_1437_, v_fvars_1438_, v_names_1439_, v_k_1440_, v_a_1441_, v_a_1442_, v_a_1443_, v_a_1444_);
lean_dec(v_a_1444_);
lean_dec_ref(v_a_1443_);
lean_dec(v_a_1442_);
lean_dec_ref(v_a_1441_);
lean_dec_ref(v_names_1439_);
lean_dec_ref(v_fvars_1438_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* v_k_1447_, lean_object* v_fvars_1448_, lean_object* v_names_1449_, lean_object* v_runInBase_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = lean_apply_2(v_runInBase_1450_, lean_box(0), v_k_1447_);
v___x_1457_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1448_, v_names_1449_, v___x_1456_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* v_k_1458_, lean_object* v_fvars_1459_, lean_object* v_names_1460_, lean_object* v_runInBase_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1458_, v_fvars_1459_, v_names_1460_, v_runInBase_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec_ref(v_names_1460_);
lean_dec_ref(v_fvars_1459_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* v_inst_1468_, lean_object* v_inst_1469_, lean_object* v_fvars_1470_, lean_object* v_names_1471_, lean_object* v_k_1472_){
_start:
{
lean_object* v_toBind_1473_; lean_object* v_liftWith_1474_; lean_object* v_restoreM_1475_; lean_object* v___f_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_toBind_1473_ = lean_ctor_get(v_inst_1469_, 1);
lean_inc(v_toBind_1473_);
lean_dec_ref(v_inst_1469_);
v_liftWith_1474_ = lean_ctor_get(v_inst_1468_, 0);
lean_inc(v_liftWith_1474_);
v_restoreM_1475_ = lean_ctor_get(v_inst_1468_, 1);
lean_inc(v_restoreM_1475_);
lean_dec_ref(v_inst_1468_);
v___f_1476_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1476_, 0, v_k_1472_);
lean_closure_set(v___f_1476_, 1, v_fvars_1470_);
lean_closure_set(v___f_1476_, 2, v_names_1471_);
v___x_1477_ = lean_apply_2(v_liftWith_1474_, lean_box(0), v___f_1476_);
v___x_1478_ = lean_apply_1(v_restoreM_1475_, lean_box(0));
v___x_1479_ = lean_apply_4(v_toBind_1473_, lean_box(0), lean_box(0), v___x_1477_, v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* v_n_1480_, lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_00_u03b1_1483_, lean_object* v_fvars_1484_, lean_object* v_names_1485_, lean_object* v_k_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_1481_, v_inst_1482_, v_fvars_1484_, v_names_1485_, v_k_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* v_k_1488_, lean_object* v_runInBase_1489_, lean_object* v_ys_1490_, lean_object* v_args_1491_, lean_object* v___mask_1492_, lean_object* v___bodyType_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = lean_apply_2(v_k_1488_, v_ys_1490_, v_args_1491_);
lean_inc(v___y_1497_);
lean_inc_ref(v___y_1496_);
lean_inc(v___y_1495_);
lean_inc_ref(v___y_1494_);
v___x_1500_ = lean_apply_7(v_runInBase_1489_, lean_box(0), v___x_1499_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, lean_box(0));
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* v_k_1501_, lean_object* v_runInBase_1502_, lean_object* v_ys_1503_, lean_object* v_args_1504_, lean_object* v___mask_1505_, lean_object* v___bodyType_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1501_, v_runInBase_1502_, v_ys_1503_, v_args_1504_, v___mask_1505_, v___bodyType_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec_ref(v___bodyType_1506_);
lean_dec_ref(v___mask_1505_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* v_k_1513_, lean_object* v_origAltType_1514_, lean_object* v_altInfo_1515_, lean_object* v_runInBase_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v___f_1522_; lean_object* v___x_1523_; 
v___f_1522_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1522_, 0, v_k_1513_);
lean_closure_set(v___f_1522_, 1, v_runInBase_1516_);
v___x_1523_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_1514_, v_altInfo_1515_, v___f_1522_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* v_k_1524_, lean_object* v_origAltType_1525_, lean_object* v_altInfo_1526_, lean_object* v_runInBase_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1524_, v_origAltType_1525_, v_altInfo_1526_, v_runInBase_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* v_inst_1534_, lean_object* v_inst_1535_, lean_object* v_origAltType_1536_, lean_object* v_altInfo_1537_, lean_object* v_k_1538_){
_start:
{
lean_object* v_toBind_1539_; lean_object* v_liftWith_1540_; lean_object* v_restoreM_1541_; lean_object* v___f_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v_toBind_1539_ = lean_ctor_get(v_inst_1534_, 1);
lean_inc(v_toBind_1539_);
lean_dec_ref(v_inst_1534_);
v_liftWith_1540_ = lean_ctor_get(v_inst_1535_, 0);
lean_inc(v_liftWith_1540_);
v_restoreM_1541_ = lean_ctor_get(v_inst_1535_, 1);
lean_inc(v_restoreM_1541_);
lean_dec_ref(v_inst_1535_);
v___f_1542_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1542_, 0, v_k_1538_);
lean_closure_set(v___f_1542_, 1, v_origAltType_1536_);
lean_closure_set(v___f_1542_, 2, v_altInfo_1537_);
v___x_1543_ = lean_apply_2(v_liftWith_1540_, lean_box(0), v___f_1542_);
v___x_1544_ = lean_apply_1(v_restoreM_1541_, lean_box(0));
v___x_1545_ = lean_apply_4(v_toBind_1539_, lean_box(0), lean_box(0), v___x_1543_, v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* v_n_1546_, lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_00_u03b1_1549_, lean_object* v_origAltType_1550_, lean_object* v_altInfo_1551_, lean_object* v_k_1552_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_1547_, v_inst_1548_, v_origAltType_1550_, v_altInfo_1551_, v_k_1552_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object* v_fvars_1554_){
_start:
{
lean_object* v_args_1555_; lean_object* v_discrEqs_1556_; lean_object* v___x_1557_; 
v_args_1555_ = lean_ctor_get(v_fvars_1554_, 0);
lean_inc_ref(v_args_1555_);
v_discrEqs_1556_ = lean_ctor_get(v_fvars_1554_, 3);
lean_inc_ref(v_discrEqs_1556_);
lean_dec_ref(v_fvars_1554_);
v___x_1557_ = l_Array_append___redArg(v_args_1555_, v_discrEqs_1556_);
lean_dec_ref(v_discrEqs_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object* v_fvars_1558_){
_start:
{
lean_object* v_fields_1559_; lean_object* v_overlaps_1560_; lean_object* v_discrEqs_1561_; lean_object* v_extraEqs_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_fields_1559_ = lean_ctor_get(v_fvars_1558_, 1);
lean_inc_ref(v_fields_1559_);
v_overlaps_1560_ = lean_ctor_get(v_fvars_1558_, 2);
lean_inc_ref(v_overlaps_1560_);
v_discrEqs_1561_ = lean_ctor_get(v_fvars_1558_, 3);
lean_inc_ref(v_discrEqs_1561_);
v_extraEqs_1562_ = lean_ctor_get(v_fvars_1558_, 4);
lean_inc_ref(v_extraEqs_1562_);
lean_dec_ref(v_fvars_1558_);
v___x_1563_ = l_Array_append___redArg(v_fields_1559_, v_overlaps_1560_);
lean_dec_ref(v_overlaps_1560_);
v___x_1564_ = l_Array_append___redArg(v___x_1563_, v_discrEqs_1561_);
lean_dec_ref(v_discrEqs_1561_);
v___x_1565_ = l_Array_append___redArg(v___x_1564_, v_extraEqs_1562_);
lean_dec_ref(v_extraEqs_1562_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1566_, lean_object* v_inst_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_1570_ = l_Lean_throwError___redArg(v_inst_1566_, v_inst_1567_, v___x_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1571_, lean_object* v_inst_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1571_, v_inst_1572_, v_x_1573_);
lean_dec_ref(v_x_1573_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = l_Lean_Expr_fvarId_x21(v_x_1576_);
v___x_1578_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1578_, 0, v___x_1577_);
v___x_1579_ = lean_apply_2(v_inst_1575_, lean_box(0), v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1580_, v_x_1581_);
lean_dec_ref(v_x_1581_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1583_, lean_object* v___f_1584_, lean_object* v_xs_1585_, lean_object* v_x_1586_){
_start:
{
size_t v_sz_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v_sz_1587_ = lean_array_size(v_xs_1585_);
v___x_1588_ = ((size_t)0ULL);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1583_, v___f_1584_, v_sz_1587_, v___x_1588_, v_xs_1585_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1590_, lean_object* v___f_1591_, lean_object* v_xs_1592_, lean_object* v_x_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1590_, v___f_1591_, v_xs_1592_, v_x_1593_);
lean_dec_ref(v_x_1593_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_fst_1595_, lean_object* v_fst_1596_, lean_object* v___x_1597_, lean_object* v___x_1598_, lean_object* v_toPure_1599_, lean_object* v_____do__lift_1600_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1601_ = lean_array_push(v_fst_1595_, v_____do__lift_1600_);
v___x_1602_ = lean_nat_add(v_fst_1596_, v___x_1597_);
v___x_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v___x_1598_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1601_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
v___x_1605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
v___x_1606_ = lean_apply_2(v_toPure_1599_, lean_box(0), v___x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed(lean_object* v_fst_1607_, lean_object* v_fst_1608_, lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_toPure_1611_, lean_object* v_____do__lift_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__3(v_fst_1607_, v_fst_1608_, v___x_1609_, v___x_1610_, v_toPure_1611_, v_____do__lift_1612_);
lean_dec(v___x_1609_);
lean_dec(v_fst_1608_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(uint8_t v_val_1614_, lean_object* v_a_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
if (v_val_1614_ == 0)
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_mkEqRefl(v_a_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1621_;
}
else
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Lean_Meta_mkHEqRefl(v_a_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed(lean_object* v_val_1623_, lean_object* v_a_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v_val_12196__boxed_1630_; lean_object* v_res_1631_; 
v_val_12196__boxed_1630_ = lean_unbox(v_val_1623_);
v_res_1631_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(v_val_12196__boxed_1630_, v_a_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_toPure_1632_, lean_object* v_inst_1633_, lean_object* v_toBind_1634_, lean_object* v_a_1635_, lean_object* v_x_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_snd_1638_; lean_object* v_snd_1639_; lean_object* v_fst_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1688_; 
v_snd_1638_ = lean_ctor_get(v___y_1637_, 1);
lean_inc(v_snd_1638_);
v_snd_1639_ = lean_ctor_get(v_snd_1638_, 1);
lean_inc(v_snd_1639_);
v_fst_1640_ = lean_ctor_get(v___y_1637_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___y_1637_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___y_1637_, 1);
lean_dec(v_unused_1689_);
v___x_1642_ = v___y_1637_;
v_isShared_1643_ = v_isSharedCheck_1688_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_fst_1640_);
lean_dec(v___y_1637_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1688_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_fst_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1686_; 
v_fst_1644_ = lean_ctor_get(v_snd_1638_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_snd_1638_);
if (v_isSharedCheck_1686_ == 0)
{
lean_object* v_unused_1687_; 
v_unused_1687_ = lean_ctor_get(v_snd_1638_, 1);
lean_dec(v_unused_1687_);
v___x_1646_ = v_snd_1638_;
v_isShared_1647_ = v_isSharedCheck_1686_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_fst_1644_);
lean_dec(v_snd_1638_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1686_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v_array_1648_; lean_object* v_start_1649_; lean_object* v_stop_1650_; uint8_t v___x_1651_; 
v_array_1648_ = lean_ctor_get(v_snd_1639_, 0);
v_start_1649_ = lean_ctor_get(v_snd_1639_, 1);
v_stop_1650_ = lean_ctor_get(v_snd_1639_, 2);
v___x_1651_ = lean_nat_dec_lt(v_start_1649_, v_stop_1650_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v_a_1635_);
lean_dec(v_toBind_1634_);
lean_dec(v_inst_1633_);
if (v_isShared_1647_ == 0)
{
v___x_1653_ = v___x_1646_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_fst_1644_);
lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_snd_1639_);
v___x_1653_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1653_);
v___x_1655_ = v___x_1642_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_fst_1640_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1653_);
v___x_1655_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1655_);
v___x_1657_ = lean_apply_2(v_toPure_1632_, lean_box(0), v___x_1656_);
return v___x_1657_;
}
}
}
else
{
lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1682_; 
lean_inc(v_stop_1650_);
lean_inc(v_start_1649_);
lean_inc_ref(v_array_1648_);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_snd_1639_);
if (v_isSharedCheck_1682_ == 0)
{
lean_object* v_unused_1683_; lean_object* v_unused_1684_; lean_object* v_unused_1685_; 
v_unused_1683_ = lean_ctor_get(v_snd_1639_, 2);
lean_dec(v_unused_1683_);
v_unused_1684_ = lean_ctor_get(v_snd_1639_, 1);
lean_dec(v_unused_1684_);
v_unused_1685_ = lean_ctor_get(v_snd_1639_, 0);
lean_dec(v_unused_1685_);
v___x_1661_ = v_snd_1639_;
v_isShared_1662_ = v_isSharedCheck_1682_;
goto v_resetjp_1660_;
}
else
{
lean_dec(v_snd_1639_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1682_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1663_ = lean_array_fget(v_array_1648_, v_start_1649_);
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_nat_add(v_start_1649_, v___x_1664_);
lean_dec(v_start_1649_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v___x_1665_);
v___x_1667_ = v___x_1661_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_array_1648_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_stop_1650_);
v___x_1667_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
if (lean_obj_tag(v___x_1663_) == 0)
{
lean_object* v___x_1669_; 
lean_dec_ref(v_a_1635_);
lean_dec(v_toBind_1634_);
lean_dec(v_inst_1633_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 1, v___x_1667_);
v___x_1669_ = v___x_1646_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_fst_1644_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
lean_object* v___x_1671_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1669_);
v___x_1671_ = v___x_1642_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_fst_1640_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
v___x_1673_ = lean_apply_2(v_toPure_1632_, lean_box(0), v___x_1672_);
return v___x_1673_;
}
}
}
else
{
lean_object* v_val_1676_; lean_object* v___f_1677_; lean_object* v___f_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_del_object(v___x_1646_);
lean_del_object(v___x_1642_);
v_val_1676_ = lean_ctor_get(v___x_1663_, 0);
lean_inc(v_val_1676_);
lean_dec_ref_known(v___x_1663_, 1);
v___f_1677_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_1677_, 0, v_fst_1640_);
lean_closure_set(v___f_1677_, 1, v_fst_1644_);
lean_closure_set(v___f_1677_, 2, v___x_1664_);
lean_closure_set(v___f_1677_, 3, v___x_1667_);
lean_closure_set(v___f_1677_, 4, v_toPure_1632_);
v___f_1678_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4___boxed), 7, 2);
lean_closure_set(v___f_1678_, 0, v_val_1676_);
lean_closure_set(v___f_1678_, 1, v_a_1635_);
v___x_1679_ = lean_apply_2(v_inst_1633_, lean_box(0), v___f_1678_);
v___x_1680_ = lean_apply_4(v_toBind_1634_, lean_box(0), lean_box(0), v___x_1679_, v___f_1677_);
return v___x_1680_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(lean_object* v_heq_1690_, lean_object* v_fst_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Lean_mkArrow(v_heq_1690_, v_fst_1691_, v___y_1694_, v___y_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_heq_1698_, lean_object* v_fst_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_heq_1698_, v_fst_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_heq_1708_, lean_object* v_fst_1709_, lean_object* v_fst_1710_, lean_object* v___x_1711_, lean_object* v___x_1712_, lean_object* v_toPure_1713_, lean_object* v_____x_1714_){
_start:
{
uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1715_ = l_Lean_Expr_isHEq(v_heq_1708_);
v___x_1716_ = lean_box(v___x_1715_);
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
v___x_1718_ = lean_array_push(v_fst_1709_, v___x_1717_);
v___x_1719_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_1720_ = lean_array_push(v_fst_1710_, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1711_);
lean_ctor_set(v___x_1721_, 1, v___x_1712_);
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
v___x_1723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1718_);
lean_ctor_set(v___x_1723_, 1, v___x_1722_);
v___x_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1724_, 0, v_____x_1714_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
v___x_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
v___x_1726_ = lean_apply_2(v_toPure_1713_, lean_box(0), v___x_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed(lean_object* v_heq_1727_, lean_object* v_fst_1728_, lean_object* v_fst_1729_, lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_toPure_1732_, lean_object* v_____x_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__7(v_heq_1727_, v_fst_1728_, v_fst_1729_, v___x_1730_, v___x_1731_, v_toPure_1732_, v_____x_1733_);
lean_dec_ref(v_heq_1727_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_fst_1735_, lean_object* v_fst_1736_, lean_object* v_fst_1737_, lean_object* v___x_1738_, lean_object* v___x_1739_, lean_object* v_toPure_1740_, lean_object* v_inst_1741_, lean_object* v_toBind_1742_, lean_object* v_heq_1743_){
_start:
{
lean_object* v___f_1744_; lean_object* v___f_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_inc_ref(v_heq_1743_);
v___f_1744_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1744_, 0, v_heq_1743_);
lean_closure_set(v___f_1744_, 1, v_fst_1735_);
v___f_1745_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___boxed), 7, 6);
lean_closure_set(v___f_1745_, 0, v_heq_1743_);
lean_closure_set(v___f_1745_, 1, v_fst_1736_);
lean_closure_set(v___f_1745_, 2, v_fst_1737_);
lean_closure_set(v___f_1745_, 3, v___x_1738_);
lean_closure_set(v___f_1745_, 4, v___x_1739_);
lean_closure_set(v___f_1745_, 5, v_toPure_1740_);
v___x_1746_ = lean_apply_2(v_inst_1741_, lean_box(0), v___f_1744_);
v___x_1747_ = lean_apply_4(v_toBind_1742_, lean_box(0), lean_box(0), v___x_1746_, v___f_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v___x_1748_, lean_object* v_a_1749_, lean_object* v_inst_1750_, lean_object* v_toBind_1751_, lean_object* v___f_1752_, lean_object* v_fst_1753_, lean_object* v_fst_1754_, lean_object* v___x_1755_, lean_object* v___x_1756_, lean_object* v___x_1757_, lean_object* v_fst_1758_, lean_object* v_toPure_1759_, uint8_t v_____do__lift_1760_){
_start:
{
if (v_____do__lift_1760_ == 0)
{
lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
lean_dec(v_toPure_1759_);
lean_dec(v_fst_1758_);
lean_dec_ref(v___x_1757_);
lean_dec_ref(v___x_1756_);
lean_dec(v___x_1755_);
lean_dec(v_fst_1754_);
lean_dec(v_fst_1753_);
v___x_1761_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1761_, 0, v___x_1748_);
lean_closure_set(v___x_1761_, 1, v_a_1749_);
v___x_1762_ = lean_apply_2(v_inst_1750_, lean_box(0), v___x_1761_);
v___x_1763_ = lean_apply_4(v_toBind_1751_, lean_box(0), lean_box(0), v___x_1762_, v___f_1752_);
return v___x_1763_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v___f_1752_);
lean_dec(v_toBind_1751_);
lean_dec(v_inst_1750_);
lean_dec_ref(v_a_1749_);
lean_dec_ref(v___x_1748_);
v___x_1764_ = lean_box(0);
v___x_1765_ = lean_array_push(v_fst_1753_, v___x_1764_);
v___x_1766_ = lean_array_push(v_fst_1754_, v___x_1755_);
v___x_1767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1756_);
lean_ctor_set(v___x_1767_, 1, v___x_1757_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1766_);
lean_ctor_set(v___x_1768_, 1, v___x_1767_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1765_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v_fst_1758_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
v___x_1772_ = lean_apply_2(v_toPure_1759_, lean_box(0), v___x_1771_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v___x_1773_, lean_object* v_a_1774_, lean_object* v_inst_1775_, lean_object* v_toBind_1776_, lean_object* v___f_1777_, lean_object* v_fst_1778_, lean_object* v_fst_1779_, lean_object* v___x_1780_, lean_object* v___x_1781_, lean_object* v___x_1782_, lean_object* v_fst_1783_, lean_object* v_toPure_1784_, lean_object* v_____do__lift_1785_){
_start:
{
uint8_t v_____do__lift_12390__boxed_1786_; lean_object* v_res_1787_; 
v_____do__lift_12390__boxed_1786_ = lean_unbox(v_____do__lift_1785_);
v_res_1787_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v___x_1773_, v_a_1774_, v_inst_1775_, v_toBind_1776_, v___f_1777_, v_fst_1778_, v_fst_1779_, v___x_1780_, v___x_1781_, v___x_1782_, v_fst_1783_, v_toPure_1784_, v_____do__lift_12390__boxed_1786_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_toPure_1788_, uint8_t v_addEqualities_1789_, lean_object* v_inst_1790_, lean_object* v_toBind_1791_, lean_object* v_a_1792_, lean_object* v_x_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_snd_1795_; lean_object* v_snd_1796_; lean_object* v_snd_1797_; lean_object* v_snd_1798_; lean_object* v_fst_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1905_; 
v_snd_1795_ = lean_ctor_get(v___y_1794_, 1);
lean_inc(v_snd_1795_);
v_snd_1796_ = lean_ctor_get(v_snd_1795_, 1);
lean_inc(v_snd_1796_);
v_snd_1797_ = lean_ctor_get(v_snd_1796_, 1);
lean_inc(v_snd_1797_);
v_snd_1798_ = lean_ctor_get(v_snd_1797_, 1);
lean_inc(v_snd_1798_);
v_fst_1799_ = lean_ctor_get(v___y_1794_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___y_1794_);
if (v_isSharedCheck_1905_ == 0)
{
lean_object* v_unused_1906_; 
v_unused_1906_ = lean_ctor_get(v___y_1794_, 1);
lean_dec(v_unused_1906_);
v___x_1801_ = v___y_1794_;
v_isShared_1802_ = v_isSharedCheck_1905_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_fst_1799_);
lean_dec(v___y_1794_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1905_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_fst_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1903_; 
v_fst_1803_ = lean_ctor_get(v_snd_1795_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_snd_1795_);
if (v_isSharedCheck_1903_ == 0)
{
lean_object* v_unused_1904_; 
v_unused_1904_ = lean_ctor_get(v_snd_1795_, 1);
lean_dec(v_unused_1904_);
v___x_1805_ = v_snd_1795_;
v_isShared_1806_ = v_isSharedCheck_1903_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_fst_1803_);
lean_dec(v_snd_1795_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1903_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v_fst_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1901_; 
v_fst_1807_ = lean_ctor_get(v_snd_1796_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_snd_1796_);
if (v_isSharedCheck_1901_ == 0)
{
lean_object* v_unused_1902_; 
v_unused_1902_ = lean_ctor_get(v_snd_1796_, 1);
lean_dec(v_unused_1902_);
v___x_1809_ = v_snd_1796_;
v_isShared_1810_ = v_isSharedCheck_1901_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_fst_1807_);
lean_dec(v_snd_1796_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1901_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v_fst_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1899_; 
v_fst_1811_ = lean_ctor_get(v_snd_1797_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_snd_1797_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_snd_1797_, 1);
lean_dec(v_unused_1900_);
v___x_1813_ = v_snd_1797_;
v_isShared_1814_ = v_isSharedCheck_1899_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_fst_1811_);
lean_dec(v_snd_1797_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1899_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_array_1815_; lean_object* v_start_1816_; lean_object* v_stop_1817_; uint8_t v___x_1818_; 
v_array_1815_ = lean_ctor_get(v_snd_1798_, 0);
v_start_1816_ = lean_ctor_get(v_snd_1798_, 1);
v_stop_1817_ = lean_ctor_get(v_snd_1798_, 2);
v___x_1818_ = lean_nat_dec_lt(v_start_1816_, v_stop_1817_);
if (v___x_1818_ == 0)
{
lean_object* v___x_1820_; 
lean_dec_ref(v_a_1792_);
lean_dec(v_toBind_1791_);
lean_dec(v_inst_1790_);
if (v_isShared_1814_ == 0)
{
v___x_1820_ = v___x_1813_;
goto v_reusejp_1819_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_fst_1811_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_snd_1798_);
v___x_1820_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1819_;
}
v_reusejp_1819_:
{
lean_object* v___x_1822_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1820_);
v___x_1822_ = v___x_1809_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_fst_1807_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
lean_object* v___x_1824_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1822_);
v___x_1824_ = v___x_1805_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_fst_1803_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1824_);
v___x_1826_ = v___x_1801_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1799_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
v___x_1828_ = lean_apply_2(v_toPure_1788_, lean_box(0), v___x_1827_);
return v___x_1828_;
}
}
}
}
}
else
{
lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1895_; 
lean_inc(v_stop_1817_);
lean_inc(v_start_1816_);
lean_inc_ref(v_array_1815_);
v_isSharedCheck_1895_ = !lean_is_exclusive(v_snd_1798_);
if (v_isSharedCheck_1895_ == 0)
{
lean_object* v_unused_1896_; lean_object* v_unused_1897_; lean_object* v_unused_1898_; 
v_unused_1896_ = lean_ctor_get(v_snd_1798_, 2);
lean_dec(v_unused_1896_);
v_unused_1897_ = lean_ctor_get(v_snd_1798_, 1);
lean_dec(v_unused_1897_);
v_unused_1898_ = lean_ctor_get(v_snd_1798_, 0);
lean_dec(v_unused_1898_);
v___x_1834_ = v_snd_1798_;
v_isShared_1835_ = v_isSharedCheck_1895_;
goto v_resetjp_1833_;
}
else
{
lean_dec(v_snd_1798_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1895_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v_array_1836_; lean_object* v_start_1837_; lean_object* v_stop_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v_array_1836_ = lean_ctor_get(v_fst_1811_, 0);
v_start_1837_ = lean_ctor_get(v_fst_1811_, 1);
v_stop_1838_ = lean_ctor_get(v_fst_1811_, 2);
v___x_1839_ = lean_array_fget(v_array_1815_, v_start_1816_);
v___x_1840_ = lean_unsigned_to_nat(1u);
v___x_1841_ = lean_nat_add(v_start_1816_, v___x_1840_);
lean_dec(v_start_1816_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1841_);
v___x_1843_ = v___x_1834_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_array_1815_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v___x_1841_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v_stop_1817_);
v___x_1843_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
uint8_t v___x_1844_; 
v___x_1844_ = lean_nat_dec_lt(v_start_1837_, v_stop_1838_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1846_; 
lean_dec(v___x_1839_);
lean_dec_ref(v_a_1792_);
lean_dec(v_toBind_1791_);
lean_dec(v_inst_1790_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1843_);
v___x_1846_ = v___x_1813_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_fst_1811_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1843_);
v___x_1846_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
lean_object* v___x_1848_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1846_);
v___x_1848_ = v___x_1809_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_fst_1807_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1846_);
v___x_1848_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1850_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1848_);
v___x_1850_ = v___x_1805_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_fst_1803_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1850_);
v___x_1852_ = v___x_1801_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_fst_1799_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
v___x_1854_ = lean_apply_2(v_toPure_1788_, lean_box(0), v___x_1853_);
return v___x_1854_;
}
}
}
}
}
else
{
lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1890_; 
lean_inc(v_stop_1838_);
lean_inc(v_start_1837_);
lean_inc_ref(v_array_1836_);
v_isSharedCheck_1890_ = !lean_is_exclusive(v_fst_1811_);
if (v_isSharedCheck_1890_ == 0)
{
lean_object* v_unused_1891_; lean_object* v_unused_1892_; lean_object* v_unused_1893_; 
v_unused_1891_ = lean_ctor_get(v_fst_1811_, 2);
lean_dec(v_unused_1891_);
v_unused_1892_ = lean_ctor_get(v_fst_1811_, 1);
lean_dec(v_unused_1892_);
v_unused_1893_ = lean_ctor_get(v_fst_1811_, 0);
lean_dec(v_unused_1893_);
v___x_1860_ = v_fst_1811_;
v_isShared_1861_ = v_isSharedCheck_1890_;
goto v_resetjp_1859_;
}
else
{
lean_dec(v_fst_1811_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1890_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1862_ = lean_array_fget(v_array_1836_, v_start_1837_);
v___x_1863_ = lean_nat_add(v_start_1837_, v___x_1840_);
lean_dec(v_start_1837_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___x_1863_);
v___x_1865_ = v___x_1860_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_array_1836_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_stop_1838_);
v___x_1865_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
if (v_addEqualities_1789_ == 0)
{
lean_dec(v___x_1862_);
lean_dec_ref(v_a_1792_);
lean_dec(v_toBind_1791_);
lean_dec(v_inst_1790_);
goto v___jp_1866_;
}
else
{
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v___f_1884_; lean_object* v___f_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_del_object(v___x_1813_);
lean_del_object(v___x_1809_);
lean_del_object(v___x_1805_);
lean_del_object(v___x_1801_);
lean_inc_n(v_toBind_1791_, 2);
lean_inc_n(v_inst_1790_, 2);
lean_inc(v_toPure_1788_);
lean_inc_ref(v___x_1843_);
lean_inc_ref(v___x_1865_);
lean_inc(v_fst_1807_);
lean_inc(v_fst_1803_);
lean_inc(v_fst_1799_);
v___f_1884_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8), 9, 8);
lean_closure_set(v___f_1884_, 0, v_fst_1799_);
lean_closure_set(v___f_1884_, 1, v_fst_1803_);
lean_closure_set(v___f_1884_, 2, v_fst_1807_);
lean_closure_set(v___f_1884_, 3, v___x_1865_);
lean_closure_set(v___f_1884_, 4, v___x_1843_);
lean_closure_set(v___f_1884_, 5, v_toPure_1788_);
lean_closure_set(v___f_1884_, 6, v_inst_1790_);
lean_closure_set(v___f_1884_, 7, v_toBind_1791_);
lean_inc_ref(v_a_1792_);
v___f_1885_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 13, 12);
lean_closure_set(v___f_1885_, 0, v___x_1862_);
lean_closure_set(v___f_1885_, 1, v_a_1792_);
lean_closure_set(v___f_1885_, 2, v_inst_1790_);
lean_closure_set(v___f_1885_, 3, v_toBind_1791_);
lean_closure_set(v___f_1885_, 4, v___f_1884_);
lean_closure_set(v___f_1885_, 5, v_fst_1803_);
lean_closure_set(v___f_1885_, 6, v_fst_1807_);
lean_closure_set(v___f_1885_, 7, v___x_1839_);
lean_closure_set(v___f_1885_, 8, v___x_1865_);
lean_closure_set(v___f_1885_, 9, v___x_1843_);
lean_closure_set(v___f_1885_, 10, v_fst_1799_);
lean_closure_set(v___f_1885_, 11, v_toPure_1788_);
v___x_1886_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1886_, 0, v_a_1792_);
v___x_1887_ = lean_apply_2(v_inst_1790_, lean_box(0), v___x_1886_);
v___x_1888_ = lean_apply_4(v_toBind_1791_, lean_box(0), lean_box(0), v___x_1887_, v___f_1885_);
return v___x_1888_;
}
else
{
lean_dec(v___x_1862_);
lean_dec_ref(v_a_1792_);
lean_dec(v_toBind_1791_);
lean_dec(v_inst_1790_);
goto v___jp_1866_;
}
}
v___jp_1866_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1867_ = lean_box(0);
v___x_1868_ = lean_array_push(v_fst_1803_, v___x_1867_);
v___x_1869_ = lean_array_push(v_fst_1807_, v___x_1839_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1843_);
lean_ctor_set(v___x_1813_, 0, v___x_1865_);
v___x_1871_ = v___x_1813_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1883_, 1, v___x_1843_);
v___x_1871_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1873_; 
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1871_);
lean_ctor_set(v___x_1809_, 0, v___x_1869_);
v___x_1873_ = v___x_1809_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1869_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1871_);
v___x_1873_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1875_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1873_);
lean_ctor_set(v___x_1805_, 0, v___x_1868_);
v___x_1875_ = v___x_1805_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1873_);
v___x_1875_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1875_);
v___x_1877_ = v___x_1801_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_fst_1799_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
v___x_1879_ = lean_apply_2(v_toPure_1788_, lean_box(0), v___x_1878_);
return v___x_1879_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed(lean_object* v_toPure_1907_, lean_object* v_addEqualities_1908_, lean_object* v_inst_1909_, lean_object* v_toBind_1910_, lean_object* v_a_1911_, lean_object* v_x_1912_, lean_object* v___y_1913_){
_start:
{
uint8_t v_addEqualities_boxed_1914_; lean_object* v_res_1915_; 
v_addEqualities_boxed_1914_ = lean_unbox(v_addEqualities_1908_);
v_res_1915_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__10(v_toPure_1907_, v_addEqualities_boxed_1914_, v_inst_1909_, v_toBind_1910_, v_a_1911_, v_x_1912_, v___y_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v_toPure_1916_, lean_object* v_____do__lift_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_apply_2(v_toPure_1916_, lean_box(0), v_____do__lift_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1919_, lean_object* v_____do__lift_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_apply_2(v_toPure_1919_, lean_box(0), v_____do__lift_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1922_, lean_object* v_fst_1923_, lean_object* v_____do__lift_1924_, lean_object* v_toPure_1925_, lean_object* v_____do__lift_1926_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v_fst_1922_);
lean_ctor_set(v___x_1927_, 1, v_fst_1923_);
v___x_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1928_, 0, v_____do__lift_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_____do__lift_1924_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_apply_2(v_toPure_1925_, lean_box(0), v___x_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1931_, lean_object* v_fst_1932_, lean_object* v_toPure_1933_, lean_object* v_fst_1934_, lean_object* v_inst_1935_, lean_object* v_toBind_1936_, lean_object* v_____do__lift_1937_){
_start:
{
lean_object* v___f_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___f_1938_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1938_, 0, v_fst_1931_);
lean_closure_set(v___f_1938_, 1, v_fst_1932_);
lean_closure_set(v___f_1938_, 2, v_____do__lift_1937_);
lean_closure_set(v___f_1938_, 3, v_toPure_1933_);
v___x_1939_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1939_, 0, v_fst_1934_);
v___x_1940_ = lean_apply_2(v_inst_1935_, lean_box(0), v___x_1939_);
v___x_1941_ = lean_apply_4(v_toBind_1936_, lean_box(0), lean_box(0), v___x_1940_, v___f_1938_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1942_, lean_object* v_inst_1943_, lean_object* v_toBind_1944_, lean_object* v_motiveArgs_1945_, lean_object* v_____s_1946_){
_start:
{
lean_object* v_snd_1947_; lean_object* v_snd_1948_; lean_object* v_fst_1949_; lean_object* v_fst_1950_; lean_object* v_fst_1951_; lean_object* v___f_1952_; uint8_t v___x_1953_; uint8_t v___x_1954_; uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v_snd_1947_ = lean_ctor_get(v_____s_1946_, 1);
lean_inc(v_snd_1947_);
v_snd_1948_ = lean_ctor_get(v_snd_1947_, 1);
lean_inc(v_snd_1948_);
v_fst_1949_ = lean_ctor_get(v_____s_1946_, 0);
lean_inc_n(v_fst_1949_, 2);
lean_dec_ref(v_____s_1946_);
v_fst_1950_ = lean_ctor_get(v_snd_1947_, 0);
lean_inc(v_fst_1950_);
lean_dec(v_snd_1947_);
v_fst_1951_ = lean_ctor_get(v_snd_1948_, 0);
lean_inc(v_fst_1951_);
lean_dec(v_snd_1948_);
lean_inc(v_toBind_1944_);
lean_inc(v_inst_1943_);
v___f_1952_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1952_, 0, v_fst_1950_);
lean_closure_set(v___f_1952_, 1, v_fst_1951_);
lean_closure_set(v___f_1952_, 2, v_toPure_1942_);
lean_closure_set(v___f_1952_, 3, v_fst_1949_);
lean_closure_set(v___f_1952_, 4, v_inst_1943_);
lean_closure_set(v___f_1952_, 5, v_toBind_1944_);
v___x_1953_ = 0;
v___x_1954_ = 1;
v___x_1955_ = 1;
v___x_1956_ = lean_box(v___x_1953_);
v___x_1957_ = lean_box(v___x_1954_);
v___x_1958_ = lean_box(v___x_1953_);
v___x_1959_ = lean_box(v___x_1954_);
v___x_1960_ = lean_box(v___x_1955_);
v___x_1961_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1961_, 0, v_motiveArgs_1945_);
lean_closure_set(v___x_1961_, 1, v_fst_1949_);
lean_closure_set(v___x_1961_, 2, v___x_1956_);
lean_closure_set(v___x_1961_, 3, v___x_1957_);
lean_closure_set(v___x_1961_, 4, v___x_1958_);
lean_closure_set(v___x_1961_, 5, v___x_1959_);
lean_closure_set(v___x_1961_, 6, v___x_1960_);
v___x_1962_ = lean_apply_2(v_inst_1943_, lean_box(0), v___x_1961_);
v___x_1963_ = lean_apply_4(v_toBind_1944_, lean_box(0), lean_box(0), v___x_1962_, v___f_1952_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_1966_, lean_object* v_discrs_x27_1967_, lean_object* v_motiveArgs_1968_, lean_object* v_inst_1969_, lean_object* v___f_1970_, lean_object* v_toBind_1971_, lean_object* v___f_1972_, lean_object* v_motiveBody_x27_1973_){
_start:
{
lean_object* v_discrInfos_1974_; lean_object* v___x_1975_; lean_object* v_addHEqualities_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; size_t v_sz_1985_; size_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v_discrInfos_1974_ = lean_ctor_get(v_toMatcherInfo_1966_, 4);
lean_inc_ref(v_discrInfos_1974_);
lean_dec_ref(v_toMatcherInfo_1966_);
v___x_1975_ = lean_unsigned_to_nat(0u);
v_addHEqualities_1976_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_1977_ = lean_array_get_size(v_discrs_x27_1967_);
v___x_1978_ = l_Array_toSubarray___redArg(v_discrs_x27_1967_, v___x_1975_, v___x_1977_);
v___x_1979_ = lean_array_get_size(v_discrInfos_1974_);
v___x_1980_ = l_Array_toSubarray___redArg(v_discrInfos_1974_, v___x_1975_, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1978_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v_addHEqualities_1976_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v_addHEqualities_1976_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_motiveBody_x27_1973_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v_sz_1985_ = lean_array_size(v_motiveArgs_1968_);
v___x_1986_ = ((size_t)0ULL);
v___x_1987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1969_, v_motiveArgs_1968_, v___f_1970_, v_sz_1985_, v___x_1986_, v___x_1984_);
v___x_1988_ = lean_apply_4(v_toBind_1971_, lean_box(0), lean_box(0), v___x_1987_, v___f_1972_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_1989_, lean_object* v_motiveArgs_1990_, lean_object* v_motiveBody_1991_, lean_object* v_toBind_1992_, lean_object* v___f_1993_, lean_object* v_____r_1994_){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_apply_2(v_onMotive_1989_, v_motiveArgs_1990_, v_motiveBody_1991_);
v___x_1996_ = lean_apply_4(v_toBind_1992_, lean_box(0), lean_box(0), v___x_1995_, v___f_1993_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_1997_, lean_object* v_____r_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_apply_1(v___f_1997_, v_____r_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_2000_, lean_object* v_inst_2001_, lean_object* v_toBind_2002_, lean_object* v_toMatcherInfo_2003_, lean_object* v_discrs_x27_2004_, lean_object* v_inst_2005_, lean_object* v___f_2006_, lean_object* v_onMotive_2007_, lean_object* v_discrs_2008_, lean_object* v_inst_2009_, lean_object* v_motiveArgs_2010_, lean_object* v_motiveBody_2011_){
_start:
{
lean_object* v___f_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
lean_inc_ref_n(v_motiveArgs_2010_, 3);
lean_inc_n(v_toBind_2002_, 3);
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2012_, 0, v_toPure_2000_);
lean_closure_set(v___f_2012_, 1, v_inst_2001_);
lean_closure_set(v___f_2012_, 2, v_toBind_2002_);
lean_closure_set(v___f_2012_, 3, v_motiveArgs_2010_);
lean_inc_ref(v_inst_2005_);
v___f_2013_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2013_, 0, v_toMatcherInfo_2003_);
lean_closure_set(v___f_2013_, 1, v_discrs_x27_2004_);
lean_closure_set(v___f_2013_, 2, v_motiveArgs_2010_);
lean_closure_set(v___f_2013_, 3, v_inst_2005_);
lean_closure_set(v___f_2013_, 4, v___f_2006_);
lean_closure_set(v___f_2013_, 5, v_toBind_2002_);
lean_closure_set(v___f_2013_, 6, v___f_2012_);
lean_inc_ref(v___f_2013_);
lean_inc_ref(v_motiveBody_2011_);
lean_inc(v_onMotive_2007_);
v___f_2014_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2014_, 0, v_onMotive_2007_);
lean_closure_set(v___f_2014_, 1, v_motiveArgs_2010_);
lean_closure_set(v___f_2014_, 2, v_motiveBody_2011_);
lean_closure_set(v___f_2014_, 3, v_toBind_2002_);
lean_closure_set(v___f_2014_, 4, v___f_2013_);
v___x_2015_ = lean_array_get_size(v_motiveArgs_2010_);
v___x_2016_ = lean_array_get_size(v_discrs_2008_);
v___x_2017_ = lean_nat_dec_eq(v___x_2015_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec_ref(v___f_2013_);
lean_dec_ref(v_motiveBody_2011_);
lean_dec_ref(v_motiveArgs_2010_);
lean_dec(v_onMotive_2007_);
v___f_2018_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2018_, 0, v___f_2014_);
v___x_2019_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2020_ = l_Nat_reprFast(v___x_2016_);
v___x_2021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
v___x_2022_ = l_Lean_MessageData_ofFormat(v___x_2021_);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2019_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = l_Lean_throwError___redArg(v_inst_2005_, v_inst_2009_, v___x_2025_);
v___x_2027_ = lean_apply_4(v_toBind_2002_, lean_box(0), lean_box(0), v___x_2026_, v___f_2018_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v___f_2014_);
lean_dec_ref(v_inst_2009_);
lean_dec_ref(v_inst_2005_);
v___x_2028_ = lean_box(0);
v___x_2029_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2007_, v_motiveArgs_2010_, v_motiveBody_2011_, v_toBind_2002_, v___f_2013_, v___x_2028_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2030_, lean_object* v_inst_2031_, lean_object* v_toBind_2032_, lean_object* v_toMatcherInfo_2033_, lean_object* v_discrs_x27_2034_, lean_object* v_inst_2035_, lean_object* v___f_2036_, lean_object* v_onMotive_2037_, lean_object* v_discrs_2038_, lean_object* v_inst_2039_, lean_object* v_motiveArgs_2040_, lean_object* v_motiveBody_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2030_, v_inst_2031_, v_toBind_2032_, v_toMatcherInfo_2033_, v_discrs_x27_2034_, v_inst_2035_, v___f_2036_, v_onMotive_2037_, v_discrs_2038_, v_inst_2039_, v_motiveArgs_2040_, v_motiveBody_2041_);
lean_dec_ref(v_discrs_2038_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2043_, lean_object* v_numParams_2044_, lean_object* v_numDiscrs_2045_, lean_object* v_altInfos_2046_, lean_object* v_uElimPos_x3f_2047_, lean_object* v_snd_2048_, lean_object* v_overlaps_2049_, lean_object* v_matcherName_2050_, lean_object* v_matcherLevels_2051_, lean_object* v_params_x27_2052_, lean_object* v_fst_2053_, lean_object* v_discrs_x27_2054_, lean_object* v_fst_2055_, lean_object* v_toPure_2056_, lean_object* v_____do__lift_2057_){
_start:
{
lean_object* v_remaining_x27_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_remaining_x27_2058_ = l_Array_append___redArg(v_fst_2043_, v_____do__lift_2057_);
v___x_2059_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2059_, 0, v_numParams_2044_);
lean_ctor_set(v___x_2059_, 1, v_numDiscrs_2045_);
lean_ctor_set(v___x_2059_, 2, v_altInfos_2046_);
lean_ctor_set(v___x_2059_, 3, v_uElimPos_x3f_2047_);
lean_ctor_set(v___x_2059_, 4, v_snd_2048_);
lean_ctor_set(v___x_2059_, 5, v_overlaps_2049_);
v___x_2060_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v_matcherName_2050_);
lean_ctor_set(v___x_2060_, 2, v_matcherLevels_2051_);
lean_ctor_set(v___x_2060_, 3, v_params_x27_2052_);
lean_ctor_set(v___x_2060_, 4, v_fst_2053_);
lean_ctor_set(v___x_2060_, 5, v_discrs_x27_2054_);
lean_ctor_set(v___x_2060_, 6, v_fst_2055_);
lean_ctor_set(v___x_2060_, 7, v_remaining_x27_2058_);
v___x_2061_ = lean_apply_2(v_toPure_2056_, lean_box(0), v___x_2060_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2062_, lean_object* v_numParams_2063_, lean_object* v_numDiscrs_2064_, lean_object* v_altInfos_2065_, lean_object* v_uElimPos_x3f_2066_, lean_object* v_snd_2067_, lean_object* v_overlaps_2068_, lean_object* v_matcherName_2069_, lean_object* v_matcherLevels_2070_, lean_object* v_params_x27_2071_, lean_object* v_fst_2072_, lean_object* v_discrs_x27_2073_, lean_object* v_fst_2074_, lean_object* v_toPure_2075_, lean_object* v_____do__lift_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2062_, v_numParams_2063_, v_numDiscrs_2064_, v_altInfos_2065_, v_uElimPos_x3f_2066_, v_snd_2067_, v_overlaps_2068_, v_matcherName_2069_, v_matcherLevels_2070_, v_params_x27_2071_, v_fst_2072_, v_discrs_x27_2073_, v_fst_2074_, v_toPure_2075_, v_____do__lift_2076_);
lean_dec_ref(v_____do__lift_2076_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2078_, lean_object* v_numParams_2079_, lean_object* v_numDiscrs_2080_, lean_object* v_altInfos_2081_, lean_object* v_uElimPos_x3f_2082_, lean_object* v_snd_2083_, lean_object* v_overlaps_2084_, lean_object* v_matcherName_2085_, lean_object* v_matcherLevels_2086_, lean_object* v_params_x27_2087_, lean_object* v_fst_2088_, lean_object* v_discrs_x27_2089_, lean_object* v_toPure_2090_, lean_object* v_onRemaining_2091_, lean_object* v_remaining_2092_, lean_object* v_toBind_2093_, lean_object* v_____s_2094_){
_start:
{
lean_object* v_fst_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v_fst_2095_ = lean_ctor_get(v_____s_2094_, 0);
lean_inc(v_fst_2095_);
lean_dec_ref(v_____s_2094_);
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2096_, 0, v_fst_2078_);
lean_closure_set(v___f_2096_, 1, v_numParams_2079_);
lean_closure_set(v___f_2096_, 2, v_numDiscrs_2080_);
lean_closure_set(v___f_2096_, 3, v_altInfos_2081_);
lean_closure_set(v___f_2096_, 4, v_uElimPos_x3f_2082_);
lean_closure_set(v___f_2096_, 5, v_snd_2083_);
lean_closure_set(v___f_2096_, 6, v_overlaps_2084_);
lean_closure_set(v___f_2096_, 7, v_matcherName_2085_);
lean_closure_set(v___f_2096_, 8, v_matcherLevels_2086_);
lean_closure_set(v___f_2096_, 9, v_params_x27_2087_);
lean_closure_set(v___f_2096_, 10, v_fst_2088_);
lean_closure_set(v___f_2096_, 11, v_discrs_x27_2089_);
lean_closure_set(v___f_2096_, 12, v_fst_2095_);
lean_closure_set(v___f_2096_, 13, v_toPure_2090_);
v___x_2097_ = lean_apply_1(v_onRemaining_2091_, v_remaining_2092_);
v___x_2098_ = lean_apply_4(v_toBind_2093_, lean_box(0), lean_box(0), v___x_2097_, v___f_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2099_ = _args[0];
lean_object* v_numParams_2100_ = _args[1];
lean_object* v_numDiscrs_2101_ = _args[2];
lean_object* v_altInfos_2102_ = _args[3];
lean_object* v_uElimPos_x3f_2103_ = _args[4];
lean_object* v_snd_2104_ = _args[5];
lean_object* v_overlaps_2105_ = _args[6];
lean_object* v_matcherName_2106_ = _args[7];
lean_object* v_matcherLevels_2107_ = _args[8];
lean_object* v_params_x27_2108_ = _args[9];
lean_object* v_fst_2109_ = _args[10];
lean_object* v_discrs_x27_2110_ = _args[11];
lean_object* v_toPure_2111_ = _args[12];
lean_object* v_onRemaining_2112_ = _args[13];
lean_object* v_remaining_2113_ = _args[14];
lean_object* v_toBind_2114_ = _args[15];
lean_object* v_____s_2115_ = _args[16];
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2099_, v_numParams_2100_, v_numDiscrs_2101_, v_altInfos_2102_, v_uElimPos_x3f_2103_, v_snd_2104_, v_overlaps_2105_, v_matcherName_2106_, v_matcherLevels_2107_, v_params_x27_2108_, v_fst_2109_, v_discrs_x27_2110_, v_toPure_2111_, v_onRemaining_2112_, v_remaining_2113_, v_toBind_2114_, v_____s_2115_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2117_, lean_object* v_next_2118_, lean_object* v_G_2119_, lean_object* v_____do__lift_2120_){
_start:
{
if (lean_obj_tag(v_____do__lift_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
lean_dec(v_G_2119_);
v_a_2121_ = lean_ctor_get(v_____do__lift_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v_____do__lift_2120_, 1);
v___x_2122_ = lean_apply_2(v_toPure_2117_, lean_box(0), v_a_2121_);
return v___x_2122_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; 
lean_dec(v_toPure_2117_);
v_a_2123_ = lean_ctor_get(v_____do__lift_2120_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v_____do__lift_2120_, 1);
v___x_2124_ = lean_unsigned_to_nat(1u);
v___x_2125_ = lean_nat_add(v_next_2118_, v___x_2124_);
v___x_2126_ = lean_apply_4(v_G_2119_, v___x_2125_, v_a_2123_, lean_box(0), lean_box(0));
return v___x_2126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2127_, lean_object* v_next_2128_, lean_object* v_G_2129_, lean_object* v_____do__lift_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2127_, v_next_2128_, v_G_2129_, v_____do__lift_2130_);
lean_dec(v_next_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2132_, lean_object* v_ys4_2133_, uint8_t v___x_2134_, uint8_t v___x_2135_, lean_object* v_inst_2136_, lean_object* v_alt_x27_2137_){
_start:
{
lean_object* v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2138_ = l_Array_append___redArg(v_xs_2132_, v_ys4_2133_);
v___x_2139_ = 1;
v___x_2140_ = lean_box(v___x_2134_);
v___x_2141_ = lean_box(v___x_2135_);
v___x_2142_ = lean_box(v___x_2134_);
v___x_2143_ = lean_box(v___x_2135_);
v___x_2144_ = lean_box(v___x_2139_);
v___x_2145_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2145_, 0, v___x_2138_);
lean_closure_set(v___x_2145_, 1, v_alt_x27_2137_);
lean_closure_set(v___x_2145_, 2, v___x_2140_);
lean_closure_set(v___x_2145_, 3, v___x_2141_);
lean_closure_set(v___x_2145_, 4, v___x_2142_);
lean_closure_set(v___x_2145_, 5, v___x_2143_);
lean_closure_set(v___x_2145_, 6, v___x_2144_);
v___x_2146_ = lean_apply_2(v_inst_2136_, lean_box(0), v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2147_, lean_object* v_ys4_2148_, lean_object* v___x_2149_, lean_object* v___x_2150_, lean_object* v_inst_2151_, lean_object* v_alt_x27_2152_){
_start:
{
uint8_t v___x_12843__boxed_2153_; uint8_t v___x_12844__boxed_2154_; lean_object* v_res_2155_; 
v___x_12843__boxed_2153_ = lean_unbox(v___x_2149_);
v___x_12844__boxed_2154_ = lean_unbox(v___x_2150_);
v_res_2155_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2147_, v_ys4_2148_, v___x_12843__boxed_2153_, v___x_12844__boxed_2154_, v_inst_2151_, v_alt_x27_2152_);
lean_dec_ref(v_ys4_2148_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_xs_2156_, lean_object* v_remaining_x27_2157_, lean_object* v_ys4_2158_, lean_object* v_onAlt_2159_, lean_object* v_next_2160_, lean_object* v_altType_2161_, lean_object* v_toBind_2162_, lean_object* v___f_2163_, lean_object* v_alt_2164_){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
lean_inc_ref(v_remaining_x27_2157_);
lean_inc_ref(v_xs_2156_);
v___x_2165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2165_, 0, v_xs_2156_);
lean_ctor_set(v___x_2165_, 1, v_xs_2156_);
lean_ctor_set(v___x_2165_, 2, v_remaining_x27_2157_);
lean_ctor_set(v___x_2165_, 3, v_remaining_x27_2157_);
lean_ctor_set(v___x_2165_, 4, v_ys4_2158_);
v___x_2166_ = lean_apply_4(v_onAlt_2159_, v_next_2160_, v_altType_2161_, v___x_2165_, v_alt_2164_);
v___x_2167_ = lean_apply_4(v_toBind_2162_, lean_box(0), lean_box(0), v___x_2166_, v___f_2163_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2168_, lean_object* v_xs_2169_, lean_object* v_inst_2170_, lean_object* v_toBind_2171_, lean_object* v___f_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_names_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_inc_ref(v_xs_2169_);
v___x_2176_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2176_, 0, v___x_2168_);
lean_closure_set(v___x_2176_, 1, v_xs_2169_);
v___x_2177_ = lean_apply_2(v_inst_2170_, lean_box(0), v___x_2176_);
v___x_2178_ = lean_apply_4(v_toBind_2171_, lean_box(0), lean_box(0), v___x_2177_, v___f_2172_);
v___x_2179_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2173_, v_inst_2174_, v_xs_2169_, v_names_2175_, v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2180_, uint8_t v___x_2181_, uint8_t v___x_2182_, lean_object* v_inst_2183_, lean_object* v_remaining_x27_2184_, lean_object* v_onAlt_2185_, lean_object* v_next_2186_, lean_object* v_toBind_2187_, lean_object* v___x_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_, lean_object* v___f_2191_, lean_object* v_ys4_2192_, lean_object* v_altType_2193_){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___f_2196_; lean_object* v___f_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2194_ = lean_box(v___x_2181_);
v___x_2195_ = lean_box(v___x_2182_);
lean_inc(v_inst_2183_);
lean_inc_ref(v_ys4_2192_);
lean_inc_ref_n(v_xs_2180_, 2);
v___f_2196_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2196_, 0, v_xs_2180_);
lean_closure_set(v___f_2196_, 1, v_ys4_2192_);
lean_closure_set(v___f_2196_, 2, v___x_2194_);
lean_closure_set(v___f_2196_, 3, v___x_2195_);
lean_closure_set(v___f_2196_, 4, v_inst_2183_);
lean_inc_n(v_toBind_2187_, 2);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 9, 8);
lean_closure_set(v___f_2197_, 0, v_xs_2180_);
lean_closure_set(v___f_2197_, 1, v_remaining_x27_2184_);
lean_closure_set(v___f_2197_, 2, v_ys4_2192_);
lean_closure_set(v___f_2197_, 3, v_onAlt_2185_);
lean_closure_set(v___f_2197_, 4, v_next_2186_);
lean_closure_set(v___f_2197_, 5, v_altType_2193_);
lean_closure_set(v___f_2197_, 6, v_toBind_2187_);
lean_closure_set(v___f_2197_, 7, v___f_2196_);
lean_inc_ref(v_inst_2190_);
lean_inc_ref(v_inst_2189_);
lean_inc_ref(v___x_2188_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2198_, 0, v___x_2188_);
lean_closure_set(v___f_2198_, 1, v_xs_2180_);
lean_closure_set(v___f_2198_, 2, v_inst_2183_);
lean_closure_set(v___f_2198_, 3, v_toBind_2187_);
lean_closure_set(v___f_2198_, 4, v___f_2197_);
lean_closure_set(v___f_2198_, 5, v_inst_2189_);
lean_closure_set(v___f_2198_, 6, v_inst_2190_);
v___x_2199_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2189_, v_inst_2190_, v___x_2188_, v___f_2191_, v___x_2181_);
v___x_2200_ = lean_apply_4(v_toBind_2187_, lean_box(0), lean_box(0), v___x_2199_, v___f_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2201_, lean_object* v___x_2202_, lean_object* v___x_2203_, lean_object* v_inst_2204_, lean_object* v_remaining_x27_2205_, lean_object* v_onAlt_2206_, lean_object* v_next_2207_, lean_object* v_toBind_2208_, lean_object* v___x_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v___f_2212_, lean_object* v_ys4_2213_, lean_object* v_altType_2214_){
_start:
{
uint8_t v___x_12896__boxed_2215_; uint8_t v___x_12897__boxed_2216_; lean_object* v_res_2217_; 
v___x_12896__boxed_2215_ = lean_unbox(v___x_2202_);
v___x_12897__boxed_2216_ = lean_unbox(v___x_2203_);
v_res_2217_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2201_, v___x_12896__boxed_2215_, v___x_12897__boxed_2216_, v_inst_2204_, v_remaining_x27_2205_, v_onAlt_2206_, v_next_2207_, v_toBind_2208_, v___x_2209_, v_inst_2210_, v_inst_2211_, v___f_2212_, v_ys4_2213_, v_altType_2214_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2218_, uint8_t v___x_2219_, lean_object* v_inst_2220_, lean_object* v_remaining_x27_2221_, lean_object* v_onAlt_2222_, lean_object* v_next_2223_, lean_object* v_toBind_2224_, lean_object* v___x_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v___f_2228_, lean_object* v_fst_2229_, lean_object* v_xs_2230_, lean_object* v_altType_2231_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2232_ = lean_box(v___x_2218_);
v___x_2233_ = lean_box(v___x_2219_);
lean_inc_ref(v_inst_2227_);
lean_inc_ref(v_inst_2226_);
v___f_2234_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 14, 12);
lean_closure_set(v___f_2234_, 0, v_xs_2230_);
lean_closure_set(v___f_2234_, 1, v___x_2232_);
lean_closure_set(v___f_2234_, 2, v___x_2233_);
lean_closure_set(v___f_2234_, 3, v_inst_2220_);
lean_closure_set(v___f_2234_, 4, v_remaining_x27_2221_);
lean_closure_set(v___f_2234_, 5, v_onAlt_2222_);
lean_closure_set(v___f_2234_, 6, v_next_2223_);
lean_closure_set(v___f_2234_, 7, v_toBind_2224_);
lean_closure_set(v___f_2234_, 8, v___x_2225_);
lean_closure_set(v___f_2234_, 9, v_inst_2226_);
lean_closure_set(v___f_2234_, 10, v_inst_2227_);
lean_closure_set(v___f_2234_, 11, v___f_2228_);
v___x_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2235_, 0, v_fst_2229_);
v___x_2236_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2226_, v_inst_2227_, v_altType_2231_, v___x_2235_, v___f_2234_, v___x_2218_, v___x_2218_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2237_, lean_object* v___x_2238_, lean_object* v_inst_2239_, lean_object* v_remaining_x27_2240_, lean_object* v_onAlt_2241_, lean_object* v_next_2242_, lean_object* v_toBind_2243_, lean_object* v___x_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v___f_2247_, lean_object* v_fst_2248_, lean_object* v_xs_2249_, lean_object* v_altType_2250_){
_start:
{
uint8_t v___x_12931__boxed_2251_; uint8_t v___x_12932__boxed_2252_; lean_object* v_res_2253_; 
v___x_12931__boxed_2251_ = lean_unbox(v___x_2237_);
v___x_12932__boxed_2252_ = lean_unbox(v___x_2238_);
v_res_2253_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_12931__boxed_2251_, v___x_12932__boxed_2252_, v_inst_2239_, v_remaining_x27_2240_, v_onAlt_2241_, v_next_2242_, v_toBind_2243_, v___x_2244_, v_inst_2245_, v_inst_2246_, v___f_2247_, v_fst_2248_, v_xs_2249_, v_altType_2250_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_fst_2254_, lean_object* v___x_2255_, lean_object* v___x_2256_, lean_object* v___x_2257_, lean_object* v_toPure_2258_, lean_object* v_alt_x27_2259_){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2260_ = lean_array_push(v_fst_2254_, v_alt_x27_2259_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2255_);
lean_ctor_set(v___x_2261_, 1, v___x_2256_);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2257_);
lean_ctor_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2260_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
v___x_2265_ = lean_apply_2(v_toPure_2258_, lean_box(0), v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2266_, lean_object* v_toPure_2267_, lean_object* v_toBind_2268_, lean_object* v___f_2269_, uint8_t v___x_2270_, uint8_t v___x_2271_, lean_object* v_inst_2272_, lean_object* v_remaining_x27_2273_, lean_object* v_onAlt_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v___f_2277_, lean_object* v_fst_2278_, lean_object* v_next_2279_, lean_object* v_acc_2280_, lean_object* v_h_2281_, lean_object* v_G_2282_){
_start:
{
uint8_t v___x_2283_; 
v___x_2283_ = lean_nat_dec_lt(v_next_2279_, v___x_2266_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec(v_G_2282_);
lean_dec(v_next_2279_);
lean_dec(v_fst_2278_);
lean_dec(v___f_2277_);
lean_dec_ref(v_inst_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec(v_onAlt_2274_);
lean_dec_ref(v_remaining_x27_2273_);
lean_dec(v_inst_2272_);
lean_dec(v___f_2269_);
lean_dec(v_toBind_2268_);
v___x_2284_ = lean_apply_2(v_toPure_2267_, lean_box(0), v_acc_2280_);
return v___x_2284_;
}
else
{
lean_object* v_snd_2285_; lean_object* v_snd_2286_; lean_object* v_snd_2287_; lean_object* v_fst_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2398_; 
v_snd_2285_ = lean_ctor_get(v_acc_2280_, 1);
lean_inc(v_snd_2285_);
v_snd_2286_ = lean_ctor_get(v_snd_2285_, 1);
lean_inc(v_snd_2286_);
v_snd_2287_ = lean_ctor_get(v_snd_2286_, 1);
lean_inc(v_snd_2287_);
v_fst_2288_ = lean_ctor_get(v_acc_2280_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_acc_2280_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v_acc_2280_, 1);
lean_dec(v_unused_2399_);
v___x_2290_ = v_acc_2280_;
v_isShared_2291_ = v_isSharedCheck_2398_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_fst_2288_);
lean_dec(v_acc_2280_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2398_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_fst_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2396_; 
v_fst_2292_ = lean_ctor_get(v_snd_2285_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_snd_2285_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v_snd_2285_, 1);
lean_dec(v_unused_2397_);
v___x_2294_ = v_snd_2285_;
v_isShared_2295_ = v_isSharedCheck_2396_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_fst_2292_);
lean_dec(v_snd_2285_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2396_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_fst_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2394_; 
v_fst_2296_ = lean_ctor_get(v_snd_2286_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_snd_2286_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v_snd_2286_, 1);
lean_dec(v_unused_2395_);
v___x_2298_ = v_snd_2286_;
v_isShared_2299_ = v_isSharedCheck_2394_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_fst_2296_);
lean_dec(v_snd_2286_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2394_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_array_2300_; lean_object* v_start_2301_; lean_object* v_stop_2302_; lean_object* v___f_2303_; lean_object* v___y_2305_; uint8_t v___x_2308_; 
v_array_2300_ = lean_ctor_get(v_snd_2287_, 0);
v_start_2301_ = lean_ctor_get(v_snd_2287_, 1);
v_stop_2302_ = lean_ctor_get(v_snd_2287_, 2);
lean_inc(v_next_2279_);
lean_inc(v_toPure_2267_);
v___f_2303_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2303_, 0, v_toPure_2267_);
lean_closure_set(v___f_2303_, 1, v_next_2279_);
lean_closure_set(v___f_2303_, 2, v_G_2282_);
v___x_2308_ = lean_nat_dec_lt(v_start_2301_, v_stop_2302_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2310_; 
lean_dec(v_next_2279_);
lean_dec(v_fst_2278_);
lean_dec(v___f_2277_);
lean_dec_ref(v_inst_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec(v_onAlt_2274_);
lean_dec_ref(v_remaining_x27_2273_);
lean_dec(v_inst_2272_);
if (v_isShared_2299_ == 0)
{
v___x_2310_ = v___x_2298_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_fst_2296_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_snd_2287_);
v___x_2310_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2310_);
v___x_2312_ = v___x_2294_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_fst_2292_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 1, v___x_2312_);
v___x_2314_ = v___x_2290_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_fst_2288_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2314_);
v___x_2316_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2315_);
v___y_2305_ = v___x_2316_;
goto v___jp_2304_;
}
}
}
}
else
{
lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2390_; 
lean_inc(v_stop_2302_);
lean_inc(v_start_2301_);
lean_inc_ref(v_array_2300_);
v_isSharedCheck_2390_ = !lean_is_exclusive(v_snd_2287_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; lean_object* v_unused_2392_; lean_object* v_unused_2393_; 
v_unused_2391_ = lean_ctor_get(v_snd_2287_, 2);
lean_dec(v_unused_2391_);
v_unused_2392_ = lean_ctor_get(v_snd_2287_, 1);
lean_dec(v_unused_2392_);
v_unused_2393_ = lean_ctor_get(v_snd_2287_, 0);
lean_dec(v_unused_2393_);
v___x_2321_ = v_snd_2287_;
v_isShared_2322_ = v_isSharedCheck_2390_;
goto v_resetjp_2320_;
}
else
{
lean_dec(v_snd_2287_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2390_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v_array_2323_; lean_object* v_start_2324_; lean_object* v_stop_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v_array_2323_ = lean_ctor_get(v_fst_2296_, 0);
v_start_2324_ = lean_ctor_get(v_fst_2296_, 1);
v_stop_2325_ = lean_ctor_get(v_fst_2296_, 2);
v___x_2326_ = lean_array_fget(v_array_2300_, v_start_2301_);
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = lean_nat_add(v_start_2301_, v___x_2327_);
lean_dec(v_start_2301_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 1, v___x_2328_);
v___x_2330_ = v___x_2321_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_array_2300_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2389_, 2, v_stop_2302_);
v___x_2330_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
uint8_t v___x_2331_; 
v___x_2331_ = lean_nat_dec_lt(v_start_2324_, v_stop_2325_);
if (v___x_2331_ == 0)
{
lean_object* v___x_2333_; 
lean_dec(v___x_2326_);
lean_dec(v_next_2279_);
lean_dec(v_fst_2278_);
lean_dec(v___f_2277_);
lean_dec_ref(v_inst_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec(v_onAlt_2274_);
lean_dec_ref(v_remaining_x27_2273_);
lean_dec(v_inst_2272_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2330_);
v___x_2333_ = v___x_2298_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_fst_2296_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2330_);
v___x_2333_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2333_);
v___x_2335_ = v___x_2294_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_fst_2292_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v___x_2333_);
v___x_2335_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2337_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 1, v___x_2335_);
v___x_2337_ = v___x_2290_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_fst_2288_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
v___x_2339_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2338_);
v___y_2305_ = v___x_2339_;
goto v___jp_2304_;
}
}
}
}
else
{
lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2385_; 
lean_inc(v_stop_2325_);
lean_inc(v_start_2324_);
lean_inc_ref(v_array_2323_);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_fst_2296_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; lean_object* v_unused_2387_; lean_object* v_unused_2388_; 
v_unused_2386_ = lean_ctor_get(v_fst_2296_, 2);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_fst_2296_, 1);
lean_dec(v_unused_2387_);
v_unused_2388_ = lean_ctor_get(v_fst_2296_, 0);
lean_dec(v_unused_2388_);
v___x_2344_ = v_fst_2296_;
v_isShared_2345_ = v_isSharedCheck_2385_;
goto v_resetjp_2343_;
}
else
{
lean_dec(v_fst_2296_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2385_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v_array_2346_; lean_object* v_start_2347_; lean_object* v_stop_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2352_; 
v_array_2346_ = lean_ctor_get(v_fst_2292_, 0);
v_start_2347_ = lean_ctor_get(v_fst_2292_, 1);
v_stop_2348_ = lean_ctor_get(v_fst_2292_, 2);
v___x_2349_ = lean_array_fget(v_array_2323_, v_start_2324_);
v___x_2350_ = lean_nat_add(v_start_2324_, v___x_2327_);
lean_dec(v_start_2324_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v___x_2350_);
v___x_2352_ = v___x_2344_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_array_2323_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v_stop_2325_);
v___x_2352_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_nat_dec_lt(v_start_2347_, v_stop_2348_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2355_; 
lean_dec(v___x_2349_);
lean_dec(v___x_2326_);
lean_dec(v_next_2279_);
lean_dec(v_fst_2278_);
lean_dec(v___f_2277_);
lean_dec_ref(v_inst_2276_);
lean_dec_ref(v_inst_2275_);
lean_dec(v_onAlt_2274_);
lean_dec_ref(v_remaining_x27_2273_);
lean_dec(v_inst_2272_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2330_);
lean_ctor_set(v___x_2298_, 0, v___x_2352_);
v___x_2355_ = v___x_2298_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v___x_2330_);
v___x_2355_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2355_);
v___x_2357_ = v___x_2294_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_fst_2292_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2359_; 
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 1, v___x_2357_);
v___x_2359_ = v___x_2290_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_fst_2288_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2359_);
v___x_2361_ = lean_apply_2(v_toPure_2267_, lean_box(0), v___x_2360_);
v___y_2305_ = v___x_2361_;
goto v___jp_2304_;
}
}
}
}
else
{
lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2380_; 
lean_inc(v_stop_2348_);
lean_inc(v_start_2347_);
lean_inc_ref(v_array_2346_);
lean_del_object(v___x_2298_);
lean_del_object(v___x_2294_);
lean_del_object(v___x_2290_);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_fst_2292_);
if (v_isSharedCheck_2380_ == 0)
{
lean_object* v_unused_2381_; lean_object* v_unused_2382_; lean_object* v_unused_2383_; 
v_unused_2381_ = lean_ctor_get(v_fst_2292_, 2);
lean_dec(v_unused_2381_);
v_unused_2382_ = lean_ctor_get(v_fst_2292_, 1);
lean_dec(v_unused_2382_);
v_unused_2383_ = lean_ctor_get(v_fst_2292_, 0);
lean_dec(v_unused_2383_);
v___x_2366_ = v_fst_2292_;
v_isShared_2367_ = v_isSharedCheck_2380_;
goto v_resetjp_2365_;
}
else
{
lean_dec(v_fst_2292_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2380_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2368_ = lean_array_fget_borrowed(v_array_2346_, v_start_2347_);
v___x_2369_ = lean_box(v___x_2270_);
v___x_2370_ = lean_box(v___x_2271_);
lean_inc_ref(v_inst_2276_);
lean_inc_ref(v_inst_2275_);
lean_inc(v___x_2368_);
lean_inc(v_toBind_2268_);
v___f_2371_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 14, 12);
lean_closure_set(v___f_2371_, 0, v___x_2369_);
lean_closure_set(v___f_2371_, 1, v___x_2370_);
lean_closure_set(v___f_2371_, 2, v_inst_2272_);
lean_closure_set(v___f_2371_, 3, v_remaining_x27_2273_);
lean_closure_set(v___f_2371_, 4, v_onAlt_2274_);
lean_closure_set(v___f_2371_, 5, v_next_2279_);
lean_closure_set(v___f_2371_, 6, v_toBind_2268_);
lean_closure_set(v___f_2371_, 7, v___x_2368_);
lean_closure_set(v___f_2371_, 8, v_inst_2275_);
lean_closure_set(v___f_2371_, 9, v_inst_2276_);
lean_closure_set(v___f_2371_, 10, v___f_2277_);
lean_closure_set(v___f_2371_, 11, v_fst_2278_);
v___x_2372_ = lean_nat_add(v_start_2347_, v___x_2327_);
lean_dec(v_start_2347_);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2372_);
v___x_2374_ = v___x_2366_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_array_2346_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v___x_2372_);
lean_ctor_set(v_reuseFailAlloc_2379_, 2, v_stop_2348_);
v___x_2374_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
lean_object* v___f_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___f_2375_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2375_, 0, v_fst_2288_);
lean_closure_set(v___f_2375_, 1, v___x_2352_);
lean_closure_set(v___f_2375_, 2, v___x_2330_);
lean_closure_set(v___f_2375_, 3, v___x_2374_);
lean_closure_set(v___f_2375_, 4, v_toPure_2267_);
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2349_);
v___x_2377_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2275_, v_inst_2276_, v___x_2326_, v___x_2376_, v___f_2371_, v___x_2270_, v___x_2270_);
lean_inc(v_toBind_2268_);
v___x_2378_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___x_2377_, v___f_2375_);
v___y_2305_ = v___x_2378_;
goto v___jp_2304_;
}
}
}
}
}
}
}
}
}
v___jp_2304_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_inc(v_toBind_2268_);
v___x_2306_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___y_2305_, v___f_2269_);
v___x_2307_ = lean_apply_4(v_toBind_2268_, lean_box(0), lean_box(0), v___x_2306_, v___f_2303_);
return v___x_2307_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_2400_ = _args[0];
lean_object* v_toPure_2401_ = _args[1];
lean_object* v_toBind_2402_ = _args[2];
lean_object* v___f_2403_ = _args[3];
lean_object* v___x_2404_ = _args[4];
lean_object* v___x_2405_ = _args[5];
lean_object* v_inst_2406_ = _args[6];
lean_object* v_remaining_x27_2407_ = _args[7];
lean_object* v_onAlt_2408_ = _args[8];
lean_object* v_inst_2409_ = _args[9];
lean_object* v_inst_2410_ = _args[10];
lean_object* v___f_2411_ = _args[11];
lean_object* v_fst_2412_ = _args[12];
lean_object* v_next_2413_ = _args[13];
lean_object* v_acc_2414_ = _args[14];
lean_object* v_h_2415_ = _args[15];
lean_object* v_G_2416_ = _args[16];
_start:
{
uint8_t v___x_12982__boxed_2417_; uint8_t v___x_12983__boxed_2418_; lean_object* v_res_2419_; 
v___x_12982__boxed_2417_ = lean_unbox(v___x_2404_);
v___x_12983__boxed_2418_ = lean_unbox(v___x_2405_);
v_res_2419_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2400_, v_toPure_2401_, v_toBind_2402_, v___f_2403_, v___x_12982__boxed_2417_, v___x_12983__boxed_2418_, v_inst_2406_, v_remaining_x27_2407_, v_onAlt_2408_, v_inst_2409_, v_inst_2410_, v___f_2411_, v_fst_2412_, v_next_2413_, v_acc_2414_, v_h_2415_, v_G_2416_);
lean_dec(v___x_2400_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_matcherApp_2420_, lean_object* v_alts_2421_, lean_object* v___x_2422_, lean_object* v___x_2423_, lean_object* v_remaining_x27_2424_, lean_object* v___f_2425_, lean_object* v_toBind_2426_, lean_object* v___f_2427_, lean_object* v_altTypes_2428_){
_start:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v___x_2429_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2420_);
v___x_2430_ = lean_array_get_size(v___x_2429_);
v___x_2431_ = lean_array_get_size(v_altTypes_2428_);
lean_inc_n(v___x_2422_, 3);
v___x_2432_ = l_Array_toSubarray___redArg(v_alts_2421_, v___x_2422_, v___x_2423_);
v___x_2433_ = l_Array_toSubarray___redArg(v___x_2429_, v___x_2422_, v___x_2430_);
v___x_2434_ = l_Array_toSubarray___redArg(v_altTypes_2428_, v___x_2422_, v___x_2431_);
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2433_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
v___x_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2432_);
lean_ctor_set(v___x_2436_, 1, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2437_, 0, v_remaining_x27_2424_);
lean_ctor_set(v___x_2437_, 1, v___x_2436_);
v___x_2438_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2425_, v___x_2422_, v___x_2437_, lean_box(0));
v___x_2439_ = lean_apply_4(v_toBind_2426_, lean_box(0), lean_box(0), v___x_2438_, v___f_2427_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2440_, lean_object* v_toPure_2441_, lean_object* v_toBind_2442_, lean_object* v___f_2443_, uint8_t v___x_2444_, uint8_t v___x_2445_, lean_object* v_inst_2446_, lean_object* v_remaining_x27_2447_, lean_object* v_onAlt_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v___f_2451_, lean_object* v_fst_2452_, lean_object* v_matcherApp_2453_, lean_object* v___x_2454_, lean_object* v___f_2455_, lean_object* v_aux_2456_, lean_object* v_____r_2457_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v___x_2458_ = lean_array_get_size(v_alts_2440_);
v___x_2459_ = lean_box(v___x_2444_);
v___x_2460_ = lean_box(v___x_2445_);
lean_inc_ref(v_remaining_x27_2447_);
lean_inc(v_inst_2446_);
lean_inc_n(v_toBind_2442_, 2);
v___f_2461_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 17, 13);
lean_closure_set(v___f_2461_, 0, v___x_2458_);
lean_closure_set(v___f_2461_, 1, v_toPure_2441_);
lean_closure_set(v___f_2461_, 2, v_toBind_2442_);
lean_closure_set(v___f_2461_, 3, v___f_2443_);
lean_closure_set(v___f_2461_, 4, v___x_2459_);
lean_closure_set(v___f_2461_, 5, v___x_2460_);
lean_closure_set(v___f_2461_, 6, v_inst_2446_);
lean_closure_set(v___f_2461_, 7, v_remaining_x27_2447_);
lean_closure_set(v___f_2461_, 8, v_onAlt_2448_);
lean_closure_set(v___f_2461_, 9, v_inst_2449_);
lean_closure_set(v___f_2461_, 10, v_inst_2450_);
lean_closure_set(v___f_2461_, 11, v___f_2451_);
lean_closure_set(v___f_2461_, 12, v_fst_2452_);
v___f_2462_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2462_, 0, v_matcherApp_2453_);
lean_closure_set(v___f_2462_, 1, v_alts_2440_);
lean_closure_set(v___f_2462_, 2, v___x_2454_);
lean_closure_set(v___f_2462_, 3, v___x_2458_);
lean_closure_set(v___f_2462_, 4, v_remaining_x27_2447_);
lean_closure_set(v___f_2462_, 5, v___f_2461_);
lean_closure_set(v___f_2462_, 6, v_toBind_2442_);
lean_closure_set(v___f_2462_, 7, v___f_2455_);
v___x_2463_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2463_, 0, v___x_2458_);
lean_closure_set(v___x_2463_, 1, v_aux_2456_);
v___x_2464_ = lean_apply_2(v_inst_2446_, lean_box(0), v___x_2463_);
v___x_2465_ = lean_apply_4(v_toBind_2442_, lean_box(0), lean_box(0), v___x_2464_, v___f_2462_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_alts_2466_ = _args[0];
lean_object* v_toPure_2467_ = _args[1];
lean_object* v_toBind_2468_ = _args[2];
lean_object* v___f_2469_ = _args[3];
lean_object* v___x_2470_ = _args[4];
lean_object* v___x_2471_ = _args[5];
lean_object* v_inst_2472_ = _args[6];
lean_object* v_remaining_x27_2473_ = _args[7];
lean_object* v_onAlt_2474_ = _args[8];
lean_object* v_inst_2475_ = _args[9];
lean_object* v_inst_2476_ = _args[10];
lean_object* v___f_2477_ = _args[11];
lean_object* v_fst_2478_ = _args[12];
lean_object* v_matcherApp_2479_ = _args[13];
lean_object* v___x_2480_ = _args[14];
lean_object* v___f_2481_ = _args[15];
lean_object* v_aux_2482_ = _args[16];
lean_object* v_____r_2483_ = _args[17];
_start:
{
uint8_t v___x_13239__boxed_2484_; uint8_t v___x_13240__boxed_2485_; lean_object* v_res_2486_; 
v___x_13239__boxed_2484_ = lean_unbox(v___x_2470_);
v___x_13240__boxed_2485_ = lean_unbox(v___x_2471_);
v_res_2486_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2466_, v_toPure_2467_, v_toBind_2468_, v___f_2469_, v___x_13239__boxed_2484_, v___x_13240__boxed_2485_, v_inst_2472_, v_remaining_x27_2473_, v_onAlt_2474_, v_inst_2475_, v_inst_2476_, v___f_2477_, v_fst_2478_, v_matcherApp_2479_, v___x_2480_, v___f_2481_, v_aux_2482_, v_____r_2483_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v___x_2487_, lean_object* v_e_2488_){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = l_Lean_indentD(v_e_2488_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2487_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v___x_2491_, lean_object* v___f_2492_, lean_object* v_runInBase_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_apply_2(v_runInBase_2493_, lean_box(0), v___x_2491_);
v___x_2500_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2499_, v___f_2492_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object* v___x_2501_, lean_object* v___f_2502_, lean_object* v_runInBase_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2501_, v___f_2502_, v_runInBase_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v_toPure_2510_, lean_object* v_next_2511_, lean_object* v_G_2512_, lean_object* v_____do__lift_2513_){
_start:
{
if (lean_obj_tag(v_____do__lift_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; 
lean_dec(v_G_2512_);
v_a_2514_ = lean_ctor_get(v_____do__lift_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v_____do__lift_2513_, 1);
v___x_2515_ = lean_apply_2(v_toPure_2510_, lean_box(0), v_a_2514_);
return v___x_2515_;
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v_toPure_2510_);
v_a_2516_ = lean_ctor_get(v_____do__lift_2513_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v_____do__lift_2513_, 1);
v___x_2517_ = lean_unsigned_to_nat(1u);
v___x_2518_ = lean_nat_add(v_next_2511_, v___x_2517_);
v___x_2519_ = lean_apply_4(v_G_2512_, v___x_2518_, v_a_2516_, lean_box(0), lean_box(0));
return v___x_2519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v_toPure_2520_, lean_object* v_next_2521_, lean_object* v_G_2522_, lean_object* v_____do__lift_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v_toPure_2520_, v_next_2521_, v_G_2522_, v_____do__lift_2523_);
lean_dec(v_next_2521_);
return v_res_2524_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = lean_box(0);
v___x_2534_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4));
v___x_2535_ = l_Lean_mkConst(v___x_2534_, v___x_2533_);
return v___x_2535_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5);
v___x_2537_ = lean_unsigned_to_nat(2u);
v___x_2538_ = lean_mk_empty_array_with_capacity(v___x_2537_);
v___x_2539_ = lean_array_push(v___x_2538_, v___x_2536_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v___x_2540_, lean_object* v_toPure_2541_, lean_object* v_inst_2542_, lean_object* v_alt_x27_2543_){
_start:
{
uint8_t v_hasUnitThunk_2544_; 
v_hasUnitThunk_2544_ = lean_ctor_get_uint8(v___x_2540_, sizeof(void*)*2);
if (v_hasUnitThunk_2544_ == 0)
{
lean_object* v___x_2545_; 
lean_dec(v_inst_2542_);
v___x_2545_ = lean_apply_2(v_toPure_2541_, lean_box(0), v_alt_x27_2543_);
return v___x_2545_;
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec(v_toPure_2541_);
v___x_2546_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_2547_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_2548_ = lean_array_push(v___x_2547_, v_alt_x27_2543_);
v___x_2549_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2549_, 0, v___x_2546_);
lean_closure_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = lean_apply_2(v_inst_2542_, lean_box(0), v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v___x_2551_, lean_object* v_toPure_2552_, lean_object* v_inst_2553_, lean_object* v_alt_x27_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v___x_2551_, v_toPure_2552_, v_inst_2553_, v_alt_x27_2554_);
lean_dec_ref(v___x_2551_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v_ys_2556_, lean_object* v_ys2_2557_, lean_object* v_ys3_2558_, lean_object* v_ys4_2559_, uint8_t v___x_2560_, uint8_t v_useSplitter_2561_, lean_object* v_inst_2562_, lean_object* v_alt_x27_2563_){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2564_ = l_Array_append___redArg(v_ys_2556_, v_ys2_2557_);
v___x_2565_ = l_Array_append___redArg(v___x_2564_, v_ys3_2558_);
v___x_2566_ = l_Array_append___redArg(v___x_2565_, v_ys4_2559_);
v___x_2567_ = 1;
v___x_2568_ = lean_box(v___x_2560_);
v___x_2569_ = lean_box(v_useSplitter_2561_);
v___x_2570_ = lean_box(v___x_2560_);
v___x_2571_ = lean_box(v_useSplitter_2561_);
v___x_2572_ = lean_box(v___x_2567_);
v___x_2573_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2573_, 0, v___x_2566_);
lean_closure_set(v___x_2573_, 1, v_alt_x27_2563_);
lean_closure_set(v___x_2573_, 2, v___x_2568_);
lean_closure_set(v___x_2573_, 3, v___x_2569_);
lean_closure_set(v___x_2573_, 4, v___x_2570_);
lean_closure_set(v___x_2573_, 5, v___x_2571_);
lean_closure_set(v___x_2573_, 6, v___x_2572_);
v___x_2574_ = lean_apply_2(v_inst_2562_, lean_box(0), v___x_2573_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v_ys_2575_, lean_object* v_ys2_2576_, lean_object* v_ys3_2577_, lean_object* v_ys4_2578_, lean_object* v___x_2579_, lean_object* v_useSplitter_2580_, lean_object* v_inst_2581_, lean_object* v_alt_x27_2582_){
_start:
{
uint8_t v___x_13393__boxed_2583_; uint8_t v_useSplitter_boxed_2584_; lean_object* v_res_2585_; 
v___x_13393__boxed_2583_ = lean_unbox(v___x_2579_);
v_useSplitter_boxed_2584_ = lean_unbox(v_useSplitter_2580_);
v_res_2585_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2575_, v_ys2_2576_, v_ys3_2577_, v_ys4_2578_, v___x_13393__boxed_2583_, v_useSplitter_boxed_2584_, v_inst_2581_, v_alt_x27_2582_);
lean_dec_ref(v_ys4_2578_);
lean_dec_ref(v_ys3_2577_);
lean_dec_ref(v_ys2_2576_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_args_2586_, lean_object* v_ys_2587_, lean_object* v_ys2_2588_, lean_object* v_ys3_2589_, lean_object* v_ys4_2590_, lean_object* v_onAlt_2591_, lean_object* v_next_2592_, lean_object* v_altType_2593_, lean_object* v_toBind_2594_, lean_object* v___f_2595_, lean_object* v_alt_2596_){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2597_, 0, v_args_2586_);
lean_ctor_set(v___x_2597_, 1, v_ys_2587_);
lean_ctor_set(v___x_2597_, 2, v_ys2_2588_);
lean_ctor_set(v___x_2597_, 3, v_ys3_2589_);
lean_ctor_set(v___x_2597_, 4, v_ys4_2590_);
v___x_2598_ = lean_apply_4(v_onAlt_2591_, v_next_2592_, v_altType_2593_, v___x_2597_, v_alt_2596_);
v___x_2599_ = lean_apply_4(v_toBind_2594_, lean_box(0), lean_box(0), v___x_2598_, v___f_2595_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_toMonadExceptOf_2600_, lean_object* v_ys_2601_, lean_object* v_ys2_2602_, lean_object* v_ys3_2603_, uint8_t v___x_2604_, uint8_t v_useSplitter_2605_, lean_object* v_inst_2606_, lean_object* v_args_2607_, lean_object* v_onAlt_2608_, lean_object* v_next_2609_, lean_object* v_toBind_2610_, lean_object* v___x_2611_, lean_object* v___f_2612_, lean_object* v_ys4_2613_, lean_object* v_altType_2614_){
_start:
{
lean_object* v_tryCatch_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v_tryCatch_2615_ = lean_ctor_get(v_toMonadExceptOf_2600_, 1);
lean_inc(v_tryCatch_2615_);
lean_dec_ref(v_toMonadExceptOf_2600_);
v___x_2616_ = lean_box(v___x_2604_);
v___x_2617_ = lean_box(v_useSplitter_2605_);
lean_inc(v_inst_2606_);
lean_inc_ref(v_ys4_2613_);
lean_inc_ref_n(v_ys3_2603_, 2);
lean_inc_ref(v_ys2_2602_);
lean_inc_ref(v_ys_2601_);
v___f_2618_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2618_, 0, v_ys_2601_);
lean_closure_set(v___f_2618_, 1, v_ys2_2602_);
lean_closure_set(v___f_2618_, 2, v_ys3_2603_);
lean_closure_set(v___f_2618_, 3, v_ys4_2613_);
lean_closure_set(v___f_2618_, 4, v___x_2616_);
lean_closure_set(v___f_2618_, 5, v___x_2617_);
lean_closure_set(v___f_2618_, 6, v_inst_2606_);
lean_inc(v_toBind_2610_);
lean_inc_ref(v_args_2607_);
v___f_2619_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 11, 10);
lean_closure_set(v___f_2619_, 0, v_args_2607_);
lean_closure_set(v___f_2619_, 1, v_ys_2601_);
lean_closure_set(v___f_2619_, 2, v_ys2_2602_);
lean_closure_set(v___f_2619_, 3, v_ys3_2603_);
lean_closure_set(v___f_2619_, 4, v_ys4_2613_);
lean_closure_set(v___f_2619_, 5, v_onAlt_2608_);
lean_closure_set(v___f_2619_, 6, v_next_2609_);
lean_closure_set(v___f_2619_, 7, v_altType_2614_);
lean_closure_set(v___f_2619_, 8, v_toBind_2610_);
lean_closure_set(v___f_2619_, 9, v___f_2618_);
v___x_2620_ = l_Array_append___redArg(v_args_2607_, v_ys3_2603_);
lean_dec_ref(v_ys3_2603_);
v___x_2621_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2621_, 0, v___x_2611_);
lean_closure_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = lean_apply_2(v_inst_2606_, lean_box(0), v___x_2621_);
v___x_2623_ = lean_apply_3(v_tryCatch_2615_, lean_box(0), v___x_2622_, v___f_2612_);
v___x_2624_ = lean_apply_4(v_toBind_2610_, lean_box(0), lean_box(0), v___x_2623_, v___f_2619_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_toMonadExceptOf_2625_, lean_object* v_ys_2626_, lean_object* v_ys2_2627_, lean_object* v_ys3_2628_, lean_object* v___x_2629_, lean_object* v_useSplitter_2630_, lean_object* v_inst_2631_, lean_object* v_args_2632_, lean_object* v_onAlt_2633_, lean_object* v_next_2634_, lean_object* v_toBind_2635_, lean_object* v___x_2636_, lean_object* v___f_2637_, lean_object* v_ys4_2638_, lean_object* v_altType_2639_){
_start:
{
uint8_t v___x_13429__boxed_2640_; uint8_t v_useSplitter_boxed_2641_; lean_object* v_res_2642_; 
v___x_13429__boxed_2640_ = lean_unbox(v___x_2629_);
v_useSplitter_boxed_2641_ = lean_unbox(v_useSplitter_2630_);
v_res_2642_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_toMonadExceptOf_2625_, v_ys_2626_, v_ys2_2627_, v_ys3_2628_, v___x_13429__boxed_2640_, v_useSplitter_boxed_2641_, v_inst_2631_, v_args_2632_, v_onAlt_2633_, v_next_2634_, v_toBind_2635_, v___x_2636_, v___f_2637_, v_ys4_2638_, v_altType_2639_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_toMonadExceptOf_2643_, lean_object* v_ys_2644_, lean_object* v_ys2_2645_, uint8_t v___x_2646_, uint8_t v_useSplitter_2647_, lean_object* v_inst_2648_, lean_object* v_args_2649_, lean_object* v_onAlt_2650_, lean_object* v_next_2651_, lean_object* v_toBind_2652_, lean_object* v___x_2653_, lean_object* v___f_2654_, lean_object* v_fst_2655_, lean_object* v_inst_2656_, lean_object* v_inst_2657_, lean_object* v_ys3_2658_, lean_object* v_altType_2659_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2660_ = lean_box(v___x_2646_);
v___x_2661_ = lean_box(v_useSplitter_2647_);
v___f_2662_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2662_, 0, v_toMonadExceptOf_2643_);
lean_closure_set(v___f_2662_, 1, v_ys_2644_);
lean_closure_set(v___f_2662_, 2, v_ys2_2645_);
lean_closure_set(v___f_2662_, 3, v_ys3_2658_);
lean_closure_set(v___f_2662_, 4, v___x_2660_);
lean_closure_set(v___f_2662_, 5, v___x_2661_);
lean_closure_set(v___f_2662_, 6, v_inst_2648_);
lean_closure_set(v___f_2662_, 7, v_args_2649_);
lean_closure_set(v___f_2662_, 8, v_onAlt_2650_);
lean_closure_set(v___f_2662_, 9, v_next_2651_);
lean_closure_set(v___f_2662_, 10, v_toBind_2652_);
lean_closure_set(v___f_2662_, 11, v___x_2653_);
lean_closure_set(v___f_2662_, 12, v___f_2654_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v_fst_2655_);
v___x_2664_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2656_, v_inst_2657_, v_altType_2659_, v___x_2663_, v___f_2662_, v___x_2646_, v___x_2646_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2665_ = _args[0];
lean_object* v_ys_2666_ = _args[1];
lean_object* v_ys2_2667_ = _args[2];
lean_object* v___x_2668_ = _args[3];
lean_object* v_useSplitter_2669_ = _args[4];
lean_object* v_inst_2670_ = _args[5];
lean_object* v_args_2671_ = _args[6];
lean_object* v_onAlt_2672_ = _args[7];
lean_object* v_next_2673_ = _args[8];
lean_object* v_toBind_2674_ = _args[9];
lean_object* v___x_2675_ = _args[10];
lean_object* v___f_2676_ = _args[11];
lean_object* v_fst_2677_ = _args[12];
lean_object* v_inst_2678_ = _args[13];
lean_object* v_inst_2679_ = _args[14];
lean_object* v_ys3_2680_ = _args[15];
lean_object* v_altType_2681_ = _args[16];
_start:
{
uint8_t v___x_13459__boxed_2682_; uint8_t v_useSplitter_boxed_2683_; lean_object* v_res_2684_; 
v___x_13459__boxed_2682_ = lean_unbox(v___x_2668_);
v_useSplitter_boxed_2683_ = lean_unbox(v_useSplitter_2669_);
v_res_2684_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_toMonadExceptOf_2665_, v_ys_2666_, v_ys2_2667_, v___x_13459__boxed_2682_, v_useSplitter_boxed_2683_, v_inst_2670_, v_args_2671_, v_onAlt_2672_, v_next_2673_, v_toBind_2674_, v___x_2675_, v___f_2676_, v_fst_2677_, v_inst_2678_, v_inst_2679_, v_ys3_2680_, v_altType_2681_);
return v_res_2684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_toMonadExceptOf_2685_, lean_object* v_ys_2686_, uint8_t v___x_2687_, uint8_t v_useSplitter_2688_, lean_object* v_inst_2689_, lean_object* v_args_2690_, lean_object* v_onAlt_2691_, lean_object* v_next_2692_, lean_object* v_toBind_2693_, lean_object* v___x_2694_, lean_object* v___f_2695_, lean_object* v_fst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_numDiscrEqs_2699_, lean_object* v_ys2_2700_, lean_object* v_altType_2701_){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2702_ = lean_box(v___x_2687_);
v___x_2703_ = lean_box(v_useSplitter_2688_);
lean_inc_ref(v_inst_2698_);
lean_inc_ref(v_inst_2697_);
v___f_2704_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2704_, 0, v_toMonadExceptOf_2685_);
lean_closure_set(v___f_2704_, 1, v_ys_2686_);
lean_closure_set(v___f_2704_, 2, v_ys2_2700_);
lean_closure_set(v___f_2704_, 3, v___x_2702_);
lean_closure_set(v___f_2704_, 4, v___x_2703_);
lean_closure_set(v___f_2704_, 5, v_inst_2689_);
lean_closure_set(v___f_2704_, 6, v_args_2690_);
lean_closure_set(v___f_2704_, 7, v_onAlt_2691_);
lean_closure_set(v___f_2704_, 8, v_next_2692_);
lean_closure_set(v___f_2704_, 9, v_toBind_2693_);
lean_closure_set(v___f_2704_, 10, v___x_2694_);
lean_closure_set(v___f_2704_, 11, v___f_2695_);
lean_closure_set(v___f_2704_, 12, v_fst_2696_);
lean_closure_set(v___f_2704_, 13, v_inst_2697_);
lean_closure_set(v___f_2704_, 14, v_inst_2698_);
v___x_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2705_, 0, v_numDiscrEqs_2699_);
v___x_2706_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2697_, v_inst_2698_, v_altType_2701_, v___x_2705_, v___f_2704_, v___x_2687_, v___x_2687_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_toMonadExceptOf_2707_ = _args[0];
lean_object* v_ys_2708_ = _args[1];
lean_object* v___x_2709_ = _args[2];
lean_object* v_useSplitter_2710_ = _args[3];
lean_object* v_inst_2711_ = _args[4];
lean_object* v_args_2712_ = _args[5];
lean_object* v_onAlt_2713_ = _args[6];
lean_object* v_next_2714_ = _args[7];
lean_object* v_toBind_2715_ = _args[8];
lean_object* v___x_2716_ = _args[9];
lean_object* v___f_2717_ = _args[10];
lean_object* v_fst_2718_ = _args[11];
lean_object* v_inst_2719_ = _args[12];
lean_object* v_inst_2720_ = _args[13];
lean_object* v_numDiscrEqs_2721_ = _args[14];
lean_object* v_ys2_2722_ = _args[15];
lean_object* v_altType_2723_ = _args[16];
_start:
{
uint8_t v___x_13487__boxed_2724_; uint8_t v_useSplitter_boxed_2725_; lean_object* v_res_2726_; 
v___x_13487__boxed_2724_ = lean_unbox(v___x_2709_);
v_useSplitter_boxed_2725_ = lean_unbox(v_useSplitter_2710_);
v_res_2726_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_toMonadExceptOf_2707_, v_ys_2708_, v___x_13487__boxed_2724_, v_useSplitter_boxed_2725_, v_inst_2711_, v_args_2712_, v_onAlt_2713_, v_next_2714_, v_toBind_2715_, v___x_2716_, v___f_2717_, v_fst_2718_, v_inst_2719_, v_inst_2720_, v_numDiscrEqs_2721_, v_ys2_2722_, v_altType_2723_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v___f_2730_, uint8_t v___x_2731_, lean_object* v_toBind_2732_, lean_object* v___f_2733_, lean_object* v_altType_2734_){
_start:
{
lean_object* v_numOverlaps_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v_numOverlaps_2735_ = lean_ctor_get(v___x_2727_, 1);
lean_inc(v_numOverlaps_2735_);
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_numOverlaps_2735_);
v___x_2737_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2728_, v_inst_2729_, v_altType_2734_, v___x_2736_, v___f_2730_, v___x_2731_, v___x_2731_);
v___x_2738_ = lean_apply_4(v_toBind_2732_, lean_box(0), lean_box(0), v___x_2737_, v___f_2733_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v___f_2742_, lean_object* v___x_2743_, lean_object* v_toBind_2744_, lean_object* v___f_2745_, lean_object* v_altType_2746_){
_start:
{
uint8_t v___x_13519__boxed_2747_; lean_object* v_res_2748_; 
v___x_13519__boxed_2747_ = lean_unbox(v___x_2743_);
v_res_2748_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2739_, v_inst_2740_, v_inst_2741_, v___f_2742_, v___x_13519__boxed_2747_, v_toBind_2744_, v___f_2745_, v_altType_2746_);
lean_dec_ref(v___x_2739_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2749_, lean_object* v_altType_2750_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_apply_1(v___f_2749_, v_altType_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_box(0);
v___x_2757_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2758_ = l_Lean_mkConst(v___x_2757_, v___x_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* v___x_2759_, lean_object* v_toPure_2760_, lean_object* v_toBind_2761_, lean_object* v___f_2762_, lean_object* v___x_2763_, lean_object* v_inst_2764_, lean_object* v___f_2765_, lean_object* v_altType_2766_){
_start:
{
uint8_t v_hasUnitThunk_2767_; 
v_hasUnitThunk_2767_ = lean_ctor_get_uint8(v___x_2759_, sizeof(void*)*2);
if (v_hasUnitThunk_2767_ == 0)
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
lean_dec(v___f_2765_);
lean_dec(v_inst_2764_);
v___x_2768_ = lean_apply_2(v_toPure_2760_, lean_box(0), v_altType_2766_);
v___x_2769_ = lean_apply_4(v_toBind_2761_, lean_box(0), lean_box(0), v___x_2768_, v___f_2762_);
return v___x_2769_;
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_dec(v___f_2762_);
lean_dec(v_toPure_2760_);
v___x_2770_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2771_ = lean_mk_empty_array_with_capacity(v___x_2763_);
v___x_2772_ = lean_array_push(v___x_2771_, v___x_2770_);
v___x_2773_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2773_, 0, v_altType_2766_);
lean_closure_set(v___x_2773_, 1, v___x_2772_);
v___x_2774_ = lean_apply_2(v_inst_2764_, lean_box(0), v___x_2773_);
v___x_2775_ = lean_apply_4(v_toBind_2761_, lean_box(0), lean_box(0), v___x_2774_, v___f_2765_);
return v___x_2775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v___x_2776_, lean_object* v_toPure_2777_, lean_object* v_toBind_2778_, lean_object* v___f_2779_, lean_object* v___x_2780_, lean_object* v_inst_2781_, lean_object* v___f_2782_, lean_object* v_altType_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v___x_2776_, v_toPure_2777_, v_toBind_2778_, v___f_2779_, v___x_2780_, v_inst_2781_, v___f_2782_, v_altType_2783_);
lean_dec(v___x_2780_);
lean_dec_ref(v___x_2776_);
return v_res_2784_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2788_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2789_ = lean_unsigned_to_nat(8u);
v___x_2790_ = lean_unsigned_to_nat(363u);
v___x_2791_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2792_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2793_ = l_mkPanicMessageWithDecl(v___x_2792_, v___x_2791_, v___x_2790_, v___x_2789_, v___x_2788_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2794_, lean_object* v___x_2795_, lean_object* v_toMonadExceptOf_2796_, uint8_t v___x_2797_, uint8_t v_useSplitter_2798_, lean_object* v_inst_2799_, lean_object* v_onAlt_2800_, lean_object* v_next_2801_, lean_object* v_toBind_2802_, lean_object* v___x_2803_, lean_object* v___f_2804_, lean_object* v_fst_2805_, lean_object* v_inst_2806_, lean_object* v_inst_2807_, lean_object* v_numDiscrEqs_2808_, lean_object* v___f_2809_, lean_object* v___x_2810_, lean_object* v_toPure_2811_, lean_object* v___x_2812_, lean_object* v___x_2813_, lean_object* v_ys_2814_, lean_object* v_args_2815_){
_start:
{
lean_object* v_numFields_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v_numFields_2816_ = lean_ctor_get(v___x_2794_, 0);
v___x_2817_ = lean_array_get_size(v_ys_2814_);
v___x_2818_ = lean_nat_dec_eq(v___x_2817_, v_numFields_2816_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_dec_ref(v_args_2815_);
lean_dec_ref(v_ys_2814_);
lean_dec_ref(v___x_2813_);
lean_dec(v___x_2812_);
lean_dec(v_toPure_2811_);
lean_dec_ref(v___x_2810_);
lean_dec(v___f_2809_);
lean_dec(v_numDiscrEqs_2808_);
lean_dec_ref(v_inst_2807_);
lean_dec_ref(v_inst_2806_);
lean_dec(v_fst_2805_);
lean_dec(v___f_2804_);
lean_dec_ref(v___x_2803_);
lean_dec(v_toBind_2802_);
lean_dec(v_next_2801_);
lean_dec(v_onAlt_2800_);
lean_dec(v_inst_2799_);
lean_dec_ref(v_toMonadExceptOf_2796_);
lean_dec_ref(v___x_2794_);
v___x_2819_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2820_ = l_panic___redArg(v___x_2795_, v___x_2819_);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___f_2826_; lean_object* v___f_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2821_ = lean_box(v___x_2797_);
v___x_2822_ = lean_box(v_useSplitter_2798_);
lean_inc_ref(v_inst_2807_);
lean_inc_ref(v_inst_2806_);
lean_inc_n(v_toBind_2802_, 3);
lean_inc_n(v_inst_2799_, 2);
lean_inc_ref(v_ys_2814_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2823_, 0, v_toMonadExceptOf_2796_);
lean_closure_set(v___f_2823_, 1, v_ys_2814_);
lean_closure_set(v___f_2823_, 2, v___x_2821_);
lean_closure_set(v___f_2823_, 3, v___x_2822_);
lean_closure_set(v___f_2823_, 4, v_inst_2799_);
lean_closure_set(v___f_2823_, 5, v_args_2815_);
lean_closure_set(v___f_2823_, 6, v_onAlt_2800_);
lean_closure_set(v___f_2823_, 7, v_next_2801_);
lean_closure_set(v___f_2823_, 8, v_toBind_2802_);
lean_closure_set(v___f_2823_, 9, v___x_2803_);
lean_closure_set(v___f_2823_, 10, v___f_2804_);
lean_closure_set(v___f_2823_, 11, v_fst_2805_);
lean_closure_set(v___f_2823_, 12, v_inst_2806_);
lean_closure_set(v___f_2823_, 13, v_inst_2807_);
lean_closure_set(v___f_2823_, 14, v_numDiscrEqs_2808_);
v___x_2824_ = lean_box(v___x_2797_);
v___f_2825_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2825_, 0, v___x_2794_);
lean_closure_set(v___f_2825_, 1, v_inst_2806_);
lean_closure_set(v___f_2825_, 2, v_inst_2807_);
lean_closure_set(v___f_2825_, 3, v___f_2823_);
lean_closure_set(v___f_2825_, 4, v___x_2824_);
lean_closure_set(v___f_2825_, 5, v_toBind_2802_);
lean_closure_set(v___f_2825_, 6, v___f_2809_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2826_, 0, v___f_2825_);
lean_inc_ref(v___f_2826_);
v___f_2827_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2827_, 0, v___x_2810_);
lean_closure_set(v___f_2827_, 1, v_toPure_2811_);
lean_closure_set(v___f_2827_, 2, v_toBind_2802_);
lean_closure_set(v___f_2827_, 3, v___f_2826_);
lean_closure_set(v___f_2827_, 4, v___x_2812_);
lean_closure_set(v___f_2827_, 5, v_inst_2799_);
lean_closure_set(v___f_2827_, 6, v___f_2826_);
v___x_2828_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2828_, 0, v___x_2813_);
lean_closure_set(v___x_2828_, 1, v_ys_2814_);
v___x_2829_ = lean_apply_2(v_inst_2799_, lean_box(0), v___x_2828_);
v___x_2830_ = lean_apply_4(v_toBind_2802_, lean_box(0), lean_box(0), v___x_2829_, v___f_2827_);
return v___x_2830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2831_ = _args[0];
lean_object* v___x_2832_ = _args[1];
lean_object* v_toMonadExceptOf_2833_ = _args[2];
lean_object* v___x_2834_ = _args[3];
lean_object* v_useSplitter_2835_ = _args[4];
lean_object* v_inst_2836_ = _args[5];
lean_object* v_onAlt_2837_ = _args[6];
lean_object* v_next_2838_ = _args[7];
lean_object* v_toBind_2839_ = _args[8];
lean_object* v___x_2840_ = _args[9];
lean_object* v___f_2841_ = _args[10];
lean_object* v_fst_2842_ = _args[11];
lean_object* v_inst_2843_ = _args[12];
lean_object* v_inst_2844_ = _args[13];
lean_object* v_numDiscrEqs_2845_ = _args[14];
lean_object* v___f_2846_ = _args[15];
lean_object* v___x_2847_ = _args[16];
lean_object* v_toPure_2848_ = _args[17];
lean_object* v___x_2849_ = _args[18];
lean_object* v___x_2850_ = _args[19];
lean_object* v_ys_2851_ = _args[20];
lean_object* v_args_2852_ = _args[21];
_start:
{
uint8_t v___x_13616__boxed_2853_; uint8_t v_useSplitter_boxed_2854_; lean_object* v_res_2855_; 
v___x_13616__boxed_2853_ = lean_unbox(v___x_2834_);
v_useSplitter_boxed_2854_ = lean_unbox(v_useSplitter_2835_);
v_res_2855_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2831_, v___x_2832_, v_toMonadExceptOf_2833_, v___x_13616__boxed_2853_, v_useSplitter_boxed_2854_, v_inst_2836_, v_onAlt_2837_, v_next_2838_, v_toBind_2839_, v___x_2840_, v___f_2841_, v_fst_2842_, v_inst_2843_, v_inst_2844_, v_numDiscrEqs_2845_, v___f_2846_, v___x_2847_, v_toPure_2848_, v___x_2849_, v___x_2850_, v_ys_2851_, v_args_2852_);
lean_dec(v___x_2832_);
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
lean_object* v_snd_2902_; lean_object* v_snd_2903_; lean_object* v_snd_2904_; lean_object* v_snd_2905_; lean_object* v_snd_2906_; lean_object* v_fst_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_3117_; 
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
v_isSharedCheck_3117_ = !lean_is_exclusive(v_acc_2897_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v_acc_2897_, 1);
lean_dec(v_unused_3118_);
v___x_2909_ = v_acc_2897_;
v_isShared_2910_ = v_isSharedCheck_3117_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_fst_2907_);
lean_dec(v_acc_2897_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_3117_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v_fst_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3115_; 
v_fst_2911_ = lean_ctor_get(v_snd_2902_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v_snd_2902_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v_snd_2902_, 1);
lean_dec(v_unused_3116_);
v___x_2913_ = v_snd_2902_;
v_isShared_2914_ = v_isSharedCheck_3115_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_fst_2911_);
lean_dec(v_snd_2902_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3115_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_fst_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_3113_; 
v_fst_2915_ = lean_ctor_get(v_snd_2903_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_snd_2903_);
if (v_isSharedCheck_3113_ == 0)
{
lean_object* v_unused_3114_; 
v_unused_3114_ = lean_ctor_get(v_snd_2903_, 1);
lean_dec(v_unused_3114_);
v___x_2917_ = v_snd_2903_;
v_isShared_2918_ = v_isSharedCheck_3113_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_fst_2915_);
lean_dec(v_snd_2903_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_3113_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_fst_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_3111_; 
v_fst_2919_ = lean_ctor_get(v_snd_2904_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_snd_2904_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v_snd_2904_, 1);
lean_dec(v_unused_3112_);
v___x_2921_ = v_snd_2904_;
v_isShared_2922_ = v_isSharedCheck_3111_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_fst_2919_);
lean_dec(v_snd_2904_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_3111_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v_fst_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_3109_; 
v_fst_2923_ = lean_ctor_get(v_snd_2905_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v_snd_2905_);
if (v_isSharedCheck_3109_ == 0)
{
lean_object* v_unused_3110_; 
v_unused_3110_ = lean_ctor_get(v_snd_2905_, 1);
lean_dec(v_unused_3110_);
v___x_2925_ = v_snd_2905_;
v_isShared_2926_ = v_isSharedCheck_3109_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_fst_2923_);
lean_dec(v_snd_2905_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_3109_;
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
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_3105_; 
lean_inc(v_stop_2929_);
lean_inc(v_start_2928_);
lean_inc_ref(v_array_2927_);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_snd_2906_);
if (v_isSharedCheck_3105_ == 0)
{
lean_object* v_unused_3106_; lean_object* v_unused_3107_; lean_object* v_unused_3108_; 
v_unused_3106_ = lean_ctor_get(v_snd_2906_, 2);
lean_dec(v_unused_3106_);
v_unused_3107_ = lean_ctor_get(v_snd_2906_, 1);
lean_dec(v_unused_3107_);
v_unused_3108_ = lean_ctor_get(v_snd_2906_, 0);
lean_dec(v_unused_3108_);
v___x_2954_ = v_snd_2906_;
v_isShared_2955_ = v_isSharedCheck_3105_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v_snd_2906_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_3105_;
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
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_array_2927_);
lean_ctor_set(v_reuseFailAlloc_3104_, 1, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_stop_2929_);
v___x_2963_ = v_reuseFailAlloc_3104_;
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
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_3100_; 
lean_inc(v_stop_2958_);
lean_inc(v_start_2957_);
lean_inc_ref(v_array_2956_);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_fst_2923_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; lean_object* v_unused_3102_; lean_object* v_unused_3103_; 
v_unused_3101_ = lean_ctor_get(v_fst_2923_, 2);
lean_dec(v_unused_3101_);
v_unused_3102_ = lean_ctor_get(v_fst_2923_, 1);
lean_dec(v_unused_3102_);
v_unused_3103_ = lean_ctor_get(v_fst_2923_, 0);
lean_dec(v_unused_3103_);
v___x_2983_ = v_fst_2923_;
v_isShared_2984_ = v_isSharedCheck_3100_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v_fst_2923_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_3100_;
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
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_array_2956_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_3099_, 2, v_stop_2958_);
v___x_2991_ = v_reuseFailAlloc_3099_;
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
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3095_; 
lean_inc(v_stop_2987_);
lean_inc(v_start_2986_);
lean_inc_ref(v_array_2985_);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_fst_2919_);
if (v_isSharedCheck_3095_ == 0)
{
lean_object* v_unused_3096_; lean_object* v_unused_3097_; lean_object* v_unused_3098_; 
v_unused_3096_ = lean_ctor_get(v_fst_2919_, 2);
lean_dec(v_unused_3096_);
v_unused_3097_ = lean_ctor_get(v_fst_2919_, 1);
lean_dec(v_unused_3097_);
v_unused_3098_ = lean_ctor_get(v_fst_2919_, 0);
lean_dec(v_unused_3098_);
v___x_3011_ = v_fst_2919_;
v_isShared_3012_ = v_isSharedCheck_3095_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v_fst_2919_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3095_;
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
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_array_2985_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3094_, 2, v_stop_2987_);
v___x_3019_ = v_reuseFailAlloc_3094_;
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
lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3090_; 
lean_inc(v_stop_3015_);
lean_inc(v_start_3014_);
lean_inc_ref(v_array_3013_);
v_isSharedCheck_3090_ = !lean_is_exclusive(v_fst_2915_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; lean_object* v_unused_3092_; lean_object* v_unused_3093_; 
v_unused_3091_ = lean_ctor_get(v_fst_2915_, 2);
lean_dec(v_unused_3091_);
v_unused_3092_ = lean_ctor_get(v_fst_2915_, 1);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v_fst_2915_, 0);
lean_dec(v_unused_3093_);
v___x_3039_ = v_fst_2915_;
v_isShared_3040_ = v_isSharedCheck_3090_;
goto v_resetjp_3038_;
}
else
{
lean_dec(v_fst_2915_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3090_;
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
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_array_3013_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_stop_3015_);
v___x_3047_ = v_reuseFailAlloc_3089_;
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
lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3085_; 
lean_inc(v_stop_3043_);
lean_inc(v_start_3042_);
lean_inc_ref(v_array_3041_);
lean_del_object(v___x_2925_);
lean_del_object(v___x_2921_);
lean_del_object(v___x_2917_);
lean_del_object(v___x_2913_);
lean_del_object(v___x_2909_);
v_isSharedCheck_3085_ = !lean_is_exclusive(v_fst_2911_);
if (v_isSharedCheck_3085_ == 0)
{
lean_object* v_unused_3086_; lean_object* v_unused_3087_; lean_object* v_unused_3088_; 
v_unused_3086_ = lean_ctor_get(v_fst_2911_, 2);
lean_dec(v_unused_3086_);
v_unused_3087_ = lean_ctor_get(v_fst_2911_, 1);
lean_dec(v_unused_3087_);
v_unused_3088_ = lean_ctor_get(v_fst_2911_, 0);
lean_dec(v_unused_3088_);
v___x_3067_ = v_fst_2911_;
v_isShared_3068_ = v_isSharedCheck_3085_;
goto v_resetjp_3066_;
}
else
{
lean_dec(v_fst_2911_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3085_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v_numOverlaps_3069_; uint8_t v___x_3070_; 
v_numOverlaps_3069_ = lean_ctor_get(v___x_3044_, 1);
v___x_3070_ = lean_nat_dec_eq(v_numOverlaps_3069_, v___x_2883_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
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
v___x_3071_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_3072_ = l_panic___redArg(v___x_2884_, v___x_3071_);
v___y_2932_ = v___x_3072_;
goto v___jp_2931_;
}
else
{
lean_object* v___f_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___f_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
lean_inc(v_inst_2885_);
lean_inc_n(v_toPure_2880_, 2);
lean_inc(v___x_3016_);
v___f_3073_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_3073_, 0, v___x_3016_);
lean_closure_set(v___f_3073_, 1, v_toPure_2880_);
lean_closure_set(v___f_3073_, 2, v_inst_2885_);
v___x_3074_ = lean_array_fget_borrowed(v_array_3041_, v_start_3042_);
v___x_3075_ = lean_box(v___x_2888_);
v___x_3076_ = lean_box(v_useSplitter_2889_);
lean_inc(v___x_3044_);
lean_inc_ref(v_inst_2894_);
lean_inc_ref(v_inst_2893_);
lean_inc(v___x_3074_);
lean_inc(v_toBind_2881_);
v___f_3077_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 22, 20);
lean_closure_set(v___f_3077_, 0, v___x_3016_);
lean_closure_set(v___f_3077_, 1, v___x_2886_);
lean_closure_set(v___f_3077_, 2, v_toMonadExceptOf_2887_);
lean_closure_set(v___f_3077_, 3, v___x_3075_);
lean_closure_set(v___f_3077_, 4, v___x_3076_);
lean_closure_set(v___f_3077_, 5, v_inst_2885_);
lean_closure_set(v___f_3077_, 6, v_onAlt_2890_);
lean_closure_set(v___f_3077_, 7, v_next_2896_);
lean_closure_set(v___f_3077_, 8, v_toBind_2881_);
lean_closure_set(v___f_3077_, 9, v___x_3074_);
lean_closure_set(v___f_3077_, 10, v___f_2891_);
lean_closure_set(v___f_3077_, 11, v_fst_2892_);
lean_closure_set(v___f_3077_, 12, v_inst_2893_);
lean_closure_set(v___f_3077_, 13, v_inst_2894_);
lean_closure_set(v___f_3077_, 14, v_numDiscrEqs_2895_);
lean_closure_set(v___f_3077_, 15, v___f_3073_);
lean_closure_set(v___f_3077_, 16, v___x_3044_);
lean_closure_set(v___f_3077_, 17, v_toPure_2880_);
lean_closure_set(v___f_3077_, 18, v___x_2960_);
lean_closure_set(v___f_3077_, 19, v___x_2959_);
v___x_3078_ = lean_nat_add(v_start_3042_, v___x_2960_);
lean_dec(v_start_3042_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 1, v___x_3078_);
v___x_3080_ = v___x_3067_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_array_3041_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3084_, 2, v_stop_3043_);
v___x_3080_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___f_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___f_3081_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3081_, 0, v_fst_2907_);
lean_closure_set(v___f_3081_, 1, v___x_2991_);
lean_closure_set(v___f_3081_, 2, v___x_2963_);
lean_closure_set(v___f_3081_, 3, v___x_3019_);
lean_closure_set(v___f_3081_, 4, v___x_3047_);
lean_closure_set(v___f_3081_, 5, v___x_3080_);
lean_closure_set(v___f_3081_, 6, v_toPure_2880_);
v___x_3082_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2894_, v_inst_2893_, v___x_2988_, v___x_3044_, v___f_3077_);
lean_inc(v_toBind_2881_);
v___x_3083_ = lean_apply_4(v_toBind_2881_, lean_box(0), lean_box(0), v___x_3082_, v___f_3081_);
v___y_2932_ = v___x_3083_;
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
lean_object* v___x_3119_ = _args[0];
lean_object* v_toPure_3120_ = _args[1];
lean_object* v_toBind_3121_ = _args[2];
lean_object* v___f_3122_ = _args[3];
lean_object* v___x_3123_ = _args[4];
lean_object* v___x_3124_ = _args[5];
lean_object* v_inst_3125_ = _args[6];
lean_object* v___x_3126_ = _args[7];
lean_object* v_toMonadExceptOf_3127_ = _args[8];
lean_object* v___x_3128_ = _args[9];
lean_object* v_useSplitter_3129_ = _args[10];
lean_object* v_onAlt_3130_ = _args[11];
lean_object* v___f_3131_ = _args[12];
lean_object* v_fst_3132_ = _args[13];
lean_object* v_inst_3133_ = _args[14];
lean_object* v_inst_3134_ = _args[15];
lean_object* v_numDiscrEqs_3135_ = _args[16];
lean_object* v_next_3136_ = _args[17];
lean_object* v_acc_3137_ = _args[18];
lean_object* v_h_3138_ = _args[19];
lean_object* v_G_3139_ = _args[20];
_start:
{
uint8_t v___x_13735__boxed_3140_; uint8_t v_useSplitter_boxed_3141_; lean_object* v_res_3142_; 
v___x_13735__boxed_3140_ = lean_unbox(v___x_3128_);
v_useSplitter_boxed_3141_ = lean_unbox(v_useSplitter_3129_);
v_res_3142_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3119_, v_toPure_3120_, v_toBind_3121_, v___f_3122_, v___x_3123_, v___x_3124_, v_inst_3125_, v___x_3126_, v_toMonadExceptOf_3127_, v___x_13735__boxed_3140_, v_useSplitter_boxed_3141_, v_onAlt_3130_, v___f_3131_, v_fst_3132_, v_inst_3133_, v_inst_3134_, v_numDiscrEqs_3135_, v_next_3136_, v_acc_3137_, v_h_3138_, v_G_3139_);
lean_dec(v___x_3124_);
lean_dec(v___x_3123_);
lean_dec(v___x_3119_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3143_, lean_object* v_numParams_3144_, lean_object* v_numDiscrs_3145_, lean_object* v_altInfos_3146_, lean_object* v_uElimPos_x3f_3147_, lean_object* v_snd_3148_, lean_object* v_overlaps_3149_, lean_object* v_splitterName_3150_, lean_object* v_matcherLevels_3151_, lean_object* v_params_x27_3152_, lean_object* v_fst_3153_, lean_object* v_discrs_x27_3154_, lean_object* v_fst_3155_, lean_object* v_toPure_3156_, lean_object* v_____do__lift_3157_){
_start:
{
lean_object* v_remaining_x27_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v_remaining_x27_3158_ = l_Array_append___redArg(v_fst_3143_, v_____do__lift_3157_);
v___x_3159_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3159_, 0, v_numParams_3144_);
lean_ctor_set(v___x_3159_, 1, v_numDiscrs_3145_);
lean_ctor_set(v___x_3159_, 2, v_altInfos_3146_);
lean_ctor_set(v___x_3159_, 3, v_uElimPos_x3f_3147_);
lean_ctor_set(v___x_3159_, 4, v_snd_3148_);
lean_ctor_set(v___x_3159_, 5, v_overlaps_3149_);
v___x_3160_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v_splitterName_3150_);
lean_ctor_set(v___x_3160_, 2, v_matcherLevels_3151_);
lean_ctor_set(v___x_3160_, 3, v_params_x27_3152_);
lean_ctor_set(v___x_3160_, 4, v_fst_3153_);
lean_ctor_set(v___x_3160_, 5, v_discrs_x27_3154_);
lean_ctor_set(v___x_3160_, 6, v_fst_3155_);
lean_ctor_set(v___x_3160_, 7, v_remaining_x27_3158_);
v___x_3161_ = lean_apply_2(v_toPure_3156_, lean_box(0), v___x_3160_);
return v___x_3161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3162_, lean_object* v_numParams_3163_, lean_object* v_numDiscrs_3164_, lean_object* v_altInfos_3165_, lean_object* v_uElimPos_x3f_3166_, lean_object* v_snd_3167_, lean_object* v_overlaps_3168_, lean_object* v_splitterName_3169_, lean_object* v_matcherLevels_3170_, lean_object* v_params_x27_3171_, lean_object* v_fst_3172_, lean_object* v_discrs_x27_3173_, lean_object* v_fst_3174_, lean_object* v_toPure_3175_, lean_object* v_____do__lift_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3162_, v_numParams_3163_, v_numDiscrs_3164_, v_altInfos_3165_, v_uElimPos_x3f_3166_, v_snd_3167_, v_overlaps_3168_, v_splitterName_3169_, v_matcherLevels_3170_, v_params_x27_3171_, v_fst_3172_, v_discrs_x27_3173_, v_fst_3174_, v_toPure_3175_, v_____do__lift_3176_);
lean_dec_ref(v_____do__lift_3176_);
return v_res_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3178_, lean_object* v_numParams_3179_, lean_object* v_numDiscrs_3180_, lean_object* v_altInfos_3181_, lean_object* v_uElimPos_x3f_3182_, lean_object* v_snd_3183_, lean_object* v_overlaps_3184_, lean_object* v_splitterName_3185_, lean_object* v_matcherLevels_3186_, lean_object* v_params_x27_3187_, lean_object* v_fst_3188_, lean_object* v_discrs_x27_3189_, lean_object* v_toPure_3190_, lean_object* v_onRemaining_3191_, lean_object* v_remaining_3192_, lean_object* v_toBind_3193_, lean_object* v_____s_3194_){
_start:
{
lean_object* v_fst_3195_; lean_object* v___f_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_fst_3195_ = lean_ctor_get(v_____s_3194_, 0);
lean_inc(v_fst_3195_);
lean_dec_ref(v_____s_3194_);
v___f_3196_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3196_, 0, v_fst_3178_);
lean_closure_set(v___f_3196_, 1, v_numParams_3179_);
lean_closure_set(v___f_3196_, 2, v_numDiscrs_3180_);
lean_closure_set(v___f_3196_, 3, v_altInfos_3181_);
lean_closure_set(v___f_3196_, 4, v_uElimPos_x3f_3182_);
lean_closure_set(v___f_3196_, 5, v_snd_3183_);
lean_closure_set(v___f_3196_, 6, v_overlaps_3184_);
lean_closure_set(v___f_3196_, 7, v_splitterName_3185_);
lean_closure_set(v___f_3196_, 8, v_matcherLevels_3186_);
lean_closure_set(v___f_3196_, 9, v_params_x27_3187_);
lean_closure_set(v___f_3196_, 10, v_fst_3188_);
lean_closure_set(v___f_3196_, 11, v_discrs_x27_3189_);
lean_closure_set(v___f_3196_, 12, v_fst_3195_);
lean_closure_set(v___f_3196_, 13, v_toPure_3190_);
v___x_3197_ = lean_apply_1(v_onRemaining_3191_, v_remaining_3192_);
v___x_3198_ = lean_apply_4(v_toBind_3193_, lean_box(0), lean_box(0), v___x_3197_, v___f_3196_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3199_ = _args[0];
lean_object* v_numParams_3200_ = _args[1];
lean_object* v_numDiscrs_3201_ = _args[2];
lean_object* v_altInfos_3202_ = _args[3];
lean_object* v_uElimPos_x3f_3203_ = _args[4];
lean_object* v_snd_3204_ = _args[5];
lean_object* v_overlaps_3205_ = _args[6];
lean_object* v_splitterName_3206_ = _args[7];
lean_object* v_matcherLevels_3207_ = _args[8];
lean_object* v_params_x27_3208_ = _args[9];
lean_object* v_fst_3209_ = _args[10];
lean_object* v_discrs_x27_3210_ = _args[11];
lean_object* v_toPure_3211_ = _args[12];
lean_object* v_onRemaining_3212_ = _args[13];
lean_object* v_remaining_3213_ = _args[14];
lean_object* v_toBind_3214_ = _args[15];
lean_object* v_____s_3215_ = _args[16];
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3199_, v_numParams_3200_, v_numDiscrs_3201_, v_altInfos_3202_, v_uElimPos_x3f_3203_, v_snd_3204_, v_overlaps_3205_, v_splitterName_3206_, v_matcherLevels_3207_, v_params_x27_3208_, v_fst_3209_, v_discrs_x27_3210_, v_toPure_3211_, v_onRemaining_3212_, v_remaining_3213_, v_toBind_3214_, v_____s_3215_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3217_, lean_object* v_fst_3218_, lean_object* v_numParams_3219_, lean_object* v_numDiscrs_3220_, lean_object* v_altInfos_3221_, lean_object* v_uElimPos_x3f_3222_, lean_object* v_snd_3223_, lean_object* v_overlaps_3224_, lean_object* v_splitterName_3225_, lean_object* v_matcherLevels_3226_, lean_object* v_params_x27_3227_, lean_object* v_fst_3228_, lean_object* v_discrs_x27_3229_, lean_object* v_toPure_3230_, lean_object* v_onRemaining_3231_, lean_object* v_remaining_3232_, lean_object* v_toBind_3233_, lean_object* v_origAltTypes_3234_, lean_object* v_alts_3235_, lean_object* v___x_3236_, lean_object* v___x_3237_, lean_object* v_remaining_x27_3238_, lean_object* v___f_3239_, lean_object* v_altTypes_3240_){
_start:
{
lean_object* v_altInfos_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_altInfos_3241_ = lean_ctor_get(v_splitterMatchInfo_3217_, 2);
lean_inc_ref(v_altInfos_3241_);
lean_dec_ref(v_splitterMatchInfo_3217_);
lean_inc(v_toBind_3233_);
lean_inc_ref(v_altInfos_3221_);
v___f_3242_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3242_, 0, v_fst_3218_);
lean_closure_set(v___f_3242_, 1, v_numParams_3219_);
lean_closure_set(v___f_3242_, 2, v_numDiscrs_3220_);
lean_closure_set(v___f_3242_, 3, v_altInfos_3221_);
lean_closure_set(v___f_3242_, 4, v_uElimPos_x3f_3222_);
lean_closure_set(v___f_3242_, 5, v_snd_3223_);
lean_closure_set(v___f_3242_, 6, v_overlaps_3224_);
lean_closure_set(v___f_3242_, 7, v_splitterName_3225_);
lean_closure_set(v___f_3242_, 8, v_matcherLevels_3226_);
lean_closure_set(v___f_3242_, 9, v_params_x27_3227_);
lean_closure_set(v___f_3242_, 10, v_fst_3228_);
lean_closure_set(v___f_3242_, 11, v_discrs_x27_3229_);
lean_closure_set(v___f_3242_, 12, v_toPure_3230_);
lean_closure_set(v___f_3242_, 13, v_onRemaining_3231_);
lean_closure_set(v___f_3242_, 14, v_remaining_3232_);
lean_closure_set(v___f_3242_, 15, v_toBind_3233_);
v___x_3243_ = lean_array_get_size(v_altInfos_3221_);
v___x_3244_ = lean_array_get_size(v_altInfos_3241_);
v___x_3245_ = lean_array_get_size(v_origAltTypes_3234_);
v___x_3246_ = lean_array_get_size(v_altTypes_3240_);
lean_inc_n(v___x_3236_, 5);
v___x_3247_ = l_Array_toSubarray___redArg(v_alts_3235_, v___x_3236_, v___x_3237_);
v___x_3248_ = l_Array_toSubarray___redArg(v_altInfos_3221_, v___x_3236_, v___x_3243_);
v___x_3249_ = l_Array_toSubarray___redArg(v_altInfos_3241_, v___x_3236_, v___x_3244_);
v___x_3250_ = l_Array_toSubarray___redArg(v_origAltTypes_3234_, v___x_3236_, v___x_3245_);
v___x_3251_ = l_Array_toSubarray___redArg(v_altTypes_3240_, v___x_3236_, v___x_3246_);
v___x_3252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3250_);
lean_ctor_set(v___x_3252_, 1, v___x_3251_);
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3249_);
lean_ctor_set(v___x_3253_, 1, v___x_3252_);
v___x_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3254_, 0, v___x_3248_);
lean_ctor_set(v___x_3254_, 1, v___x_3253_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3247_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3256_, 0, v_remaining_x27_3238_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
v___x_3257_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3239_, v___x_3236_, v___x_3256_, lean_box(0));
v___x_3258_ = lean_apply_4(v_toBind_3233_, lean_box(0), lean_box(0), v___x_3257_, v___f_3242_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3259_ = _args[0];
lean_object* v_fst_3260_ = _args[1];
lean_object* v_numParams_3261_ = _args[2];
lean_object* v_numDiscrs_3262_ = _args[3];
lean_object* v_altInfos_3263_ = _args[4];
lean_object* v_uElimPos_x3f_3264_ = _args[5];
lean_object* v_snd_3265_ = _args[6];
lean_object* v_overlaps_3266_ = _args[7];
lean_object* v_splitterName_3267_ = _args[8];
lean_object* v_matcherLevels_3268_ = _args[9];
lean_object* v_params_x27_3269_ = _args[10];
lean_object* v_fst_3270_ = _args[11];
lean_object* v_discrs_x27_3271_ = _args[12];
lean_object* v_toPure_3272_ = _args[13];
lean_object* v_onRemaining_3273_ = _args[14];
lean_object* v_remaining_3274_ = _args[15];
lean_object* v_toBind_3275_ = _args[16];
lean_object* v_origAltTypes_3276_ = _args[17];
lean_object* v_alts_3277_ = _args[18];
lean_object* v___x_3278_ = _args[19];
lean_object* v___x_3279_ = _args[20];
lean_object* v_remaining_x27_3280_ = _args[21];
lean_object* v___f_3281_ = _args[22];
lean_object* v_altTypes_3282_ = _args[23];
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3259_, v_fst_3260_, v_numParams_3261_, v_numDiscrs_3262_, v_altInfos_3263_, v_uElimPos_x3f_3264_, v_snd_3265_, v_overlaps_3266_, v_splitterName_3267_, v_matcherLevels_3268_, v_params_x27_3269_, v_fst_3270_, v_discrs_x27_3271_, v_toPure_3272_, v_onRemaining_3273_, v_remaining_3274_, v_toBind_3275_, v_origAltTypes_3276_, v_alts_3277_, v___x_3278_, v___x_3279_, v_remaining_x27_3280_, v___f_3281_, v_altTypes_3282_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3284_, lean_object* v_aux2_3285_, lean_object* v_inst_3286_, lean_object* v_toBind_3287_, lean_object* v___f_3288_, lean_object* v_____r_3289_){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3290_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3290_, 0, v___x_3284_);
lean_closure_set(v___x_3290_, 1, v_aux2_3285_);
v___x_3291_ = lean_apply_2(v_inst_3286_, lean_box(0), v___x_3290_);
v___x_3292_ = lean_apply_4(v_toBind_3287_, lean_box(0), lean_box(0), v___x_3291_, v___f_3288_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3294_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3295_ = l_Lean_stringToMessageData(v___x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3296_, lean_object* v_params_x27_3297_, lean_object* v_fst_3298_, lean_object* v_discrs_x27_3299_, lean_object* v_fst_3300_, lean_object* v_numParams_3301_, lean_object* v_numDiscrs_3302_, lean_object* v_altInfos_3303_, lean_object* v_uElimPos_x3f_3304_, lean_object* v_snd_3305_, lean_object* v_overlaps_3306_, lean_object* v_matcherLevels_3307_, lean_object* v_toPure_3308_, lean_object* v_onRemaining_3309_, lean_object* v_remaining_3310_, lean_object* v_toBind_3311_, lean_object* v_origAltTypes_3312_, lean_object* v_alts_3313_, lean_object* v___x_3314_, lean_object* v___x_3315_, lean_object* v_remaining_x27_3316_, lean_object* v___f_3317_, lean_object* v_inst_3318_, lean_object* v___x_3319_, uint8_t v___x_3320_, lean_object* v_liftWith_3321_, lean_object* v_restoreM_3322_, lean_object* v_matchEqns_3323_){
_start:
{
lean_object* v_splitterName_3324_; lean_object* v_splitterMatchInfo_3325_; lean_object* v___x_3326_; lean_object* v_aux2_3327_; lean_object* v_aux2_3328_; lean_object* v_aux2_3329_; lean_object* v___x_3330_; lean_object* v___f_3331_; lean_object* v___f_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___f_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___f_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_splitterName_3324_ = lean_ctor_get(v_matchEqns_3323_, 1);
lean_inc_n(v_splitterName_3324_, 2);
v_splitterMatchInfo_3325_ = lean_ctor_get(v_matchEqns_3323_, 2);
lean_inc_ref(v_splitterMatchInfo_3325_);
lean_dec_ref(v_matchEqns_3323_);
v___x_3326_ = l_Lean_mkConst(v_splitterName_3324_, v___x_3296_);
v_aux2_3327_ = l_Lean_mkAppN(v___x_3326_, v_params_x27_3297_);
lean_inc_ref(v_fst_3298_);
v_aux2_3328_ = l_Lean_Expr_app___override(v_aux2_3327_, v_fst_3298_);
v_aux2_3329_ = l_Lean_mkAppN(v_aux2_3328_, v_discrs_x27_3299_);
lean_inc_ref_n(v_aux2_3329_, 2);
v___x_3330_ = l_Lean_indentExpr(v_aux2_3329_);
lean_inc(v___x_3315_);
lean_inc_n(v_toBind_3311_, 3);
v___f_3331_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3331_, 0, v_splitterMatchInfo_3325_);
lean_closure_set(v___f_3331_, 1, v_fst_3300_);
lean_closure_set(v___f_3331_, 2, v_numParams_3301_);
lean_closure_set(v___f_3331_, 3, v_numDiscrs_3302_);
lean_closure_set(v___f_3331_, 4, v_altInfos_3303_);
lean_closure_set(v___f_3331_, 5, v_uElimPos_x3f_3304_);
lean_closure_set(v___f_3331_, 6, v_snd_3305_);
lean_closure_set(v___f_3331_, 7, v_overlaps_3306_);
lean_closure_set(v___f_3331_, 8, v_splitterName_3324_);
lean_closure_set(v___f_3331_, 9, v_matcherLevels_3307_);
lean_closure_set(v___f_3331_, 10, v_params_x27_3297_);
lean_closure_set(v___f_3331_, 11, v_fst_3298_);
lean_closure_set(v___f_3331_, 12, v_discrs_x27_3299_);
lean_closure_set(v___f_3331_, 13, v_toPure_3308_);
lean_closure_set(v___f_3331_, 14, v_onRemaining_3309_);
lean_closure_set(v___f_3331_, 15, v_remaining_3310_);
lean_closure_set(v___f_3331_, 16, v_toBind_3311_);
lean_closure_set(v___f_3331_, 17, v_origAltTypes_3312_);
lean_closure_set(v___f_3331_, 18, v_alts_3313_);
lean_closure_set(v___f_3331_, 19, v___x_3314_);
lean_closure_set(v___f_3331_, 20, v___x_3315_);
lean_closure_set(v___f_3331_, 21, v_remaining_x27_3316_);
lean_closure_set(v___f_3331_, 22, v___f_3317_);
lean_inc(v_inst_3318_);
v___f_3332_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3332_, 0, v___x_3315_);
lean_closure_set(v___f_3332_, 1, v_aux2_3329_);
lean_closure_set(v___f_3332_, 2, v_inst_3318_);
lean_closure_set(v___f_3332_, 3, v_toBind_3311_);
lean_closure_set(v___f_3332_, 4, v___f_3331_);
v___x_3333_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v___x_3330_);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v___x_3319_);
v___f_3336_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3336_, 0, v___x_3335_);
v___x_3337_ = lean_box(v___x_3320_);
v___x_3338_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3338_, 0, v_aux2_3329_);
lean_closure_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = lean_apply_2(v_inst_3318_, lean_box(0), v___x_3338_);
v___f_3340_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3340_, 0, v___x_3339_);
lean_closure_set(v___f_3340_, 1, v___f_3336_);
v___x_3341_ = lean_apply_2(v_liftWith_3321_, lean_box(0), v___f_3340_);
v___x_3342_ = lean_apply_1(v_restoreM_3322_, lean_box(0));
v___x_3343_ = lean_apply_4(v_toBind_3311_, lean_box(0), lean_box(0), v___x_3341_, v___x_3342_);
v___x_3344_ = lean_apply_4(v_toBind_3311_, lean_box(0), lean_box(0), v___x_3343_, v___f_3332_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3345_ = _args[0];
lean_object* v_params_x27_3346_ = _args[1];
lean_object* v_fst_3347_ = _args[2];
lean_object* v_discrs_x27_3348_ = _args[3];
lean_object* v_fst_3349_ = _args[4];
lean_object* v_numParams_3350_ = _args[5];
lean_object* v_numDiscrs_3351_ = _args[6];
lean_object* v_altInfos_3352_ = _args[7];
lean_object* v_uElimPos_x3f_3353_ = _args[8];
lean_object* v_snd_3354_ = _args[9];
lean_object* v_overlaps_3355_ = _args[10];
lean_object* v_matcherLevels_3356_ = _args[11];
lean_object* v_toPure_3357_ = _args[12];
lean_object* v_onRemaining_3358_ = _args[13];
lean_object* v_remaining_3359_ = _args[14];
lean_object* v_toBind_3360_ = _args[15];
lean_object* v_origAltTypes_3361_ = _args[16];
lean_object* v_alts_3362_ = _args[17];
lean_object* v___x_3363_ = _args[18];
lean_object* v___x_3364_ = _args[19];
lean_object* v_remaining_x27_3365_ = _args[20];
lean_object* v___f_3366_ = _args[21];
lean_object* v_inst_3367_ = _args[22];
lean_object* v___x_3368_ = _args[23];
lean_object* v___x_3369_ = _args[24];
lean_object* v_liftWith_3370_ = _args[25];
lean_object* v_restoreM_3371_ = _args[26];
lean_object* v_matchEqns_3372_ = _args[27];
_start:
{
uint8_t v___x_14259__boxed_3373_; lean_object* v_res_3374_; 
v___x_14259__boxed_3373_ = lean_unbox(v___x_3369_);
v_res_3374_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3345_, v_params_x27_3346_, v_fst_3347_, v_discrs_x27_3348_, v_fst_3349_, v_numParams_3350_, v_numDiscrs_3351_, v_altInfos_3352_, v_uElimPos_x3f_3353_, v_snd_3354_, v_overlaps_3355_, v_matcherLevels_3356_, v_toPure_3357_, v_onRemaining_3358_, v_remaining_3359_, v_toBind_3360_, v_origAltTypes_3361_, v_alts_3362_, v___x_3363_, v___x_3364_, v_remaining_x27_3365_, v___f_3366_, v_inst_3367_, v___x_3368_, v___x_14259__boxed_3373_, v_liftWith_3370_, v_restoreM_3371_, v_matchEqns_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3375_, lean_object* v_params_x27_3376_, lean_object* v_fst_3377_, lean_object* v_discrs_x27_3378_, lean_object* v_fst_3379_, lean_object* v_numParams_3380_, lean_object* v_numDiscrs_3381_, lean_object* v_altInfos_3382_, lean_object* v_uElimPos_x3f_3383_, lean_object* v_snd_3384_, lean_object* v_overlaps_3385_, lean_object* v_matcherLevels_3386_, lean_object* v_toPure_3387_, lean_object* v_onRemaining_3388_, lean_object* v_remaining_3389_, lean_object* v_toBind_3390_, lean_object* v_alts_3391_, lean_object* v___x_3392_, lean_object* v___x_3393_, lean_object* v_remaining_x27_3394_, lean_object* v___f_3395_, lean_object* v_inst_3396_, lean_object* v___x_3397_, uint8_t v___x_3398_, lean_object* v_liftWith_3399_, lean_object* v_restoreM_3400_, lean_object* v_matcherName_3401_, lean_object* v_origAltTypes_3402_){
_start:
{
lean_object* v___x_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3403_ = lean_box(v___x_3398_);
lean_inc(v_inst_3396_);
lean_inc(v_toBind_3390_);
v___f_3404_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3404_, 0, v___x_3375_);
lean_closure_set(v___f_3404_, 1, v_params_x27_3376_);
lean_closure_set(v___f_3404_, 2, v_fst_3377_);
lean_closure_set(v___f_3404_, 3, v_discrs_x27_3378_);
lean_closure_set(v___f_3404_, 4, v_fst_3379_);
lean_closure_set(v___f_3404_, 5, v_numParams_3380_);
lean_closure_set(v___f_3404_, 6, v_numDiscrs_3381_);
lean_closure_set(v___f_3404_, 7, v_altInfos_3382_);
lean_closure_set(v___f_3404_, 8, v_uElimPos_x3f_3383_);
lean_closure_set(v___f_3404_, 9, v_snd_3384_);
lean_closure_set(v___f_3404_, 10, v_overlaps_3385_);
lean_closure_set(v___f_3404_, 11, v_matcherLevels_3386_);
lean_closure_set(v___f_3404_, 12, v_toPure_3387_);
lean_closure_set(v___f_3404_, 13, v_onRemaining_3388_);
lean_closure_set(v___f_3404_, 14, v_remaining_3389_);
lean_closure_set(v___f_3404_, 15, v_toBind_3390_);
lean_closure_set(v___f_3404_, 16, v_origAltTypes_3402_);
lean_closure_set(v___f_3404_, 17, v_alts_3391_);
lean_closure_set(v___f_3404_, 18, v___x_3392_);
lean_closure_set(v___f_3404_, 19, v___x_3393_);
lean_closure_set(v___f_3404_, 20, v_remaining_x27_3394_);
lean_closure_set(v___f_3404_, 21, v___f_3395_);
lean_closure_set(v___f_3404_, 22, v_inst_3396_);
lean_closure_set(v___f_3404_, 23, v___x_3397_);
lean_closure_set(v___f_3404_, 24, v___x_3403_);
lean_closure_set(v___f_3404_, 25, v_liftWith_3399_);
lean_closure_set(v___f_3404_, 26, v_restoreM_3400_);
v___x_3405_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3405_, 0, v_matcherName_3401_);
v___x_3406_ = lean_apply_2(v_inst_3396_, lean_box(0), v___x_3405_);
v___x_3407_ = lean_apply_4(v_toBind_3390_, lean_box(0), lean_box(0), v___x_3406_, v___f_3404_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3408_ = _args[0];
lean_object* v_params_x27_3409_ = _args[1];
lean_object* v_fst_3410_ = _args[2];
lean_object* v_discrs_x27_3411_ = _args[3];
lean_object* v_fst_3412_ = _args[4];
lean_object* v_numParams_3413_ = _args[5];
lean_object* v_numDiscrs_3414_ = _args[6];
lean_object* v_altInfos_3415_ = _args[7];
lean_object* v_uElimPos_x3f_3416_ = _args[8];
lean_object* v_snd_3417_ = _args[9];
lean_object* v_overlaps_3418_ = _args[10];
lean_object* v_matcherLevels_3419_ = _args[11];
lean_object* v_toPure_3420_ = _args[12];
lean_object* v_onRemaining_3421_ = _args[13];
lean_object* v_remaining_3422_ = _args[14];
lean_object* v_toBind_3423_ = _args[15];
lean_object* v_alts_3424_ = _args[16];
lean_object* v___x_3425_ = _args[17];
lean_object* v___x_3426_ = _args[18];
lean_object* v_remaining_x27_3427_ = _args[19];
lean_object* v___f_3428_ = _args[20];
lean_object* v_inst_3429_ = _args[21];
lean_object* v___x_3430_ = _args[22];
lean_object* v___x_3431_ = _args[23];
lean_object* v_liftWith_3432_ = _args[24];
lean_object* v_restoreM_3433_ = _args[25];
lean_object* v_matcherName_3434_ = _args[26];
lean_object* v_origAltTypes_3435_ = _args[27];
_start:
{
uint8_t v___x_14321__boxed_3436_; lean_object* v_res_3437_; 
v___x_14321__boxed_3436_ = lean_unbox(v___x_3431_);
v_res_3437_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3408_, v_params_x27_3409_, v_fst_3410_, v_discrs_x27_3411_, v_fst_3412_, v_numParams_3413_, v_numDiscrs_3414_, v_altInfos_3415_, v_uElimPos_x3f_3416_, v_snd_3417_, v_overlaps_3418_, v_matcherLevels_3419_, v_toPure_3420_, v_onRemaining_3421_, v_remaining_3422_, v_toBind_3423_, v_alts_3424_, v___x_3425_, v___x_3426_, v_remaining_x27_3427_, v___f_3428_, v_inst_3429_, v___x_3430_, v___x_14321__boxed_3436_, v_liftWith_3432_, v_restoreM_3433_, v_matcherName_3434_, v_origAltTypes_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3438_, lean_object* v_toPure_3439_, lean_object* v_toBind_3440_, lean_object* v___f_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v_inst_3444_, lean_object* v___x_3445_, lean_object* v_toMonadExceptOf_3446_, uint8_t v___x_3447_, uint8_t v_useSplitter_3448_, lean_object* v_onAlt_3449_, lean_object* v___f_3450_, lean_object* v_fst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_numDiscrEqs_3454_, lean_object* v___x_3455_, lean_object* v_params_x27_3456_, lean_object* v_fst_3457_, lean_object* v_discrs_x27_3458_, lean_object* v_fst_3459_, lean_object* v_numParams_3460_, lean_object* v_numDiscrs_3461_, lean_object* v_altInfos_3462_, lean_object* v_uElimPos_x3f_3463_, lean_object* v_snd_3464_, lean_object* v_overlaps_3465_, lean_object* v_matcherLevels_3466_, lean_object* v_onRemaining_3467_, lean_object* v_remaining_3468_, lean_object* v_remaining_x27_3469_, lean_object* v___x_3470_, uint8_t v___x_3471_, lean_object* v_liftWith_3472_, lean_object* v_restoreM_3473_, lean_object* v_matcherName_3474_, lean_object* v_aux1_3475_, lean_object* v_____r_3476_){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___f_3480_; lean_object* v___x_3481_; lean_object* v___f_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3477_ = lean_array_get_size(v_alts_3438_);
v___x_3478_ = lean_box(v___x_3447_);
v___x_3479_ = lean_box(v_useSplitter_3448_);
lean_inc_n(v_inst_3444_, 2);
lean_inc(v___x_3442_);
lean_inc_n(v_toBind_3440_, 2);
lean_inc(v_toPure_3439_);
v___f_3480_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 21, 17);
lean_closure_set(v___f_3480_, 0, v___x_3477_);
lean_closure_set(v___f_3480_, 1, v_toPure_3439_);
lean_closure_set(v___f_3480_, 2, v_toBind_3440_);
lean_closure_set(v___f_3480_, 3, v___f_3441_);
lean_closure_set(v___f_3480_, 4, v___x_3442_);
lean_closure_set(v___f_3480_, 5, v___x_3443_);
lean_closure_set(v___f_3480_, 6, v_inst_3444_);
lean_closure_set(v___f_3480_, 7, v___x_3445_);
lean_closure_set(v___f_3480_, 8, v_toMonadExceptOf_3446_);
lean_closure_set(v___f_3480_, 9, v___x_3478_);
lean_closure_set(v___f_3480_, 10, v___x_3479_);
lean_closure_set(v___f_3480_, 11, v_onAlt_3449_);
lean_closure_set(v___f_3480_, 12, v___f_3450_);
lean_closure_set(v___f_3480_, 13, v_fst_3451_);
lean_closure_set(v___f_3480_, 14, v_inst_3452_);
lean_closure_set(v___f_3480_, 15, v_inst_3453_);
lean_closure_set(v___f_3480_, 16, v_numDiscrEqs_3454_);
v___x_3481_ = lean_box(v___x_3471_);
v___f_3482_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 28, 27);
lean_closure_set(v___f_3482_, 0, v___x_3455_);
lean_closure_set(v___f_3482_, 1, v_params_x27_3456_);
lean_closure_set(v___f_3482_, 2, v_fst_3457_);
lean_closure_set(v___f_3482_, 3, v_discrs_x27_3458_);
lean_closure_set(v___f_3482_, 4, v_fst_3459_);
lean_closure_set(v___f_3482_, 5, v_numParams_3460_);
lean_closure_set(v___f_3482_, 6, v_numDiscrs_3461_);
lean_closure_set(v___f_3482_, 7, v_altInfos_3462_);
lean_closure_set(v___f_3482_, 8, v_uElimPos_x3f_3463_);
lean_closure_set(v___f_3482_, 9, v_snd_3464_);
lean_closure_set(v___f_3482_, 10, v_overlaps_3465_);
lean_closure_set(v___f_3482_, 11, v_matcherLevels_3466_);
lean_closure_set(v___f_3482_, 12, v_toPure_3439_);
lean_closure_set(v___f_3482_, 13, v_onRemaining_3467_);
lean_closure_set(v___f_3482_, 14, v_remaining_3468_);
lean_closure_set(v___f_3482_, 15, v_toBind_3440_);
lean_closure_set(v___f_3482_, 16, v_alts_3438_);
lean_closure_set(v___f_3482_, 17, v___x_3442_);
lean_closure_set(v___f_3482_, 18, v___x_3477_);
lean_closure_set(v___f_3482_, 19, v_remaining_x27_3469_);
lean_closure_set(v___f_3482_, 20, v___f_3480_);
lean_closure_set(v___f_3482_, 21, v_inst_3444_);
lean_closure_set(v___f_3482_, 22, v___x_3470_);
lean_closure_set(v___f_3482_, 23, v___x_3481_);
lean_closure_set(v___f_3482_, 24, v_liftWith_3472_);
lean_closure_set(v___f_3482_, 25, v_restoreM_3473_);
lean_closure_set(v___f_3482_, 26, v_matcherName_3474_);
v___x_3483_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3483_, 0, v___x_3477_);
lean_closure_set(v___x_3483_, 1, v_aux1_3475_);
v___x_3484_ = lean_apply_2(v_inst_3444_, lean_box(0), v___x_3483_);
v___x_3485_ = lean_apply_4(v_toBind_3440_, lean_box(0), lean_box(0), v___x_3484_, v___f_3482_);
return v___x_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3486_ = _args[0];
lean_object* v_toPure_3487_ = _args[1];
lean_object* v_toBind_3488_ = _args[2];
lean_object* v___f_3489_ = _args[3];
lean_object* v___x_3490_ = _args[4];
lean_object* v___x_3491_ = _args[5];
lean_object* v_inst_3492_ = _args[6];
lean_object* v___x_3493_ = _args[7];
lean_object* v_toMonadExceptOf_3494_ = _args[8];
lean_object* v___x_3495_ = _args[9];
lean_object* v_useSplitter_3496_ = _args[10];
lean_object* v_onAlt_3497_ = _args[11];
lean_object* v___f_3498_ = _args[12];
lean_object* v_fst_3499_ = _args[13];
lean_object* v_inst_3500_ = _args[14];
lean_object* v_inst_3501_ = _args[15];
lean_object* v_numDiscrEqs_3502_ = _args[16];
lean_object* v___x_3503_ = _args[17];
lean_object* v_params_x27_3504_ = _args[18];
lean_object* v_fst_3505_ = _args[19];
lean_object* v_discrs_x27_3506_ = _args[20];
lean_object* v_fst_3507_ = _args[21];
lean_object* v_numParams_3508_ = _args[22];
lean_object* v_numDiscrs_3509_ = _args[23];
lean_object* v_altInfos_3510_ = _args[24];
lean_object* v_uElimPos_x3f_3511_ = _args[25];
lean_object* v_snd_3512_ = _args[26];
lean_object* v_overlaps_3513_ = _args[27];
lean_object* v_matcherLevels_3514_ = _args[28];
lean_object* v_onRemaining_3515_ = _args[29];
lean_object* v_remaining_3516_ = _args[30];
lean_object* v_remaining_x27_3517_ = _args[31];
lean_object* v___x_3518_ = _args[32];
lean_object* v___x_3519_ = _args[33];
lean_object* v_liftWith_3520_ = _args[34];
lean_object* v_restoreM_3521_ = _args[35];
lean_object* v_matcherName_3522_ = _args[36];
lean_object* v_aux1_3523_ = _args[37];
lean_object* v_____r_3524_ = _args[38];
_start:
{
uint8_t v___x_14355__boxed_3525_; uint8_t v_useSplitter_boxed_3526_; uint8_t v___x_14363__boxed_3527_; lean_object* v_res_3528_; 
v___x_14355__boxed_3525_ = lean_unbox(v___x_3495_);
v_useSplitter_boxed_3526_ = lean_unbox(v_useSplitter_3496_);
v___x_14363__boxed_3527_ = lean_unbox(v___x_3519_);
v_res_3528_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3486_, v_toPure_3487_, v_toBind_3488_, v___f_3489_, v___x_3490_, v___x_3491_, v_inst_3492_, v___x_3493_, v_toMonadExceptOf_3494_, v___x_14355__boxed_3525_, v_useSplitter_boxed_3526_, v_onAlt_3497_, v___f_3498_, v_fst_3499_, v_inst_3500_, v_inst_3501_, v_numDiscrEqs_3502_, v___x_3503_, v_params_x27_3504_, v_fst_3505_, v_discrs_x27_3506_, v_fst_3507_, v_numParams_3508_, v_numDiscrs_3509_, v_altInfos_3510_, v_uElimPos_x3f_3511_, v_snd_3512_, v_overlaps_3513_, v_matcherLevels_3514_, v_onRemaining_3515_, v_remaining_3516_, v_remaining_x27_3517_, v___x_3518_, v___x_14363__boxed_3527_, v_liftWith_3520_, v_restoreM_3521_, v_matcherName_3522_, v_aux1_3523_, v_____r_3524_);
return v_res_3528_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3531_ = l_Lean_stringToMessageData(v___x_3530_);
return v___x_3531_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3(void){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2));
v___x_3534_ = l_Lean_stringToMessageData(v___x_3533_);
return v___x_3534_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4));
v___x_3537_ = l_Lean_stringToMessageData(v___x_3536_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v_numParams_3538_, lean_object* v_numDiscrs_3539_, lean_object* v_altInfos_3540_, lean_object* v_uElimPos_x3f_3541_, lean_object* v_snd_3542_, lean_object* v_overlaps_3543_, lean_object* v_matcherName_3544_, lean_object* v_matcherLevels_3545_, lean_object* v_params_x27_3546_, lean_object* v_fst_3547_, lean_object* v_discrs_x27_3548_, lean_object* v_toPure_3549_, lean_object* v_onRemaining_3550_, lean_object* v_remaining_3551_, lean_object* v_toBind_3552_, lean_object* v_inst_3553_, lean_object* v_alts_3554_, lean_object* v___f_3555_, uint8_t v___x_3556_, lean_object* v_inst_3557_, lean_object* v_remaining_x27_3558_, lean_object* v_onAlt_3559_, lean_object* v_inst_3560_, lean_object* v___f_3561_, lean_object* v_matcherApp_3562_, lean_object* v___x_3563_, uint8_t v_useSplitter_3564_, uint8_t v_isCasesOn_3565_, lean_object* v___f_3566_, lean_object* v___x_3567_, lean_object* v___x_3568_, lean_object* v_toMonadExceptOf_3569_, lean_object* v___f_3570_, lean_object* v_numDiscrEqs_3571_, lean_object* v_____s_3572_){
_start:
{
lean_object* v_snd_3573_; lean_object* v_fst_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3640_; 
v_snd_3573_ = lean_ctor_get(v_____s_3572_, 1);
v_fst_3574_ = lean_ctor_get(v_____s_3572_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_____s_3572_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3576_ = v_____s_3572_;
v_isShared_3577_ = v_isSharedCheck_3640_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snd_3573_);
lean_inc(v_fst_3574_);
lean_dec(v_____s_3572_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3640_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v_fst_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3638_; 
v_fst_3578_ = lean_ctor_get(v_snd_3573_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_snd_3573_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v_snd_3573_, 1);
lean_dec(v_unused_3639_);
v___x_3580_ = v_snd_3573_;
v_isShared_3581_ = v_isSharedCheck_3638_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_fst_3578_);
lean_dec(v_snd_3573_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3638_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___f_3582_; 
lean_inc(v_toBind_3552_);
lean_inc_ref(v_remaining_3551_);
lean_inc(v_onRemaining_3550_);
lean_inc(v_toPure_3549_);
lean_inc_ref(v_discrs_x27_3548_);
lean_inc_ref(v_fst_3547_);
lean_inc_ref(v_params_x27_3546_);
lean_inc_ref(v_matcherLevels_3545_);
lean_inc(v_matcherName_3544_);
lean_inc_ref(v_overlaps_3543_);
lean_inc_ref(v_snd_3542_);
lean_inc(v_uElimPos_x3f_3541_);
lean_inc_ref(v_altInfos_3540_);
lean_inc(v_numDiscrs_3539_);
lean_inc(v_numParams_3538_);
lean_inc(v_fst_3574_);
v___f_3582_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3582_, 0, v_fst_3574_);
lean_closure_set(v___f_3582_, 1, v_numParams_3538_);
lean_closure_set(v___f_3582_, 2, v_numDiscrs_3539_);
lean_closure_set(v___f_3582_, 3, v_altInfos_3540_);
lean_closure_set(v___f_3582_, 4, v_uElimPos_x3f_3541_);
lean_closure_set(v___f_3582_, 5, v_snd_3542_);
lean_closure_set(v___f_3582_, 6, v_overlaps_3543_);
lean_closure_set(v___f_3582_, 7, v_matcherName_3544_);
lean_closure_set(v___f_3582_, 8, v_matcherLevels_3545_);
lean_closure_set(v___f_3582_, 9, v_params_x27_3546_);
lean_closure_set(v___f_3582_, 10, v_fst_3547_);
lean_closure_set(v___f_3582_, 11, v_discrs_x27_3548_);
lean_closure_set(v___f_3582_, 12, v_toPure_3549_);
lean_closure_set(v___f_3582_, 13, v_onRemaining_3550_);
lean_closure_set(v___f_3582_, 14, v_remaining_3551_);
lean_closure_set(v___f_3582_, 15, v_toBind_3552_);
if (v_useSplitter_3564_ == 0)
{
lean_del_object(v___x_3576_);
lean_dec(v_fst_3574_);
lean_dec(v_numDiscrEqs_3571_);
lean_dec(v___f_3570_);
lean_dec_ref(v_toMonadExceptOf_3569_);
lean_dec(v___x_3568_);
lean_dec(v___x_3567_);
lean_dec(v___f_3566_);
lean_dec_ref(v_remaining_3551_);
lean_dec(v_onRemaining_3550_);
lean_dec_ref(v_overlaps_3543_);
lean_dec_ref(v_snd_3542_);
lean_dec(v_uElimPos_x3f_3541_);
lean_dec_ref(v_altInfos_3540_);
lean_dec(v_numDiscrs_3539_);
lean_dec(v_numParams_3538_);
goto v___jp_3583_;
}
else
{
if (v_isCasesOn_3565_ == 0)
{
lean_object* v_liftWith_3610_; lean_object* v_restoreM_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v_aux1_3614_; lean_object* v_aux1_3615_; lean_object* v_aux1_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_dec_ref(v___f_3582_);
lean_del_object(v___x_3580_);
lean_dec_ref(v_matcherApp_3562_);
lean_dec(v___f_3561_);
lean_dec(v___f_3555_);
v_liftWith_3610_ = lean_ctor_get(v_inst_3553_, 0);
lean_inc(v_liftWith_3610_);
v_restoreM_3611_ = lean_ctor_get(v_inst_3553_, 1);
lean_inc(v_restoreM_3611_);
lean_inc_ref(v_matcherLevels_3545_);
v___x_3612_ = lean_array_to_list(v_matcherLevels_3545_);
lean_inc(v___x_3612_);
lean_inc(v_matcherName_3544_);
v___x_3613_ = l_Lean_mkConst(v_matcherName_3544_, v___x_3612_);
v_aux1_3614_ = l_Lean_mkAppN(v___x_3613_, v_params_x27_3546_);
lean_inc_ref(v_fst_3547_);
v_aux1_3615_ = l_Lean_Expr_app___override(v_aux1_3614_, v_fst_3547_);
v_aux1_3616_ = l_Lean_mkAppN(v_aux1_3615_, v_discrs_x27_3548_);
lean_inc_ref(v_aux1_3616_);
v___x_3617_ = l_Lean_indentExpr(v_aux1_3616_);
v___x_3618_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
if (v_isShared_3577_ == 0)
{
lean_ctor_set_tag(v___x_3576_, 7);
lean_ctor_set(v___x_3576_, 1, v___x_3617_);
lean_ctor_set(v___x_3576_, 0, v___x_3618_);
v___x_3620_ = v___x_3576_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v___x_3617_);
v___x_3620_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___f_3623_; uint8_t v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___f_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___f_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3621_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___f_3623_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3623_, 0, v___x_3622_);
v___x_3624_ = 0;
v___x_3625_ = lean_box(v___x_3556_);
v___x_3626_ = lean_box(v_useSplitter_3564_);
v___x_3627_ = lean_box(v___x_3624_);
lean_inc_ref(v_aux1_3616_);
lean_inc(v_restoreM_3611_);
lean_inc(v_liftWith_3610_);
lean_inc(v_inst_3557_);
lean_inc_n(v_toBind_3552_, 2);
v___f_3628_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 39, 38);
lean_closure_set(v___f_3628_, 0, v_alts_3554_);
lean_closure_set(v___f_3628_, 1, v_toPure_3549_);
lean_closure_set(v___f_3628_, 2, v_toBind_3552_);
lean_closure_set(v___f_3628_, 3, v___f_3566_);
lean_closure_set(v___f_3628_, 4, v___x_3563_);
lean_closure_set(v___f_3628_, 5, v___x_3567_);
lean_closure_set(v___f_3628_, 6, v_inst_3557_);
lean_closure_set(v___f_3628_, 7, v___x_3568_);
lean_closure_set(v___f_3628_, 8, v_toMonadExceptOf_3569_);
lean_closure_set(v___f_3628_, 9, v___x_3625_);
lean_closure_set(v___f_3628_, 10, v___x_3626_);
lean_closure_set(v___f_3628_, 11, v_onAlt_3559_);
lean_closure_set(v___f_3628_, 12, v___f_3570_);
lean_closure_set(v___f_3628_, 13, v_fst_3578_);
lean_closure_set(v___f_3628_, 14, v_inst_3553_);
lean_closure_set(v___f_3628_, 15, v_inst_3560_);
lean_closure_set(v___f_3628_, 16, v_numDiscrEqs_3571_);
lean_closure_set(v___f_3628_, 17, v___x_3612_);
lean_closure_set(v___f_3628_, 18, v_params_x27_3546_);
lean_closure_set(v___f_3628_, 19, v_fst_3547_);
lean_closure_set(v___f_3628_, 20, v_discrs_x27_3548_);
lean_closure_set(v___f_3628_, 21, v_fst_3574_);
lean_closure_set(v___f_3628_, 22, v_numParams_3538_);
lean_closure_set(v___f_3628_, 23, v_numDiscrs_3539_);
lean_closure_set(v___f_3628_, 24, v_altInfos_3540_);
lean_closure_set(v___f_3628_, 25, v_uElimPos_x3f_3541_);
lean_closure_set(v___f_3628_, 26, v_snd_3542_);
lean_closure_set(v___f_3628_, 27, v_overlaps_3543_);
lean_closure_set(v___f_3628_, 28, v_matcherLevels_3545_);
lean_closure_set(v___f_3628_, 29, v_onRemaining_3550_);
lean_closure_set(v___f_3628_, 30, v_remaining_3551_);
lean_closure_set(v___f_3628_, 31, v_remaining_x27_3558_);
lean_closure_set(v___f_3628_, 32, v___x_3621_);
lean_closure_set(v___f_3628_, 33, v___x_3627_);
lean_closure_set(v___f_3628_, 34, v_liftWith_3610_);
lean_closure_set(v___f_3628_, 35, v_restoreM_3611_);
lean_closure_set(v___f_3628_, 36, v_matcherName_3544_);
lean_closure_set(v___f_3628_, 37, v_aux1_3616_);
v___x_3629_ = lean_box(v___x_3624_);
v___x_3630_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3630_, 0, v_aux1_3616_);
lean_closure_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_apply_2(v_inst_3557_, lean_box(0), v___x_3630_);
v___f_3632_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3632_, 0, v___x_3631_);
lean_closure_set(v___f_3632_, 1, v___f_3623_);
v___x_3633_ = lean_apply_2(v_liftWith_3610_, lean_box(0), v___f_3632_);
v___x_3634_ = lean_apply_1(v_restoreM_3611_, lean_box(0));
v___x_3635_ = lean_apply_4(v_toBind_3552_, lean_box(0), lean_box(0), v___x_3633_, v___x_3634_);
v___x_3636_ = lean_apply_4(v_toBind_3552_, lean_box(0), lean_box(0), v___x_3635_, v___f_3628_);
return v___x_3636_;
}
}
else
{
lean_del_object(v___x_3576_);
lean_dec(v_fst_3574_);
lean_dec(v_numDiscrEqs_3571_);
lean_dec(v___f_3570_);
lean_dec_ref(v_toMonadExceptOf_3569_);
lean_dec(v___x_3568_);
lean_dec(v___x_3567_);
lean_dec(v___f_3566_);
lean_dec_ref(v_remaining_3551_);
lean_dec(v_onRemaining_3550_);
lean_dec_ref(v_overlaps_3543_);
lean_dec_ref(v_snd_3542_);
lean_dec(v_uElimPos_x3f_3541_);
lean_dec_ref(v_altInfos_3540_);
lean_dec(v_numDiscrs_3539_);
lean_dec(v_numParams_3538_);
goto v___jp_3583_;
}
}
v___jp_3583_:
{
lean_object* v_liftWith_3584_; lean_object* v_restoreM_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v_aux_3588_; lean_object* v_aux_3589_; lean_object* v_aux_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___f_3595_; lean_object* v___x_3596_; lean_object* v___x_3598_; 
v_liftWith_3584_ = lean_ctor_get(v_inst_3553_, 0);
lean_inc(v_liftWith_3584_);
v_restoreM_3585_ = lean_ctor_get(v_inst_3553_, 1);
lean_inc(v_restoreM_3585_);
v___x_3586_ = lean_array_to_list(v_matcherLevels_3545_);
v___x_3587_ = l_Lean_mkConst(v_matcherName_3544_, v___x_3586_);
v_aux_3588_ = l_Lean_mkAppN(v___x_3587_, v_params_x27_3546_);
lean_dec_ref(v_params_x27_3546_);
v_aux_3589_ = l_Lean_Expr_app___override(v_aux_3588_, v_fst_3547_);
v_aux_3590_ = l_Lean_mkAppN(v_aux_3589_, v_discrs_x27_3548_);
lean_dec_ref(v_discrs_x27_3548_);
lean_inc_ref_n(v_aux_3590_, 2);
v___x_3591_ = l_Lean_indentExpr(v_aux_3590_);
v___x_3592_ = 1;
v___x_3593_ = lean_box(v___x_3556_);
v___x_3594_ = lean_box(v___x_3592_);
lean_inc(v_inst_3557_);
lean_inc(v_toBind_3552_);
v___f_3595_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3595_, 0, v_alts_3554_);
lean_closure_set(v___f_3595_, 1, v_toPure_3549_);
lean_closure_set(v___f_3595_, 2, v_toBind_3552_);
lean_closure_set(v___f_3595_, 3, v___f_3555_);
lean_closure_set(v___f_3595_, 4, v___x_3593_);
lean_closure_set(v___f_3595_, 5, v___x_3594_);
lean_closure_set(v___f_3595_, 6, v_inst_3557_);
lean_closure_set(v___f_3595_, 7, v_remaining_x27_3558_);
lean_closure_set(v___f_3595_, 8, v_onAlt_3559_);
lean_closure_set(v___f_3595_, 9, v_inst_3553_);
lean_closure_set(v___f_3595_, 10, v_inst_3560_);
lean_closure_set(v___f_3595_, 11, v___f_3561_);
lean_closure_set(v___f_3595_, 12, v_fst_3578_);
lean_closure_set(v___f_3595_, 13, v_matcherApp_3562_);
lean_closure_set(v___f_3595_, 14, v___x_3563_);
lean_closure_set(v___f_3595_, 15, v___f_3582_);
lean_closure_set(v___f_3595_, 16, v_aux_3590_);
v___x_3596_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
if (v_isShared_3581_ == 0)
{
lean_ctor_set_tag(v___x_3580_, 7);
lean_ctor_set(v___x_3580_, 1, v___x_3591_);
lean_ctor_set(v___x_3580_, 0, v___x_3596_);
v___x_3598_ = v___x_3580_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v___x_3591_);
v___x_3598_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___f_3599_; uint8_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___f_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___f_3599_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3599_, 0, v___x_3598_);
v___x_3600_ = 0;
v___x_3601_ = lean_box(v___x_3600_);
v___x_3602_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3602_, 0, v_aux_3590_);
lean_closure_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = lean_apply_2(v_inst_3557_, lean_box(0), v___x_3602_);
v___f_3604_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3604_, 0, v___x_3603_);
lean_closure_set(v___f_3604_, 1, v___f_3599_);
v___x_3605_ = lean_apply_2(v_liftWith_3584_, lean_box(0), v___f_3604_);
v___x_3606_ = lean_apply_1(v_restoreM_3585_, lean_box(0));
lean_inc(v_toBind_3552_);
v___x_3607_ = lean_apply_4(v_toBind_3552_, lean_box(0), lean_box(0), v___x_3605_, v___x_3606_);
v___x_3608_ = lean_apply_4(v_toBind_3552_, lean_box(0), lean_box(0), v___x_3607_, v___f_3595_);
return v___x_3608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v_numParams_3641_ = _args[0];
lean_object* v_numDiscrs_3642_ = _args[1];
lean_object* v_altInfos_3643_ = _args[2];
lean_object* v_uElimPos_x3f_3644_ = _args[3];
lean_object* v_snd_3645_ = _args[4];
lean_object* v_overlaps_3646_ = _args[5];
lean_object* v_matcherName_3647_ = _args[6];
lean_object* v_matcherLevels_3648_ = _args[7];
lean_object* v_params_x27_3649_ = _args[8];
lean_object* v_fst_3650_ = _args[9];
lean_object* v_discrs_x27_3651_ = _args[10];
lean_object* v_toPure_3652_ = _args[11];
lean_object* v_onRemaining_3653_ = _args[12];
lean_object* v_remaining_3654_ = _args[13];
lean_object* v_toBind_3655_ = _args[14];
lean_object* v_inst_3656_ = _args[15];
lean_object* v_alts_3657_ = _args[16];
lean_object* v___f_3658_ = _args[17];
lean_object* v___x_3659_ = _args[18];
lean_object* v_inst_3660_ = _args[19];
lean_object* v_remaining_x27_3661_ = _args[20];
lean_object* v_onAlt_3662_ = _args[21];
lean_object* v_inst_3663_ = _args[22];
lean_object* v___f_3664_ = _args[23];
lean_object* v_matcherApp_3665_ = _args[24];
lean_object* v___x_3666_ = _args[25];
lean_object* v_useSplitter_3667_ = _args[26];
lean_object* v_isCasesOn_3668_ = _args[27];
lean_object* v___f_3669_ = _args[28];
lean_object* v___x_3670_ = _args[29];
lean_object* v___x_3671_ = _args[30];
lean_object* v_toMonadExceptOf_3672_ = _args[31];
lean_object* v___f_3673_ = _args[32];
lean_object* v_numDiscrEqs_3674_ = _args[33];
lean_object* v_____s_3675_ = _args[34];
_start:
{
uint8_t v___x_14435__boxed_3676_; uint8_t v_useSplitter_boxed_3677_; uint8_t v_isCasesOn_boxed_3678_; lean_object* v_res_3679_; 
v___x_14435__boxed_3676_ = lean_unbox(v___x_3659_);
v_useSplitter_boxed_3677_ = lean_unbox(v_useSplitter_3667_);
v_isCasesOn_boxed_3678_ = lean_unbox(v_isCasesOn_3668_);
v_res_3679_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3641_, v_numDiscrs_3642_, v_altInfos_3643_, v_uElimPos_x3f_3644_, v_snd_3645_, v_overlaps_3646_, v_matcherName_3647_, v_matcherLevels_3648_, v_params_x27_3649_, v_fst_3650_, v_discrs_x27_3651_, v_toPure_3652_, v_onRemaining_3653_, v_remaining_3654_, v_toBind_3655_, v_inst_3656_, v_alts_3657_, v___f_3658_, v___x_14435__boxed_3676_, v_inst_3660_, v_remaining_x27_3661_, v_onAlt_3662_, v_inst_3663_, v___f_3664_, v_matcherApp_3665_, v___x_3666_, v_useSplitter_boxed_3677_, v_isCasesOn_boxed_3678_, v___f_3669_, v___x_3670_, v___x_3671_, v_toMonadExceptOf_3672_, v___f_3673_, v_numDiscrEqs_3674_, v_____s_3675_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3680_, lean_object* v_numDiscrs_3681_, lean_object* v_altInfos_3682_, lean_object* v_uElimPos_x3f_3683_, lean_object* v_snd_3684_, lean_object* v_overlaps_3685_, lean_object* v_matcherName_3686_, lean_object* v_params_x27_3687_, lean_object* v_fst_3688_, lean_object* v_discrs_x27_3689_, lean_object* v_toPure_3690_, lean_object* v_onRemaining_3691_, lean_object* v_remaining_3692_, lean_object* v_toBind_3693_, lean_object* v_inst_3694_, lean_object* v_alts_3695_, lean_object* v___f_3696_, uint8_t v___x_3697_, lean_object* v_inst_3698_, lean_object* v_onAlt_3699_, lean_object* v_inst_3700_, lean_object* v___f_3701_, lean_object* v_matcherApp_3702_, uint8_t v_useSplitter_3703_, uint8_t v_isCasesOn_3704_, lean_object* v___f_3705_, lean_object* v___x_3706_, lean_object* v___x_3707_, lean_object* v_toMonadExceptOf_3708_, lean_object* v___f_3709_, lean_object* v_numDiscrEqs_3710_, lean_object* v_fst_3711_, lean_object* v___f_3712_, lean_object* v_matcherLevels_3713_){
_start:
{
lean_object* v___x_3714_; lean_object* v_remaining_x27_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___f_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; size_t v_sz_3726_; size_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3714_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3715_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3716_ = lean_box(v___x_3697_);
v___x_3717_ = lean_box(v_useSplitter_3703_);
v___x_3718_ = lean_box(v_isCasesOn_3704_);
lean_inc_ref(v_inst_3700_);
lean_inc(v_toBind_3693_);
lean_inc_ref(v_discrs_x27_3689_);
v___f_3719_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 35, 34);
lean_closure_set(v___f_3719_, 0, v_numParams_3680_);
lean_closure_set(v___f_3719_, 1, v_numDiscrs_3681_);
lean_closure_set(v___f_3719_, 2, v_altInfos_3682_);
lean_closure_set(v___f_3719_, 3, v_uElimPos_x3f_3683_);
lean_closure_set(v___f_3719_, 4, v_snd_3684_);
lean_closure_set(v___f_3719_, 5, v_overlaps_3685_);
lean_closure_set(v___f_3719_, 6, v_matcherName_3686_);
lean_closure_set(v___f_3719_, 7, v_matcherLevels_3713_);
lean_closure_set(v___f_3719_, 8, v_params_x27_3687_);
lean_closure_set(v___f_3719_, 9, v_fst_3688_);
lean_closure_set(v___f_3719_, 10, v_discrs_x27_3689_);
lean_closure_set(v___f_3719_, 11, v_toPure_3690_);
lean_closure_set(v___f_3719_, 12, v_onRemaining_3691_);
lean_closure_set(v___f_3719_, 13, v_remaining_3692_);
lean_closure_set(v___f_3719_, 14, v_toBind_3693_);
lean_closure_set(v___f_3719_, 15, v_inst_3694_);
lean_closure_set(v___f_3719_, 16, v_alts_3695_);
lean_closure_set(v___f_3719_, 17, v___f_3696_);
lean_closure_set(v___f_3719_, 18, v___x_3716_);
lean_closure_set(v___f_3719_, 19, v_inst_3698_);
lean_closure_set(v___f_3719_, 20, v_remaining_x27_3715_);
lean_closure_set(v___f_3719_, 21, v_onAlt_3699_);
lean_closure_set(v___f_3719_, 22, v_inst_3700_);
lean_closure_set(v___f_3719_, 23, v___f_3701_);
lean_closure_set(v___f_3719_, 24, v_matcherApp_3702_);
lean_closure_set(v___f_3719_, 25, v___x_3714_);
lean_closure_set(v___f_3719_, 26, v___x_3717_);
lean_closure_set(v___f_3719_, 27, v___x_3718_);
lean_closure_set(v___f_3719_, 28, v___f_3705_);
lean_closure_set(v___f_3719_, 29, v___x_3706_);
lean_closure_set(v___f_3719_, 30, v___x_3707_);
lean_closure_set(v___f_3719_, 31, v_toMonadExceptOf_3708_);
lean_closure_set(v___f_3719_, 32, v___f_3709_);
lean_closure_set(v___f_3719_, 33, v_numDiscrEqs_3710_);
v___x_3720_ = l_Array_reverse___redArg(v_fst_3711_);
v___x_3721_ = lean_array_get_size(v___x_3720_);
v___x_3722_ = l_Array_toSubarray___redArg(v___x_3720_, v___x_3714_, v___x_3721_);
v___x_3723_ = l_Array_reverse___redArg(v_discrs_x27_3689_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3714_);
lean_ctor_set(v___x_3724_, 1, v___x_3722_);
v___x_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3725_, 0, v_remaining_x27_3715_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v_sz_3726_ = lean_array_size(v___x_3723_);
v___x_3727_ = ((size_t)0ULL);
v___x_3728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3700_, v___x_3723_, v___f_3712_, v_sz_3726_, v___x_3727_, v___x_3725_);
v___x_3729_ = lean_apply_4(v_toBind_3693_, lean_box(0), lean_box(0), v___x_3728_, v___f_3719_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3730_ = _args[0];
lean_object* v_numDiscrs_3731_ = _args[1];
lean_object* v_altInfos_3732_ = _args[2];
lean_object* v_uElimPos_x3f_3733_ = _args[3];
lean_object* v_snd_3734_ = _args[4];
lean_object* v_overlaps_3735_ = _args[5];
lean_object* v_matcherName_3736_ = _args[6];
lean_object* v_params_x27_3737_ = _args[7];
lean_object* v_fst_3738_ = _args[8];
lean_object* v_discrs_x27_3739_ = _args[9];
lean_object* v_toPure_3740_ = _args[10];
lean_object* v_onRemaining_3741_ = _args[11];
lean_object* v_remaining_3742_ = _args[12];
lean_object* v_toBind_3743_ = _args[13];
lean_object* v_inst_3744_ = _args[14];
lean_object* v_alts_3745_ = _args[15];
lean_object* v___f_3746_ = _args[16];
lean_object* v___x_3747_ = _args[17];
lean_object* v_inst_3748_ = _args[18];
lean_object* v_onAlt_3749_ = _args[19];
lean_object* v_inst_3750_ = _args[20];
lean_object* v___f_3751_ = _args[21];
lean_object* v_matcherApp_3752_ = _args[22];
lean_object* v_useSplitter_3753_ = _args[23];
lean_object* v_isCasesOn_3754_ = _args[24];
lean_object* v___f_3755_ = _args[25];
lean_object* v___x_3756_ = _args[26];
lean_object* v___x_3757_ = _args[27];
lean_object* v_toMonadExceptOf_3758_ = _args[28];
lean_object* v___f_3759_ = _args[29];
lean_object* v_numDiscrEqs_3760_ = _args[30];
lean_object* v_fst_3761_ = _args[31];
lean_object* v___f_3762_ = _args[32];
lean_object* v_matcherLevels_3763_ = _args[33];
_start:
{
uint8_t v___x_14597__boxed_3764_; uint8_t v_useSplitter_boxed_3765_; uint8_t v_isCasesOn_boxed_3766_; lean_object* v_res_3767_; 
v___x_14597__boxed_3764_ = lean_unbox(v___x_3747_);
v_useSplitter_boxed_3765_ = lean_unbox(v_useSplitter_3753_);
v_isCasesOn_boxed_3766_ = lean_unbox(v_isCasesOn_3754_);
v_res_3767_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3730_, v_numDiscrs_3731_, v_altInfos_3732_, v_uElimPos_x3f_3733_, v_snd_3734_, v_overlaps_3735_, v_matcherName_3736_, v_params_x27_3737_, v_fst_3738_, v_discrs_x27_3739_, v_toPure_3740_, v_onRemaining_3741_, v_remaining_3742_, v_toBind_3743_, v_inst_3744_, v_alts_3745_, v___f_3746_, v___x_14597__boxed_3764_, v_inst_3748_, v_onAlt_3749_, v_inst_3750_, v___f_3751_, v_matcherApp_3752_, v_useSplitter_boxed_3765_, v_isCasesOn_boxed_3766_, v___f_3755_, v___x_3756_, v___x_3757_, v_toMonadExceptOf_3758_, v___f_3759_, v_numDiscrEqs_3760_, v_fst_3761_, v___f_3762_, v_matcherLevels_3763_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v___f_3768_, lean_object* v_matcherLevels_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_apply_1(v___f_3768_, v_matcherLevels_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3771_, lean_object* v_matcherName_3772_, lean_object* v_params_x27_3773_, lean_object* v_discrs_x27_3774_, lean_object* v_toPure_3775_, lean_object* v_onRemaining_3776_, lean_object* v_remaining_3777_, lean_object* v_toBind_3778_, lean_object* v_inst_3779_, lean_object* v_alts_3780_, lean_object* v___f_3781_, uint8_t v___x_3782_, lean_object* v_inst_3783_, lean_object* v_onAlt_3784_, lean_object* v_inst_3785_, lean_object* v___f_3786_, lean_object* v_matcherApp_3787_, uint8_t v_useSplitter_3788_, uint8_t v_isCasesOn_3789_, lean_object* v___f_3790_, lean_object* v___x_3791_, lean_object* v___x_3792_, lean_object* v_toMonadExceptOf_3793_, lean_object* v___f_3794_, lean_object* v_numDiscrEqs_3795_, lean_object* v___f_3796_, lean_object* v_matcherLevels_3797_, lean_object* v_____x_3798_){
_start:
{
lean_object* v_snd_3799_; lean_object* v_snd_3800_; lean_object* v_fst_3801_; lean_object* v_fst_3802_; lean_object* v_fst_3803_; lean_object* v_snd_3804_; lean_object* v_numParams_3805_; lean_object* v_numDiscrs_3806_; lean_object* v_altInfos_3807_; lean_object* v_uElimPos_x3f_3808_; lean_object* v_overlaps_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___f_3813_; 
v_snd_3799_ = lean_ctor_get(v_____x_3798_, 1);
lean_inc(v_snd_3799_);
v_snd_3800_ = lean_ctor_get(v_snd_3799_, 1);
lean_inc(v_snd_3800_);
v_fst_3801_ = lean_ctor_get(v_____x_3798_, 0);
lean_inc(v_fst_3801_);
lean_dec_ref(v_____x_3798_);
v_fst_3802_ = lean_ctor_get(v_snd_3799_, 0);
lean_inc(v_fst_3802_);
lean_dec(v_snd_3799_);
v_fst_3803_ = lean_ctor_get(v_snd_3800_, 0);
lean_inc(v_fst_3803_);
v_snd_3804_ = lean_ctor_get(v_snd_3800_, 1);
lean_inc(v_snd_3804_);
lean_dec(v_snd_3800_);
v_numParams_3805_ = lean_ctor_get(v_toMatcherInfo_3771_, 0);
lean_inc(v_numParams_3805_);
v_numDiscrs_3806_ = lean_ctor_get(v_toMatcherInfo_3771_, 1);
lean_inc(v_numDiscrs_3806_);
v_altInfos_3807_ = lean_ctor_get(v_toMatcherInfo_3771_, 2);
lean_inc_ref(v_altInfos_3807_);
v_uElimPos_x3f_3808_ = lean_ctor_get(v_toMatcherInfo_3771_, 3);
lean_inc_n(v_uElimPos_x3f_3808_, 2);
v_overlaps_3809_ = lean_ctor_get(v_toMatcherInfo_3771_, 5);
lean_inc_ref(v_overlaps_3809_);
lean_dec_ref(v_toMatcherInfo_3771_);
v___x_3810_ = lean_box(v___x_3782_);
v___x_3811_ = lean_box(v_useSplitter_3788_);
v___x_3812_ = lean_box(v_isCasesOn_3789_);
lean_inc(v_toBind_3778_);
lean_inc(v_toPure_3775_);
v___f_3813_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 34, 33);
lean_closure_set(v___f_3813_, 0, v_numParams_3805_);
lean_closure_set(v___f_3813_, 1, v_numDiscrs_3806_);
lean_closure_set(v___f_3813_, 2, v_altInfos_3807_);
lean_closure_set(v___f_3813_, 3, v_uElimPos_x3f_3808_);
lean_closure_set(v___f_3813_, 4, v_snd_3804_);
lean_closure_set(v___f_3813_, 5, v_overlaps_3809_);
lean_closure_set(v___f_3813_, 6, v_matcherName_3772_);
lean_closure_set(v___f_3813_, 7, v_params_x27_3773_);
lean_closure_set(v___f_3813_, 8, v_fst_3801_);
lean_closure_set(v___f_3813_, 9, v_discrs_x27_3774_);
lean_closure_set(v___f_3813_, 10, v_toPure_3775_);
lean_closure_set(v___f_3813_, 11, v_onRemaining_3776_);
lean_closure_set(v___f_3813_, 12, v_remaining_3777_);
lean_closure_set(v___f_3813_, 13, v_toBind_3778_);
lean_closure_set(v___f_3813_, 14, v_inst_3779_);
lean_closure_set(v___f_3813_, 15, v_alts_3780_);
lean_closure_set(v___f_3813_, 16, v___f_3781_);
lean_closure_set(v___f_3813_, 17, v___x_3810_);
lean_closure_set(v___f_3813_, 18, v_inst_3783_);
lean_closure_set(v___f_3813_, 19, v_onAlt_3784_);
lean_closure_set(v___f_3813_, 20, v_inst_3785_);
lean_closure_set(v___f_3813_, 21, v___f_3786_);
lean_closure_set(v___f_3813_, 22, v_matcherApp_3787_);
lean_closure_set(v___f_3813_, 23, v___x_3811_);
lean_closure_set(v___f_3813_, 24, v___x_3812_);
lean_closure_set(v___f_3813_, 25, v___f_3790_);
lean_closure_set(v___f_3813_, 26, v___x_3791_);
lean_closure_set(v___f_3813_, 27, v___x_3792_);
lean_closure_set(v___f_3813_, 28, v_toMonadExceptOf_3793_);
lean_closure_set(v___f_3813_, 29, v___f_3794_);
lean_closure_set(v___f_3813_, 30, v_numDiscrEqs_3795_);
lean_closure_set(v___f_3813_, 31, v_fst_3803_);
lean_closure_set(v___f_3813_, 32, v___f_3796_);
if (lean_obj_tag(v_uElimPos_x3f_3808_) == 0)
{
lean_object* v___f_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec(v_fst_3802_);
v___f_3814_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3814_, 0, v___f_3813_);
v___x_3815_ = lean_apply_2(v_toPure_3775_, lean_box(0), v_matcherLevels_3797_);
v___x_3816_ = lean_apply_4(v_toBind_3778_, lean_box(0), lean_box(0), v___x_3815_, v___f_3814_);
return v___x_3816_;
}
else
{
lean_object* v_val_3817_; lean_object* v___f_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v_val_3817_ = lean_ctor_get(v_uElimPos_x3f_3808_, 0);
lean_inc(v_val_3817_);
lean_dec_ref_known(v_uElimPos_x3f_3808_, 1);
v___f_3818_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3818_, 0, v___f_3813_);
v___x_3819_ = lean_array_set(v_matcherLevels_3797_, v_val_3817_, v_fst_3802_);
lean_dec(v_val_3817_);
v___x_3820_ = lean_apply_2(v_toPure_3775_, lean_box(0), v___x_3819_);
v___x_3821_ = lean_apply_4(v_toBind_3778_, lean_box(0), lean_box(0), v___x_3820_, v___f_3818_);
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3822_ = _args[0];
lean_object* v_matcherName_3823_ = _args[1];
lean_object* v_params_x27_3824_ = _args[2];
lean_object* v_discrs_x27_3825_ = _args[3];
lean_object* v_toPure_3826_ = _args[4];
lean_object* v_onRemaining_3827_ = _args[5];
lean_object* v_remaining_3828_ = _args[6];
lean_object* v_toBind_3829_ = _args[7];
lean_object* v_inst_3830_ = _args[8];
lean_object* v_alts_3831_ = _args[9];
lean_object* v___f_3832_ = _args[10];
lean_object* v___x_3833_ = _args[11];
lean_object* v_inst_3834_ = _args[12];
lean_object* v_onAlt_3835_ = _args[13];
lean_object* v_inst_3836_ = _args[14];
lean_object* v___f_3837_ = _args[15];
lean_object* v_matcherApp_3838_ = _args[16];
lean_object* v_useSplitter_3839_ = _args[17];
lean_object* v_isCasesOn_3840_ = _args[18];
lean_object* v___f_3841_ = _args[19];
lean_object* v___x_3842_ = _args[20];
lean_object* v___x_3843_ = _args[21];
lean_object* v_toMonadExceptOf_3844_ = _args[22];
lean_object* v___f_3845_ = _args[23];
lean_object* v_numDiscrEqs_3846_ = _args[24];
lean_object* v___f_3847_ = _args[25];
lean_object* v_matcherLevels_3848_ = _args[26];
lean_object* v_____x_3849_ = _args[27];
_start:
{
uint8_t v___x_14669__boxed_3850_; uint8_t v_useSplitter_boxed_3851_; uint8_t v_isCasesOn_boxed_3852_; lean_object* v_res_3853_; 
v___x_14669__boxed_3850_ = lean_unbox(v___x_3833_);
v_useSplitter_boxed_3851_ = lean_unbox(v_useSplitter_3839_);
v_isCasesOn_boxed_3852_ = lean_unbox(v_isCasesOn_3840_);
v_res_3853_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3822_, v_matcherName_3823_, v_params_x27_3824_, v_discrs_x27_3825_, v_toPure_3826_, v_onRemaining_3827_, v_remaining_3828_, v_toBind_3829_, v_inst_3830_, v_alts_3831_, v___f_3832_, v___x_14669__boxed_3850_, v_inst_3834_, v_onAlt_3835_, v_inst_3836_, v___f_3837_, v_matcherApp_3838_, v_useSplitter_boxed_3851_, v_isCasesOn_boxed_3852_, v___f_3841_, v___x_3842_, v___x_3843_, v_toMonadExceptOf_3844_, v___f_3845_, v_numDiscrEqs_3846_, v___f_3847_, v_matcherLevels_3848_, v_____x_3849_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3854_, lean_object* v_inst_3855_, lean_object* v_toBind_3856_, lean_object* v_toMatcherInfo_3857_, lean_object* v_inst_3858_, lean_object* v___f_3859_, lean_object* v_onMotive_3860_, lean_object* v_discrs_3861_, lean_object* v_inst_3862_, lean_object* v_matcherName_3863_, lean_object* v_params_x27_3864_, lean_object* v_onRemaining_3865_, lean_object* v_remaining_3866_, lean_object* v_inst_3867_, lean_object* v_alts_3868_, lean_object* v___f_3869_, lean_object* v_onAlt_3870_, lean_object* v___f_3871_, lean_object* v_matcherApp_3872_, uint8_t v_useSplitter_3873_, uint8_t v_isCasesOn_3874_, lean_object* v___f_3875_, lean_object* v___x_3876_, lean_object* v___x_3877_, lean_object* v_toMonadExceptOf_3878_, lean_object* v___f_3879_, lean_object* v_numDiscrEqs_3880_, lean_object* v___f_3881_, lean_object* v_matcherLevels_3882_, lean_object* v_motive_3883_, lean_object* v_discrs_x27_3884_){
_start:
{
lean_object* v___f_3885_; uint8_t v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___f_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
lean_inc_ref_n(v_inst_3858_, 2);
lean_inc_ref(v_discrs_x27_3884_);
lean_inc_ref(v_toMatcherInfo_3857_);
lean_inc_n(v_toBind_3856_, 2);
lean_inc(v_inst_3855_);
lean_inc(v_toPure_3854_);
v___f_3885_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3885_, 0, v_toPure_3854_);
lean_closure_set(v___f_3885_, 1, v_inst_3855_);
lean_closure_set(v___f_3885_, 2, v_toBind_3856_);
lean_closure_set(v___f_3885_, 3, v_toMatcherInfo_3857_);
lean_closure_set(v___f_3885_, 4, v_discrs_x27_3884_);
lean_closure_set(v___f_3885_, 5, v_inst_3858_);
lean_closure_set(v___f_3885_, 6, v___f_3859_);
lean_closure_set(v___f_3885_, 7, v_onMotive_3860_);
lean_closure_set(v___f_3885_, 8, v_discrs_3861_);
lean_closure_set(v___f_3885_, 9, v_inst_3862_);
v___x_3886_ = 0;
v___x_3887_ = lean_box(v___x_3886_);
v___x_3888_ = lean_box(v_useSplitter_3873_);
v___x_3889_ = lean_box(v_isCasesOn_3874_);
lean_inc_ref(v_inst_3867_);
v___f_3890_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 28, 27);
lean_closure_set(v___f_3890_, 0, v_toMatcherInfo_3857_);
lean_closure_set(v___f_3890_, 1, v_matcherName_3863_);
lean_closure_set(v___f_3890_, 2, v_params_x27_3864_);
lean_closure_set(v___f_3890_, 3, v_discrs_x27_3884_);
lean_closure_set(v___f_3890_, 4, v_toPure_3854_);
lean_closure_set(v___f_3890_, 5, v_onRemaining_3865_);
lean_closure_set(v___f_3890_, 6, v_remaining_3866_);
lean_closure_set(v___f_3890_, 7, v_toBind_3856_);
lean_closure_set(v___f_3890_, 8, v_inst_3867_);
lean_closure_set(v___f_3890_, 9, v_alts_3868_);
lean_closure_set(v___f_3890_, 10, v___f_3869_);
lean_closure_set(v___f_3890_, 11, v___x_3887_);
lean_closure_set(v___f_3890_, 12, v_inst_3855_);
lean_closure_set(v___f_3890_, 13, v_onAlt_3870_);
lean_closure_set(v___f_3890_, 14, v_inst_3858_);
lean_closure_set(v___f_3890_, 15, v___f_3871_);
lean_closure_set(v___f_3890_, 16, v_matcherApp_3872_);
lean_closure_set(v___f_3890_, 17, v___x_3888_);
lean_closure_set(v___f_3890_, 18, v___x_3889_);
lean_closure_set(v___f_3890_, 19, v___f_3875_);
lean_closure_set(v___f_3890_, 20, v___x_3876_);
lean_closure_set(v___f_3890_, 21, v___x_3877_);
lean_closure_set(v___f_3890_, 22, v_toMonadExceptOf_3878_);
lean_closure_set(v___f_3890_, 23, v___f_3879_);
lean_closure_set(v___f_3890_, 24, v_numDiscrEqs_3880_);
lean_closure_set(v___f_3890_, 25, v___f_3881_);
lean_closure_set(v___f_3890_, 26, v_matcherLevels_3882_);
v___x_3891_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3867_, v_inst_3858_, v_motive_3883_, v___f_3885_, v___x_3886_);
v___x_3892_ = lean_apply_4(v_toBind_3856_, lean_box(0), lean_box(0), v___x_3891_, v___f_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3893_ = _args[0];
lean_object* v_inst_3894_ = _args[1];
lean_object* v_toBind_3895_ = _args[2];
lean_object* v_toMatcherInfo_3896_ = _args[3];
lean_object* v_inst_3897_ = _args[4];
lean_object* v___f_3898_ = _args[5];
lean_object* v_onMotive_3899_ = _args[6];
lean_object* v_discrs_3900_ = _args[7];
lean_object* v_inst_3901_ = _args[8];
lean_object* v_matcherName_3902_ = _args[9];
lean_object* v_params_x27_3903_ = _args[10];
lean_object* v_onRemaining_3904_ = _args[11];
lean_object* v_remaining_3905_ = _args[12];
lean_object* v_inst_3906_ = _args[13];
lean_object* v_alts_3907_ = _args[14];
lean_object* v___f_3908_ = _args[15];
lean_object* v_onAlt_3909_ = _args[16];
lean_object* v___f_3910_ = _args[17];
lean_object* v_matcherApp_3911_ = _args[18];
lean_object* v_useSplitter_3912_ = _args[19];
lean_object* v_isCasesOn_3913_ = _args[20];
lean_object* v___f_3914_ = _args[21];
lean_object* v___x_3915_ = _args[22];
lean_object* v___x_3916_ = _args[23];
lean_object* v_toMonadExceptOf_3917_ = _args[24];
lean_object* v___f_3918_ = _args[25];
lean_object* v_numDiscrEqs_3919_ = _args[26];
lean_object* v___f_3920_ = _args[27];
lean_object* v_matcherLevels_3921_ = _args[28];
lean_object* v_motive_3922_ = _args[29];
lean_object* v_discrs_x27_3923_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3924_; uint8_t v_isCasesOn_boxed_3925_; lean_object* v_res_3926_; 
v_useSplitter_boxed_3924_ = lean_unbox(v_useSplitter_3912_);
v_isCasesOn_boxed_3925_ = lean_unbox(v_isCasesOn_3913_);
v_res_3926_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3893_, v_inst_3894_, v_toBind_3895_, v_toMatcherInfo_3896_, v_inst_3897_, v___f_3898_, v_onMotive_3899_, v_discrs_3900_, v_inst_3901_, v_matcherName_3902_, v_params_x27_3903_, v_onRemaining_3904_, v_remaining_3905_, v_inst_3906_, v_alts_3907_, v___f_3908_, v_onAlt_3909_, v___f_3910_, v_matcherApp_3911_, v_useSplitter_boxed_3924_, v_isCasesOn_boxed_3925_, v___f_3914_, v___x_3915_, v___x_3916_, v_toMonadExceptOf_3917_, v___f_3918_, v_numDiscrEqs_3919_, v___f_3920_, v_matcherLevels_3921_, v_motive_3922_, v_discrs_x27_3923_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3927_, lean_object* v_inst_3928_, lean_object* v_toBind_3929_, lean_object* v_toMatcherInfo_3930_, lean_object* v_inst_3931_, lean_object* v___f_3932_, lean_object* v_onMotive_3933_, lean_object* v_discrs_3934_, lean_object* v_inst_3935_, lean_object* v_matcherName_3936_, lean_object* v_onRemaining_3937_, lean_object* v_remaining_3938_, lean_object* v_inst_3939_, lean_object* v_alts_3940_, lean_object* v___f_3941_, lean_object* v_onAlt_3942_, lean_object* v___f_3943_, lean_object* v_matcherApp_3944_, uint8_t v_useSplitter_3945_, uint8_t v_isCasesOn_3946_, lean_object* v___f_3947_, lean_object* v___x_3948_, lean_object* v___x_3949_, lean_object* v_toMonadExceptOf_3950_, lean_object* v___f_3951_, lean_object* v_numDiscrEqs_3952_, lean_object* v___f_3953_, lean_object* v_matcherLevels_3954_, lean_object* v_motive_3955_, lean_object* v_onParams_3956_, lean_object* v_params_x27_3957_){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___f_3960_; size_t v_sz_3961_; size_t v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3958_ = lean_box(v_useSplitter_3945_);
v___x_3959_ = lean_box(v_isCasesOn_3946_);
lean_inc_ref(v_discrs_3934_);
lean_inc_ref(v_inst_3931_);
lean_inc(v_toBind_3929_);
v___f_3960_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 31, 30);
lean_closure_set(v___f_3960_, 0, v_toPure_3927_);
lean_closure_set(v___f_3960_, 1, v_inst_3928_);
lean_closure_set(v___f_3960_, 2, v_toBind_3929_);
lean_closure_set(v___f_3960_, 3, v_toMatcherInfo_3930_);
lean_closure_set(v___f_3960_, 4, v_inst_3931_);
lean_closure_set(v___f_3960_, 5, v___f_3932_);
lean_closure_set(v___f_3960_, 6, v_onMotive_3933_);
lean_closure_set(v___f_3960_, 7, v_discrs_3934_);
lean_closure_set(v___f_3960_, 8, v_inst_3935_);
lean_closure_set(v___f_3960_, 9, v_matcherName_3936_);
lean_closure_set(v___f_3960_, 10, v_params_x27_3957_);
lean_closure_set(v___f_3960_, 11, v_onRemaining_3937_);
lean_closure_set(v___f_3960_, 12, v_remaining_3938_);
lean_closure_set(v___f_3960_, 13, v_inst_3939_);
lean_closure_set(v___f_3960_, 14, v_alts_3940_);
lean_closure_set(v___f_3960_, 15, v___f_3941_);
lean_closure_set(v___f_3960_, 16, v_onAlt_3942_);
lean_closure_set(v___f_3960_, 17, v___f_3943_);
lean_closure_set(v___f_3960_, 18, v_matcherApp_3944_);
lean_closure_set(v___f_3960_, 19, v___x_3958_);
lean_closure_set(v___f_3960_, 20, v___x_3959_);
lean_closure_set(v___f_3960_, 21, v___f_3947_);
lean_closure_set(v___f_3960_, 22, v___x_3948_);
lean_closure_set(v___f_3960_, 23, v___x_3949_);
lean_closure_set(v___f_3960_, 24, v_toMonadExceptOf_3950_);
lean_closure_set(v___f_3960_, 25, v___f_3951_);
lean_closure_set(v___f_3960_, 26, v_numDiscrEqs_3952_);
lean_closure_set(v___f_3960_, 27, v___f_3953_);
lean_closure_set(v___f_3960_, 28, v_matcherLevels_3954_);
lean_closure_set(v___f_3960_, 29, v_motive_3955_);
v_sz_3961_ = lean_array_size(v_discrs_3934_);
v___x_3962_ = ((size_t)0ULL);
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3931_, v_onParams_3956_, v_sz_3961_, v___x_3962_, v_discrs_3934_);
v___x_3964_ = lean_apply_4(v_toBind_3929_, lean_box(0), lean_box(0), v___x_3963_, v___f_3960_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3965_ = _args[0];
lean_object* v_inst_3966_ = _args[1];
lean_object* v_toBind_3967_ = _args[2];
lean_object* v_toMatcherInfo_3968_ = _args[3];
lean_object* v_inst_3969_ = _args[4];
lean_object* v___f_3970_ = _args[5];
lean_object* v_onMotive_3971_ = _args[6];
lean_object* v_discrs_3972_ = _args[7];
lean_object* v_inst_3973_ = _args[8];
lean_object* v_matcherName_3974_ = _args[9];
lean_object* v_onRemaining_3975_ = _args[10];
lean_object* v_remaining_3976_ = _args[11];
lean_object* v_inst_3977_ = _args[12];
lean_object* v_alts_3978_ = _args[13];
lean_object* v___f_3979_ = _args[14];
lean_object* v_onAlt_3980_ = _args[15];
lean_object* v___f_3981_ = _args[16];
lean_object* v_matcherApp_3982_ = _args[17];
lean_object* v_useSplitter_3983_ = _args[18];
lean_object* v_isCasesOn_3984_ = _args[19];
lean_object* v___f_3985_ = _args[20];
lean_object* v___x_3986_ = _args[21];
lean_object* v___x_3987_ = _args[22];
lean_object* v_toMonadExceptOf_3988_ = _args[23];
lean_object* v___f_3989_ = _args[24];
lean_object* v_numDiscrEqs_3990_ = _args[25];
lean_object* v___f_3991_ = _args[26];
lean_object* v_matcherLevels_3992_ = _args[27];
lean_object* v_motive_3993_ = _args[28];
lean_object* v_onParams_3994_ = _args[29];
lean_object* v_params_x27_3995_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_3996_; uint8_t v_isCasesOn_boxed_3997_; lean_object* v_res_3998_; 
v_useSplitter_boxed_3996_ = lean_unbox(v_useSplitter_3983_);
v_isCasesOn_boxed_3997_ = lean_unbox(v_isCasesOn_3984_);
v_res_3998_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3965_, v_inst_3966_, v_toBind_3967_, v_toMatcherInfo_3968_, v_inst_3969_, v___f_3970_, v_onMotive_3971_, v_discrs_3972_, v_inst_3973_, v_matcherName_3974_, v_onRemaining_3975_, v_remaining_3976_, v_inst_3977_, v_alts_3978_, v___f_3979_, v_onAlt_3980_, v___f_3981_, v_matcherApp_3982_, v_useSplitter_boxed_3996_, v_isCasesOn_boxed_3997_, v___f_3985_, v___x_3986_, v___x_3987_, v_toMonadExceptOf_3988_, v___f_3989_, v_numDiscrEqs_3990_, v___f_3991_, v_matcherLevels_3992_, v_motive_3993_, v_onParams_3994_, v_params_x27_3995_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_3999_, lean_object* v_inst_4000_, lean_object* v_toBind_4001_, lean_object* v_toMatcherInfo_4002_, lean_object* v_inst_4003_, lean_object* v___f_4004_, lean_object* v_onMotive_4005_, lean_object* v_discrs_4006_, lean_object* v_inst_4007_, lean_object* v_matcherName_4008_, lean_object* v_onRemaining_4009_, lean_object* v_remaining_4010_, lean_object* v_inst_4011_, lean_object* v_alts_4012_, lean_object* v___f_4013_, lean_object* v_onAlt_4014_, lean_object* v___f_4015_, lean_object* v_matcherApp_4016_, uint8_t v_useSplitter_4017_, uint8_t v_isCasesOn_4018_, lean_object* v___f_4019_, lean_object* v___x_4020_, lean_object* v___x_4021_, lean_object* v_toMonadExceptOf_4022_, lean_object* v___f_4023_, lean_object* v___f_4024_, lean_object* v_matcherLevels_4025_, lean_object* v_motive_4026_, lean_object* v_onParams_4027_, lean_object* v_params_4028_, lean_object* v_numDiscrEqs_4029_){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___f_4032_; size_t v_sz_4033_; size_t v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4030_ = lean_box(v_useSplitter_4017_);
v___x_4031_ = lean_box(v_isCasesOn_4018_);
lean_inc(v_onParams_4027_);
lean_inc_ref(v_inst_4003_);
lean_inc(v_toBind_4001_);
v___f_4032_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 31, 30);
lean_closure_set(v___f_4032_, 0, v_toPure_3999_);
lean_closure_set(v___f_4032_, 1, v_inst_4000_);
lean_closure_set(v___f_4032_, 2, v_toBind_4001_);
lean_closure_set(v___f_4032_, 3, v_toMatcherInfo_4002_);
lean_closure_set(v___f_4032_, 4, v_inst_4003_);
lean_closure_set(v___f_4032_, 5, v___f_4004_);
lean_closure_set(v___f_4032_, 6, v_onMotive_4005_);
lean_closure_set(v___f_4032_, 7, v_discrs_4006_);
lean_closure_set(v___f_4032_, 8, v_inst_4007_);
lean_closure_set(v___f_4032_, 9, v_matcherName_4008_);
lean_closure_set(v___f_4032_, 10, v_onRemaining_4009_);
lean_closure_set(v___f_4032_, 11, v_remaining_4010_);
lean_closure_set(v___f_4032_, 12, v_inst_4011_);
lean_closure_set(v___f_4032_, 13, v_alts_4012_);
lean_closure_set(v___f_4032_, 14, v___f_4013_);
lean_closure_set(v___f_4032_, 15, v_onAlt_4014_);
lean_closure_set(v___f_4032_, 16, v___f_4015_);
lean_closure_set(v___f_4032_, 17, v_matcherApp_4016_);
lean_closure_set(v___f_4032_, 18, v___x_4030_);
lean_closure_set(v___f_4032_, 19, v___x_4031_);
lean_closure_set(v___f_4032_, 20, v___f_4019_);
lean_closure_set(v___f_4032_, 21, v___x_4020_);
lean_closure_set(v___f_4032_, 22, v___x_4021_);
lean_closure_set(v___f_4032_, 23, v_toMonadExceptOf_4022_);
lean_closure_set(v___f_4032_, 24, v___f_4023_);
lean_closure_set(v___f_4032_, 25, v_numDiscrEqs_4029_);
lean_closure_set(v___f_4032_, 26, v___f_4024_);
lean_closure_set(v___f_4032_, 27, v_matcherLevels_4025_);
lean_closure_set(v___f_4032_, 28, v_motive_4026_);
lean_closure_set(v___f_4032_, 29, v_onParams_4027_);
v_sz_4033_ = lean_array_size(v_params_4028_);
v___x_4034_ = ((size_t)0ULL);
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4003_, v_onParams_4027_, v_sz_4033_, v___x_4034_, v_params_4028_);
v___x_4036_ = lean_apply_4(v_toBind_4001_, lean_box(0), lean_box(0), v___x_4035_, v___f_4032_);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4037_ = _args[0];
lean_object* v_inst_4038_ = _args[1];
lean_object* v_toBind_4039_ = _args[2];
lean_object* v_toMatcherInfo_4040_ = _args[3];
lean_object* v_inst_4041_ = _args[4];
lean_object* v___f_4042_ = _args[5];
lean_object* v_onMotive_4043_ = _args[6];
lean_object* v_discrs_4044_ = _args[7];
lean_object* v_inst_4045_ = _args[8];
lean_object* v_matcherName_4046_ = _args[9];
lean_object* v_onRemaining_4047_ = _args[10];
lean_object* v_remaining_4048_ = _args[11];
lean_object* v_inst_4049_ = _args[12];
lean_object* v_alts_4050_ = _args[13];
lean_object* v___f_4051_ = _args[14];
lean_object* v_onAlt_4052_ = _args[15];
lean_object* v___f_4053_ = _args[16];
lean_object* v_matcherApp_4054_ = _args[17];
lean_object* v_useSplitter_4055_ = _args[18];
lean_object* v_isCasesOn_4056_ = _args[19];
lean_object* v___f_4057_ = _args[20];
lean_object* v___x_4058_ = _args[21];
lean_object* v___x_4059_ = _args[22];
lean_object* v_toMonadExceptOf_4060_ = _args[23];
lean_object* v___f_4061_ = _args[24];
lean_object* v___f_4062_ = _args[25];
lean_object* v_matcherLevels_4063_ = _args[26];
lean_object* v_motive_4064_ = _args[27];
lean_object* v_onParams_4065_ = _args[28];
lean_object* v_params_4066_ = _args[29];
lean_object* v_numDiscrEqs_4067_ = _args[30];
_start:
{
uint8_t v_useSplitter_boxed_4068_; uint8_t v_isCasesOn_boxed_4069_; lean_object* v_res_4070_; 
v_useSplitter_boxed_4068_ = lean_unbox(v_useSplitter_4055_);
v_isCasesOn_boxed_4069_ = lean_unbox(v_isCasesOn_4056_);
v_res_4070_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4037_, v_inst_4038_, v_toBind_4039_, v_toMatcherInfo_4040_, v_inst_4041_, v___f_4042_, v_onMotive_4043_, v_discrs_4044_, v_inst_4045_, v_matcherName_4046_, v_onRemaining_4047_, v_remaining_4048_, v_inst_4049_, v_alts_4050_, v___f_4051_, v_onAlt_4052_, v___f_4053_, v_matcherApp_4054_, v_useSplitter_boxed_4068_, v_isCasesOn_boxed_4069_, v___f_4057_, v___x_4058_, v___x_4059_, v_toMonadExceptOf_4060_, v___f_4061_, v___f_4062_, v_matcherLevels_4063_, v_motive_4064_, v_onParams_4065_, v_params_4066_, v_numDiscrEqs_4067_);
return v_res_4070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4071_, lean_object* v_numDiscrEqs_4072_){
_start:
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_apply_1(v___f_4071_, v_numDiscrEqs_4072_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4076_ = l_Lean_stringToMessageData(v___x_4075_);
return v___x_4076_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4079_ = l_Lean_stringToMessageData(v___x_4078_);
return v___x_4079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4080_, lean_object* v_inst_4081_, lean_object* v_inst_4082_, lean_object* v_toBind_4083_, lean_object* v___f_4084_, lean_object* v_toPure_4085_, lean_object* v___f_4086_, lean_object* v_____do__lift_4087_){
_start:
{
if (lean_obj_tag(v_____do__lift_4087_) == 0)
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
lean_dec(v___f_4086_);
lean_dec(v_toPure_4085_);
v___x_4088_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4089_ = l_Lean_MessageData_ofName(v_matcherName_4080_);
v___x_4090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4088_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
v___x_4091_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4090_);
lean_ctor_set(v___x_4092_, 1, v___x_4091_);
v___x_4093_ = l_Lean_throwError___redArg(v_inst_4081_, v_inst_4082_, v___x_4092_);
v___x_4094_ = lean_apply_4(v_toBind_4083_, lean_box(0), lean_box(0), v___x_4093_, v___f_4084_);
return v___x_4094_;
}
else
{
lean_object* v_val_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
lean_dec(v___f_4084_);
lean_dec_ref(v_inst_4082_);
lean_dec_ref(v_inst_4081_);
lean_dec(v_matcherName_4080_);
v_val_4095_ = lean_ctor_get(v_____do__lift_4087_, 0);
v___x_4096_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4095_);
v___x_4097_ = lean_apply_2(v_toPure_4085_, lean_box(0), v___x_4096_);
v___x_4098_ = lean_apply_4(v_toBind_4083_, lean_box(0), lean_box(0), v___x_4097_, v___f_4086_);
return v___x_4098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4099_, lean_object* v_inst_4100_, lean_object* v_inst_4101_, lean_object* v_toBind_4102_, lean_object* v___f_4103_, lean_object* v_toPure_4104_, lean_object* v___f_4105_, lean_object* v_____do__lift_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4099_, v_inst_4100_, v_inst_4101_, v_toBind_4102_, v___f_4103_, v_toPure_4104_, v___f_4105_, v_____do__lift_4106_);
lean_dec(v_____do__lift_4106_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4108_, lean_object* v_toPure_4109_, lean_object* v_inst_4110_, lean_object* v_toBind_4111_, lean_object* v_inst_4112_, lean_object* v___f_4113_, lean_object* v_onMotive_4114_, lean_object* v_inst_4115_, lean_object* v_onRemaining_4116_, lean_object* v_inst_4117_, lean_object* v___f_4118_, lean_object* v_onAlt_4119_, lean_object* v___f_4120_, uint8_t v_useSplitter_4121_, lean_object* v___f_4122_, lean_object* v___x_4123_, lean_object* v___x_4124_, lean_object* v_toMonadExceptOf_4125_, lean_object* v___f_4126_, lean_object* v___f_4127_, lean_object* v_onParams_4128_, lean_object* v_inst_4129_, lean_object* v_____do__lift_4130_){
_start:
{
lean_object* v_toMatcherInfo_4131_; lean_object* v_matcherName_4132_; lean_object* v_matcherLevels_4133_; lean_object* v_params_4134_; lean_object* v_motive_4135_; lean_object* v_discrs_4136_; lean_object* v_alts_4137_; lean_object* v_remaining_4138_; uint8_t v_isCasesOn_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___f_4142_; 
v_toMatcherInfo_4131_ = lean_ctor_get(v_matcherApp_4108_, 0);
lean_inc_ref(v_toMatcherInfo_4131_);
v_matcherName_4132_ = lean_ctor_get(v_matcherApp_4108_, 1);
lean_inc_n(v_matcherName_4132_, 3);
v_matcherLevels_4133_ = lean_ctor_get(v_matcherApp_4108_, 2);
lean_inc_ref(v_matcherLevels_4133_);
v_params_4134_ = lean_ctor_get(v_matcherApp_4108_, 3);
lean_inc_ref(v_params_4134_);
v_motive_4135_ = lean_ctor_get(v_matcherApp_4108_, 4);
lean_inc_ref(v_motive_4135_);
v_discrs_4136_ = lean_ctor_get(v_matcherApp_4108_, 5);
lean_inc_ref(v_discrs_4136_);
v_alts_4137_ = lean_ctor_get(v_matcherApp_4108_, 6);
lean_inc_ref(v_alts_4137_);
v_remaining_4138_ = lean_ctor_get(v_matcherApp_4108_, 7);
lean_inc_ref(v_remaining_4138_);
v_isCasesOn_4139_ = l_Lean_isCasesOnRecursor(v_____do__lift_4130_, v_matcherName_4132_);
v___x_4140_ = lean_box(v_useSplitter_4121_);
v___x_4141_ = lean_box(v_isCasesOn_4139_);
lean_inc_ref(v_inst_4115_);
lean_inc_ref(v_inst_4112_);
lean_inc(v_toBind_4111_);
lean_inc(v_toPure_4109_);
v___f_4142_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 31, 30);
lean_closure_set(v___f_4142_, 0, v_toPure_4109_);
lean_closure_set(v___f_4142_, 1, v_inst_4110_);
lean_closure_set(v___f_4142_, 2, v_toBind_4111_);
lean_closure_set(v___f_4142_, 3, v_toMatcherInfo_4131_);
lean_closure_set(v___f_4142_, 4, v_inst_4112_);
lean_closure_set(v___f_4142_, 5, v___f_4113_);
lean_closure_set(v___f_4142_, 6, v_onMotive_4114_);
lean_closure_set(v___f_4142_, 7, v_discrs_4136_);
lean_closure_set(v___f_4142_, 8, v_inst_4115_);
lean_closure_set(v___f_4142_, 9, v_matcherName_4132_);
lean_closure_set(v___f_4142_, 10, v_onRemaining_4116_);
lean_closure_set(v___f_4142_, 11, v_remaining_4138_);
lean_closure_set(v___f_4142_, 12, v_inst_4117_);
lean_closure_set(v___f_4142_, 13, v_alts_4137_);
lean_closure_set(v___f_4142_, 14, v___f_4118_);
lean_closure_set(v___f_4142_, 15, v_onAlt_4119_);
lean_closure_set(v___f_4142_, 16, v___f_4120_);
lean_closure_set(v___f_4142_, 17, v_matcherApp_4108_);
lean_closure_set(v___f_4142_, 18, v___x_4140_);
lean_closure_set(v___f_4142_, 19, v___x_4141_);
lean_closure_set(v___f_4142_, 20, v___f_4122_);
lean_closure_set(v___f_4142_, 21, v___x_4123_);
lean_closure_set(v___f_4142_, 22, v___x_4124_);
lean_closure_set(v___f_4142_, 23, v_toMonadExceptOf_4125_);
lean_closure_set(v___f_4142_, 24, v___f_4126_);
lean_closure_set(v___f_4142_, 25, v___f_4127_);
lean_closure_set(v___f_4142_, 26, v_matcherLevels_4133_);
lean_closure_set(v___f_4142_, 27, v_motive_4135_);
lean_closure_set(v___f_4142_, 28, v_onParams_4128_);
lean_closure_set(v___f_4142_, 29, v_params_4134_);
if (v_isCasesOn_4139_ == 0)
{
lean_object* v___f_4143_; lean_object* v___f_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___f_4143_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4143_, 0, v___f_4142_);
lean_inc_ref(v___f_4143_);
lean_inc(v_toBind_4111_);
lean_inc_ref(v_inst_4112_);
lean_inc(v_matcherName_4132_);
v___f_4144_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4144_, 0, v_matcherName_4132_);
lean_closure_set(v___f_4144_, 1, v_inst_4112_);
lean_closure_set(v___f_4144_, 2, v_inst_4115_);
lean_closure_set(v___f_4144_, 3, v_toBind_4111_);
lean_closure_set(v___f_4144_, 4, v___f_4143_);
lean_closure_set(v___f_4144_, 5, v_toPure_4109_);
lean_closure_set(v___f_4144_, 6, v___f_4143_);
v___x_4145_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4112_, v_inst_4129_, v_matcherName_4132_);
v___x_4146_ = lean_apply_4(v_toBind_4111_, lean_box(0), lean_box(0), v___x_4145_, v___f_4144_);
return v___x_4146_;
}
else
{
lean_object* v___f_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_dec(v_matcherName_4132_);
lean_dec_ref(v_inst_4129_);
lean_dec_ref(v_inst_4115_);
lean_dec_ref(v_inst_4112_);
v___f_4147_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4147_, 0, v___f_4142_);
v___x_4148_ = lean_unsigned_to_nat(0u);
v___x_4149_ = lean_apply_2(v_toPure_4109_, lean_box(0), v___x_4148_);
v___x_4150_ = lean_apply_4(v_toBind_4111_, lean_box(0), lean_box(0), v___x_4149_, v___f_4147_);
return v___x_4150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object** _args){
lean_object* v_matcherApp_4151_ = _args[0];
lean_object* v_toPure_4152_ = _args[1];
lean_object* v_inst_4153_ = _args[2];
lean_object* v_toBind_4154_ = _args[3];
lean_object* v_inst_4155_ = _args[4];
lean_object* v___f_4156_ = _args[5];
lean_object* v_onMotive_4157_ = _args[6];
lean_object* v_inst_4158_ = _args[7];
lean_object* v_onRemaining_4159_ = _args[8];
lean_object* v_inst_4160_ = _args[9];
lean_object* v___f_4161_ = _args[10];
lean_object* v_onAlt_4162_ = _args[11];
lean_object* v___f_4163_ = _args[12];
lean_object* v_useSplitter_4164_ = _args[13];
lean_object* v___f_4165_ = _args[14];
lean_object* v___x_4166_ = _args[15];
lean_object* v___x_4167_ = _args[16];
lean_object* v_toMonadExceptOf_4168_ = _args[17];
lean_object* v___f_4169_ = _args[18];
lean_object* v___f_4170_ = _args[19];
lean_object* v_onParams_4171_ = _args[20];
lean_object* v_inst_4172_ = _args[21];
lean_object* v_____do__lift_4173_ = _args[22];
_start:
{
uint8_t v_useSplitter_boxed_4174_; lean_object* v_res_4175_; 
v_useSplitter_boxed_4174_ = lean_unbox(v_useSplitter_4164_);
v_res_4175_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4151_, v_toPure_4152_, v_inst_4153_, v_toBind_4154_, v_inst_4155_, v___f_4156_, v_onMotive_4157_, v_inst_4158_, v_onRemaining_4159_, v_inst_4160_, v___f_4161_, v_onAlt_4162_, v___f_4163_, v_useSplitter_boxed_4174_, v___f_4165_, v___x_4166_, v___x_4167_, v_toMonadExceptOf_4168_, v___f_4169_, v___f_4170_, v_onParams_4171_, v_inst_4172_, v_____do__lift_4173_);
return v_res_4175_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0(void){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Subarray_empty___redArg();
return v___x_4176_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1(void){
_start:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
lean_ctor_set(v___x_4178_, 1, v___x_4177_);
return v___x_4178_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4179_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__1);
v___x_4180_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
lean_ctor_set(v___x_4181_, 1, v___x_4179_);
return v___x_4181_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3(void){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Array_instInhabited___redArg();
return v___x_4182_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4(void){
_start:
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4183_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__2);
v___x_4184_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v___x_4183_);
return v___x_4185_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5(void){
_start:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4186_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__4);
v___x_4187_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__0);
v___x_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
lean_ctor_set(v___x_4188_, 1, v___x_4186_);
return v___x_4188_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6(void){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__5);
v___x_4190_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__3);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4190_);
lean_ctor_set(v___x_4191_, 1, v___x_4189_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__6);
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4192_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4194_, lean_object* v_inst_4195_, lean_object* v_inst_4196_, lean_object* v_inst_4197_, lean_object* v_inst_4198_, lean_object* v_matcherApp_4199_, uint8_t v_useSplitter_4200_, uint8_t v_addEqualities_4201_, lean_object* v_onParams_4202_, lean_object* v_onMotive_4203_, lean_object* v_onAlt_4204_, lean_object* v_onRemaining_4205_){
_start:
{
lean_object* v_toApplicative_4206_; lean_object* v_toBind_4207_; lean_object* v_getEnv_4208_; lean_object* v_toPure_4209_; lean_object* v_toMonadExceptOf_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___f_4213_; lean_object* v___f_4214_; lean_object* v___f_4215_; lean_object* v___x_4216_; lean_object* v___f_4217_; lean_object* v___x_4218_; lean_object* v___f_4219_; lean_object* v___f_4220_; lean_object* v___f_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___f_4224_; lean_object* v___x_4225_; 
v_toApplicative_4206_ = lean_ctor_get(v_inst_4196_, 0);
v_toBind_4207_ = lean_ctor_get(v_inst_4196_, 1);
lean_inc_n(v_toBind_4207_, 4);
v_getEnv_4208_ = lean_ctor_get(v_inst_4198_, 0);
lean_inc(v_getEnv_4208_);
v_toPure_4209_ = lean_ctor_get(v_toApplicative_4206_, 1);
lean_inc_n(v_toPure_4209_, 5);
v_toMonadExceptOf_4210_ = lean_ctor_get(v_inst_4197_, 0);
lean_inc_ref(v_toMonadExceptOf_4210_);
v___x_4211_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
lean_inc_ref_n(v_inst_4196_, 4);
v___x_4212_ = l_instInhabitedOfMonad___redArg(v_inst_4196_, v___x_4211_);
lean_inc_ref(v_inst_4197_);
v___f_4213_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4213_, 0, v_inst_4196_);
lean_closure_set(v___f_4213_, 1, v_inst_4197_);
lean_inc_n(v_inst_4194_, 3);
v___f_4214_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4214_, 0, v_inst_4194_);
v___f_4215_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4215_, 0, v_inst_4196_);
lean_closure_set(v___f_4215_, 1, v___f_4214_);
v___x_4216_ = l_Lean_instInhabitedExpr;
v___f_4217_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5), 6, 3);
lean_closure_set(v___f_4217_, 0, v_toPure_4209_);
lean_closure_set(v___f_4217_, 1, v_inst_4194_);
lean_closure_set(v___f_4217_, 2, v_toBind_4207_);
v___x_4218_ = lean_box(v_addEqualities_4201_);
v___f_4219_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_4219_, 0, v_toPure_4209_);
lean_closure_set(v___f_4219_, 1, v___x_4218_);
lean_closure_set(v___f_4219_, 2, v_inst_4194_);
lean_closure_set(v___f_4219_, 3, v_toBind_4207_);
v___f_4220_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11), 2, 1);
lean_closure_set(v___f_4220_, 0, v_toPure_4209_);
v___f_4221_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12), 2, 1);
lean_closure_set(v___f_4221_, 0, v_toPure_4209_);
v___x_4222_ = l_instInhabitedOfMonad___redArg(v_inst_4196_, v___x_4216_);
v___x_4223_ = lean_box(v_useSplitter_4200_);
v___f_4224_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 23, 22);
lean_closure_set(v___f_4224_, 0, v_matcherApp_4199_);
lean_closure_set(v___f_4224_, 1, v_toPure_4209_);
lean_closure_set(v___f_4224_, 2, v_inst_4194_);
lean_closure_set(v___f_4224_, 3, v_toBind_4207_);
lean_closure_set(v___f_4224_, 4, v_inst_4196_);
lean_closure_set(v___f_4224_, 5, v___f_4219_);
lean_closure_set(v___f_4224_, 6, v_onMotive_4203_);
lean_closure_set(v___f_4224_, 7, v_inst_4197_);
lean_closure_set(v___f_4224_, 8, v_onRemaining_4205_);
lean_closure_set(v___f_4224_, 9, v_inst_4195_);
lean_closure_set(v___f_4224_, 10, v___f_4221_);
lean_closure_set(v___f_4224_, 11, v_onAlt_4204_);
lean_closure_set(v___f_4224_, 12, v___f_4215_);
lean_closure_set(v___f_4224_, 13, v___x_4223_);
lean_closure_set(v___f_4224_, 14, v___f_4220_);
lean_closure_set(v___f_4224_, 15, v___x_4212_);
lean_closure_set(v___f_4224_, 16, v___x_4222_);
lean_closure_set(v___f_4224_, 17, v_toMonadExceptOf_4210_);
lean_closure_set(v___f_4224_, 18, v___f_4213_);
lean_closure_set(v___f_4224_, 19, v___f_4217_);
lean_closure_set(v___f_4224_, 20, v_onParams_4202_);
lean_closure_set(v___f_4224_, 21, v_inst_4198_);
v___x_4225_ = lean_apply_4(v_toBind_4207_, lean_box(0), lean_box(0), v_getEnv_4208_, v___f_4224_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4226_, lean_object* v_inst_4227_, lean_object* v_inst_4228_, lean_object* v_inst_4229_, lean_object* v_inst_4230_, lean_object* v_matcherApp_4231_, lean_object* v_useSplitter_4232_, lean_object* v_addEqualities_4233_, lean_object* v_onParams_4234_, lean_object* v_onMotive_4235_, lean_object* v_onAlt_4236_, lean_object* v_onRemaining_4237_){
_start:
{
uint8_t v_useSplitter_boxed_4238_; uint8_t v_addEqualities_boxed_4239_; lean_object* v_res_4240_; 
v_useSplitter_boxed_4238_ = lean_unbox(v_useSplitter_4232_);
v_addEqualities_boxed_4239_ = lean_unbox(v_addEqualities_4233_);
v_res_4240_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4226_, v_inst_4227_, v_inst_4228_, v_inst_4229_, v_inst_4230_, v_matcherApp_4231_, v_useSplitter_boxed_4238_, v_addEqualities_boxed_4239_, v_onParams_4234_, v_onMotive_4235_, v_onAlt_4236_, v_onRemaining_4237_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4241_, lean_object* v_inst_4242_, lean_object* v_inst_4243_, lean_object* v_inst_4244_, lean_object* v_inst_4245_, lean_object* v_inst_4246_, lean_object* v_inst_4247_, lean_object* v_inst_4248_, lean_object* v_inst_4249_, lean_object* v_matcherApp_4250_, uint8_t v_useSplitter_4251_, uint8_t v_addEqualities_4252_, lean_object* v_onParams_4253_, lean_object* v_onMotive_4254_, lean_object* v_onAlt_4255_, lean_object* v_onRemaining_4256_){
_start:
{
lean_object* v___x_4257_; 
v___x_4257_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4242_, v_inst_4243_, v_inst_4244_, v_inst_4245_, v_inst_4246_, v_matcherApp_4250_, v_useSplitter_4251_, v_addEqualities_4252_, v_onParams_4253_, v_onMotive_4254_, v_onAlt_4255_, v_onRemaining_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4258_, lean_object* v_inst_4259_, lean_object* v_inst_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_inst_4263_, lean_object* v_inst_4264_, lean_object* v_inst_4265_, lean_object* v_inst_4266_, lean_object* v_matcherApp_4267_, lean_object* v_useSplitter_4268_, lean_object* v_addEqualities_4269_, lean_object* v_onParams_4270_, lean_object* v_onMotive_4271_, lean_object* v_onAlt_4272_, lean_object* v_onRemaining_4273_){
_start:
{
uint8_t v_useSplitter_boxed_4274_; uint8_t v_addEqualities_boxed_4275_; lean_object* v_res_4276_; 
v_useSplitter_boxed_4274_ = lean_unbox(v_useSplitter_4268_);
v_addEqualities_boxed_4275_ = lean_unbox(v_addEqualities_4269_);
v_res_4276_ = l_Lean_Meta_MatcherApp_transform(v_n_4258_, v_inst_4259_, v_inst_4260_, v_inst_4261_, v_inst_4262_, v_inst_4263_, v_inst_4264_, v_inst_4265_, v_inst_4266_, v_matcherApp_4267_, v_useSplitter_boxed_4274_, v_addEqualities_boxed_4275_, v_onParams_4270_, v_onMotive_4271_, v_onAlt_4272_, v_onRemaining_4273_);
lean_dec_ref(v_inst_4266_);
lean_dec(v_inst_4265_);
lean_dec_ref(v_inst_4264_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_){
_start:
{
lean_object* v___x_4283_; 
v___x_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4283_, 0, v___y_4277_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4297_, 0, v___y_4291_);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
return v_res_4304_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4305_, lean_object* v_opt_4306_){
_start:
{
lean_object* v_name_4307_; lean_object* v_defValue_4308_; lean_object* v_map_4309_; lean_object* v___x_4310_; 
v_name_4307_ = lean_ctor_get(v_opt_4306_, 0);
v_defValue_4308_ = lean_ctor_get(v_opt_4306_, 1);
v_map_4309_ = lean_ctor_get(v_opts_4305_, 0);
v___x_4310_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4309_, v_name_4307_);
if (lean_obj_tag(v___x_4310_) == 0)
{
uint8_t v___x_4311_; 
v___x_4311_ = lean_unbox(v_defValue_4308_);
return v___x_4311_;
}
else
{
lean_object* v_val_4312_; 
v_val_4312_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_val_4312_);
lean_dec_ref_known(v___x_4310_, 1);
if (lean_obj_tag(v_val_4312_) == 1)
{
uint8_t v_v_4313_; 
v_v_4313_ = lean_ctor_get_uint8(v_val_4312_, 0);
lean_dec_ref_known(v_val_4312_, 0);
return v_v_4313_;
}
else
{
uint8_t v___x_4314_; 
lean_dec(v_val_4312_);
v___x_4314_ = lean_unbox(v_defValue_4308_);
return v___x_4314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4315_, lean_object* v_opt_4316_){
_start:
{
uint8_t v_res_4317_; lean_object* v_r_4318_; 
v_res_4317_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4315_, v_opt_4316_);
lean_dec_ref(v_opt_4316_);
lean_dec_ref(v_opts_4315_);
v_r_4318_ = lean_box(v_res_4317_);
return v_r_4318_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_4327_, uint8_t v___y_4328_, lean_object* v_x_4329_){
_start:
{
if (lean_obj_tag(v_x_4329_) == 1)
{
lean_object* v_pre_4330_; 
v_pre_4330_ = lean_ctor_get(v_x_4329_, 0);
switch(lean_obj_tag(v_pre_4330_))
{
case 1:
{
lean_object* v_pre_4331_; 
v_pre_4331_ = lean_ctor_get(v_pre_4330_, 0);
switch(lean_obj_tag(v_pre_4331_))
{
case 0:
{
lean_object* v_str_4332_; lean_object* v_str_4333_; lean_object* v___x_4334_; uint8_t v___x_4335_; 
v_str_4332_ = lean_ctor_get(v_x_4329_, 1);
v_str_4333_ = lean_ctor_get(v_pre_4330_, 1);
v___x_4334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4335_ = lean_string_dec_eq(v_str_4333_, v___x_4334_);
if (v___x_4335_ == 0)
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4337_ = lean_string_dec_eq(v_str_4333_, v___x_4336_);
if (v___x_4337_ == 0)
{
return v___x_4337_;
}
else
{
lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4339_ = lean_string_dec_eq(v_str_4332_, v___x_4338_);
if (v___x_4339_ == 0)
{
return v___x_4339_;
}
else
{
return v_suppressElabErrors_4327_;
}
}
}
else
{
lean_object* v___x_4340_; uint8_t v___x_4341_; 
v___x_4340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4341_ = lean_string_dec_eq(v_str_4332_, v___x_4340_);
if (v___x_4341_ == 0)
{
return v___x_4341_;
}
else
{
return v_suppressElabErrors_4327_;
}
}
}
case 1:
{
lean_object* v_pre_4342_; 
v_pre_4342_ = lean_ctor_get(v_pre_4331_, 0);
if (lean_obj_tag(v_pre_4342_) == 0)
{
lean_object* v_str_4343_; lean_object* v_str_4344_; lean_object* v_str_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; 
v_str_4343_ = lean_ctor_get(v_x_4329_, 1);
v_str_4344_ = lean_ctor_get(v_pre_4330_, 1);
v_str_4345_ = lean_ctor_get(v_pre_4331_, 1);
v___x_4346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4347_ = lean_string_dec_eq(v_str_4345_, v___x_4346_);
if (v___x_4347_ == 0)
{
return v___x_4347_;
}
else
{
lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4348_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4349_ = lean_string_dec_eq(v_str_4344_, v___x_4348_);
if (v___x_4349_ == 0)
{
return v___x_4349_;
}
else
{
lean_object* v___x_4350_; uint8_t v___x_4351_; 
v___x_4350_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4351_ = lean_string_dec_eq(v_str_4343_, v___x_4350_);
if (v___x_4351_ == 0)
{
return v___x_4351_;
}
else
{
return v_suppressElabErrors_4327_;
}
}
}
}
else
{
return v___y_4328_;
}
}
default: 
{
return v___y_4328_;
}
}
}
case 0:
{
lean_object* v_str_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
v_str_4352_ = lean_ctor_get(v_x_4329_, 1);
v___x_4353_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4354_ = lean_string_dec_eq(v_str_4352_, v___x_4353_);
if (v___x_4354_ == 0)
{
return v___x_4354_;
}
else
{
return v_suppressElabErrors_4327_;
}
}
default: 
{
return v___y_4328_;
}
}
}
else
{
return v___y_4328_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_4355_, lean_object* v___y_4356_, lean_object* v_x_4357_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4358_; uint8_t v___y_32220__boxed_4359_; uint8_t v_res_4360_; lean_object* v_r_4361_; 
v_suppressElabErrors_boxed_4358_ = lean_unbox(v_suppressElabErrors_4355_);
v___y_32220__boxed_4359_ = lean_unbox(v___y_4356_);
v_res_4360_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_4358_, v___y_32220__boxed_4359_, v_x_4357_);
lean_dec(v_x_4357_);
v_r_4361_ = lean_box(v_res_4360_);
return v_r_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4363_, lean_object* v_msgData_4364_, uint8_t v_severity_4365_, uint8_t v_isSilent_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
uint8_t v___y_4373_; lean_object* v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; uint8_t v___y_4379_; lean_object* v_toCold_4380_; lean_object* v___y_4381_; lean_object* v___y_4410_; lean_object* v___y_4411_; uint8_t v___y_4412_; lean_object* v___y_4413_; uint8_t v___y_4414_; lean_object* v___y_4415_; uint8_t v___y_4416_; lean_object* v___y_4417_; uint8_t v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; uint8_t v___y_4441_; uint8_t v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4447_; uint8_t v___y_4448_; uint8_t v___y_4449_; uint8_t v___x_4460_; uint8_t v___y_4462_; uint8_t v___y_4463_; uint8_t v___y_4464_; uint8_t v___y_4466_; uint8_t v___x_4474_; 
v___x_4460_ = 2;
v___x_4474_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4365_, v___x_4460_);
if (v___x_4474_ == 0)
{
v___y_4466_ = v___x_4474_;
goto v___jp_4465_;
}
else
{
uint8_t v___x_4475_; 
lean_inc_ref(v_msgData_4364_);
v___x_4475_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4364_);
v___y_4466_ = v___x_4475_;
goto v___jp_4465_;
}
v___jp_4372_:
{
lean_object* v_currNamespace_4382_; lean_object* v_openDecls_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v_env_4388_; lean_object* v_nextMacroScope_4389_; lean_object* v_ngen_4390_; lean_object* v_auxDeclNGen_4391_; lean_object* v_traceState_4392_; lean_object* v_cache_4393_; lean_object* v_recordedDeps_4394_; lean_object* v_messages_4395_; lean_object* v_infoState_4396_; lean_object* v_snapshotTasks_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4408_; 
v_currNamespace_4382_ = lean_ctor_get(v_toCold_4380_, 4);
v_openDecls_4383_ = lean_ctor_get(v_toCold_4380_, 5);
lean_inc(v_openDecls_4383_);
lean_inc(v_currNamespace_4382_);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v_currNamespace_4382_);
lean_ctor_set(v___x_4384_, 1, v_openDecls_4383_);
v___x_4385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
lean_ctor_set(v___x_4385_, 1, v___y_4375_);
lean_inc_ref(v___y_4374_);
lean_inc_ref(v___y_4378_);
v___x_4386_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4386_, 0, v___y_4378_);
lean_ctor_set(v___x_4386_, 1, v___y_4376_);
lean_ctor_set(v___x_4386_, 2, v___y_4377_);
lean_ctor_set(v___x_4386_, 3, v___y_4374_);
lean_ctor_set(v___x_4386_, 4, v___x_4385_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*5, v___y_4373_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*5 + 1, v___y_4379_);
lean_ctor_set_uint8(v___x_4386_, sizeof(void*)*5 + 2, v_isSilent_4366_);
v___x_4387_ = lean_st_ref_take(v___y_4381_);
v_env_4388_ = lean_ctor_get(v___x_4387_, 0);
v_nextMacroScope_4389_ = lean_ctor_get(v___x_4387_, 1);
v_ngen_4390_ = lean_ctor_get(v___x_4387_, 2);
v_auxDeclNGen_4391_ = lean_ctor_get(v___x_4387_, 3);
v_traceState_4392_ = lean_ctor_get(v___x_4387_, 4);
v_cache_4393_ = lean_ctor_get(v___x_4387_, 5);
v_recordedDeps_4394_ = lean_ctor_get(v___x_4387_, 6);
v_messages_4395_ = lean_ctor_get(v___x_4387_, 7);
v_infoState_4396_ = lean_ctor_get(v___x_4387_, 8);
v_snapshotTasks_4397_ = lean_ctor_get(v___x_4387_, 9);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4387_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4399_ = v___x_4387_;
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_snapshotTasks_4397_);
lean_inc(v_infoState_4396_);
lean_inc(v_messages_4395_);
lean_inc(v_recordedDeps_4394_);
lean_inc(v_cache_4393_);
lean_inc(v_traceState_4392_);
lean_inc(v_auxDeclNGen_4391_);
lean_inc(v_ngen_4390_);
lean_inc(v_nextMacroScope_4389_);
lean_inc(v_env_4388_);
lean_dec(v___x_4387_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4408_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4404_; 
v___x_4401_ = lean_box(0);
v___x_4402_ = l_Lean_MessageLog_add(v___x_4386_, v_messages_4395_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 7, v___x_4402_);
v___x_4404_ = v___x_4399_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_env_4388_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_nextMacroScope_4389_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_ngen_4390_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_auxDeclNGen_4391_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_traceState_4392_);
lean_ctor_set(v_reuseFailAlloc_4407_, 5, v_cache_4393_);
lean_ctor_set(v_reuseFailAlloc_4407_, 6, v_recordedDeps_4394_);
lean_ctor_set(v_reuseFailAlloc_4407_, 7, v___x_4402_);
lean_ctor_set(v_reuseFailAlloc_4407_, 8, v_infoState_4396_);
lean_ctor_set(v_reuseFailAlloc_4407_, 9, v_snapshotTasks_4397_);
v___x_4404_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = lean_st_ref_put(v___y_4381_, v___x_4404_);
v___x_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4401_);
return v___x_4406_;
}
}
}
v___jp_4409_:
{
lean_object* v_fileName_4418_; lean_object* v_fileMap_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4435_; 
v_fileName_4418_ = lean_ctor_get(v___y_4415_, 0);
v_fileMap_4419_ = lean_ctor_get(v___y_4415_, 1);
v___x_4420_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4364_);
v___x_4421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4420_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
v_a_4422_ = lean_ctor_get(v___x_4421_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4424_ = v___x_4421_;
v_isShared_4425_ = v_isSharedCheck_4435_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4421_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4435_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
lean_inc_ref_n(v_fileMap_4419_, 2);
v___x_4426_ = l_Lean_FileMap_toPosition(v_fileMap_4419_, v___y_4413_);
lean_dec(v___y_4413_);
v___x_4427_ = l_Lean_FileMap_toPosition(v_fileMap_4419_, v___y_4417_);
lean_dec(v___y_4417_);
v___x_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4427_);
v___x_4429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4414_ == 0)
{
lean_del_object(v___x_4424_);
lean_dec_ref(v___y_4411_);
v___y_4373_ = v___y_4412_;
v___y_4374_ = v___x_4429_;
v___y_4375_ = v_a_4422_;
v___y_4376_ = v___x_4426_;
v___y_4377_ = v___x_4428_;
v___y_4378_ = v_fileName_4418_;
v___y_4379_ = v___y_4416_;
v_toCold_4380_ = v___y_4410_;
v___y_4381_ = v___y_4370_;
goto v___jp_4372_;
}
else
{
uint8_t v___x_4430_; 
lean_inc(v_a_4422_);
v___x_4430_ = l_Lean_MessageData_hasTag(v___y_4411_, v_a_4422_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; lean_object* v___x_4433_; 
lean_dec_ref_known(v___x_4428_, 1);
lean_dec_ref(v___x_4426_);
lean_dec(v_a_4422_);
v___x_4431_ = lean_box(0);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 0, v___x_4431_);
v___x_4433_ = v___x_4424_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4434_; 
v_reuseFailAlloc_4434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4431_);
v___x_4433_ = v_reuseFailAlloc_4434_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
return v___x_4433_;
}
}
else
{
lean_del_object(v___x_4424_);
v___y_4373_ = v___y_4412_;
v___y_4374_ = v___x_4429_;
v___y_4375_ = v_a_4422_;
v___y_4376_ = v___x_4426_;
v___y_4377_ = v___x_4428_;
v___y_4378_ = v_fileName_4418_;
v___y_4379_ = v___y_4416_;
v_toCold_4380_ = v___y_4410_;
v___y_4381_ = v___y_4370_;
goto v___jp_4372_;
}
}
}
}
v___jp_4436_:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_Syntax_getTailPos_x3f(v___y_4440_, v___y_4441_);
lean_dec(v___y_4440_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_inc(v___y_4443_);
v___y_4410_ = v___y_4438_;
v___y_4411_ = v___y_4439_;
v___y_4412_ = v___y_4441_;
v___y_4413_ = v___y_4443_;
v___y_4414_ = v___y_4437_;
v___y_4415_ = v___y_4438_;
v___y_4416_ = v___y_4442_;
v___y_4417_ = v___y_4443_;
goto v___jp_4409_;
}
else
{
lean_object* v_val_4445_; 
v_val_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_val_4445_);
lean_dec_ref_known(v___x_4444_, 1);
v___y_4410_ = v___y_4438_;
v___y_4411_ = v___y_4439_;
v___y_4412_ = v___y_4441_;
v___y_4413_ = v___y_4443_;
v___y_4414_ = v___y_4437_;
v___y_4415_ = v___y_4438_;
v___y_4416_ = v___y_4442_;
v___y_4417_ = v_val_4445_;
goto v___jp_4409_;
}
}
v___jp_4446_:
{
lean_object* v_toCold_4450_; lean_object* v_ref_4451_; uint8_t v_suppressElabErrors_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___f_4455_; lean_object* v_ref_4456_; lean_object* v___x_4457_; 
v_toCold_4450_ = lean_ctor_get(v___y_4369_, 0);
v_ref_4451_ = lean_ctor_get(v___y_4369_, 2);
v_suppressElabErrors_4452_ = lean_ctor_get_uint8(v___y_4369_, sizeof(void*)*3 + 2);
v___x_4453_ = lean_box(v_suppressElabErrors_4452_);
v___x_4454_ = lean_box(v___y_4447_);
v___f_4455_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4455_, 0, v___x_4453_);
lean_closure_set(v___f_4455_, 1, v___x_4454_);
v_ref_4456_ = l_Lean_replaceRef(v_ref_4363_, v_ref_4451_);
v___x_4457_ = l_Lean_Syntax_getPos_x3f(v_ref_4456_, v___y_4448_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v___x_4458_; 
v___x_4458_ = lean_unsigned_to_nat(0u);
v___y_4437_ = v_suppressElabErrors_4452_;
v___y_4438_ = v_toCold_4450_;
v___y_4439_ = v___f_4455_;
v___y_4440_ = v_ref_4456_;
v___y_4441_ = v___y_4448_;
v___y_4442_ = v___y_4449_;
v___y_4443_ = v___x_4458_;
goto v___jp_4436_;
}
else
{
lean_object* v_val_4459_; 
v_val_4459_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_val_4459_);
lean_dec_ref_known(v___x_4457_, 1);
v___y_4437_ = v_suppressElabErrors_4452_;
v___y_4438_ = v_toCold_4450_;
v___y_4439_ = v___f_4455_;
v___y_4440_ = v_ref_4456_;
v___y_4441_ = v___y_4448_;
v___y_4442_ = v___y_4449_;
v___y_4443_ = v_val_4459_;
goto v___jp_4436_;
}
}
v___jp_4461_:
{
if (v___y_4464_ == 0)
{
v___y_4447_ = v___y_4462_;
v___y_4448_ = v___y_4463_;
v___y_4449_ = v_severity_4365_;
goto v___jp_4446_;
}
else
{
v___y_4447_ = v___y_4462_;
v___y_4448_ = v___y_4463_;
v___y_4449_ = v___x_4460_;
goto v___jp_4446_;
}
}
v___jp_4465_:
{
if (v___y_4466_ == 0)
{
uint8_t v___x_4467_; uint8_t v___x_4468_; 
v___x_4467_ = 1;
v___x_4468_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4365_, v___x_4467_);
if (v___x_4468_ == 0)
{
v___y_4462_ = v___y_4466_;
v___y_4463_ = v___y_4466_;
v___y_4464_ = v___x_4468_;
goto v___jp_4461_;
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4470_; uint8_t v___x_4471_; 
v___x_4469_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4369_);
v___x_4470_ = l_Lean_warningAsError;
v___x_4471_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v___x_4469_, v___x_4470_);
lean_dec_ref(v___x_4469_);
v___y_4462_ = v___y_4466_;
v___y_4463_ = v___y_4466_;
v___y_4464_ = v___x_4471_;
goto v___jp_4461_;
}
}
else
{
lean_object* v___x_4472_; lean_object* v___x_4473_; 
lean_dec_ref(v_msgData_4364_);
v___x_4472_ = lean_box(0);
v___x_4473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4472_);
return v___x_4473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4476_, lean_object* v_msgData_4477_, lean_object* v_severity_4478_, lean_object* v_isSilent_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v_severity_boxed_4485_; uint8_t v_isSilent_boxed_4486_; lean_object* v_res_4487_; 
v_severity_boxed_4485_ = lean_unbox(v_severity_4478_);
v_isSilent_boxed_4486_ = lean_unbox(v_isSilent_4479_);
v_res_4487_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4476_, v_msgData_4477_, v_severity_boxed_4485_, v_isSilent_boxed_4486_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v_ref_4476_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4488_, uint8_t v_severity_4489_, uint8_t v_isSilent_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v_ref_4496_; lean_object* v___x_4497_; 
v_ref_4496_ = lean_ctor_get(v___y_4493_, 2);
v___x_4497_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4496_, v_msgData_4488_, v_severity_4489_, v_isSilent_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4498_, lean_object* v_severity_4499_, lean_object* v_isSilent_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
uint8_t v_severity_boxed_4506_; uint8_t v_isSilent_boxed_4507_; lean_object* v_res_4508_; 
v_severity_boxed_4506_ = lean_unbox(v_severity_4499_);
v_isSilent_boxed_4507_ = lean_unbox(v_isSilent_4500_);
v_res_4508_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4498_, v_severity_boxed_4506_, v_isSilent_boxed_4507_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
uint8_t v___x_4515_; uint8_t v___x_4516_; lean_object* v___x_4517_; 
v___x_4515_ = 0;
v___x_4516_ = 0;
v___x_4517_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4509_, v___x_4515_, v___x_4516_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
return v___x_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
return v_res_4524_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4527_ = l_Lean_stringToMessageData(v___x_4526_);
return v___x_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4528_, lean_object* v___altIdx_4529_, lean_object* v_expAltType_4530_, lean_object* v___altFVars_4531_, lean_object* v_alt_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_){
_start:
{
lean_object* v___x_4538_; 
lean_inc(v___y_4536_);
lean_inc_ref(v___y_4535_);
lean_inc(v___y_4534_);
lean_inc_ref(v___y_4533_);
lean_inc_ref(v_alt_4532_);
v___x_4538_ = lean_infer_type(v_alt_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v___x_4540_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v___x_4540_ = l_Lean_Meta_mkEq(v_expAltType_4530_, v_a_4539_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_a_4541_);
lean_dec_ref_known(v___x_4540_, 1);
v___x_4542_ = lean_box(0);
v___x_4543_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4541_, v___x_4542_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_object* v_a_4544_; lean_object* v___y_4546_; lean_object* v___x_4556_; lean_object* v___x_4557_; 
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
lean_inc(v_a_4544_);
lean_dec_ref_known(v___x_4543_, 1);
v___x_4556_ = l_Lean_Expr_mvarId_x21(v_a_4544_);
v___x_4557_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4556_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; lean_object* v___x_4559_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc_n(v_a_4558_, 2);
lean_dec_ref_known(v___x_4557_, 1);
v___x_4559_ = l_Lean_MVarId_refl(v_a_4558_, v___x_4528_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4559_) == 0)
{
lean_dec(v_a_4558_);
v___y_4546_ = v___x_4559_;
goto v___jp_4545_;
}
else
{
lean_object* v_a_4560_; uint8_t v___y_4562_; uint8_t v___x_4575_; 
v_a_4560_ = lean_ctor_get(v___x_4559_, 0);
v___x_4575_ = l_Lean_Exception_isInterrupt(v_a_4560_);
if (v___x_4575_ == 0)
{
uint8_t v___x_4576_; 
lean_inc(v_a_4560_);
v___x_4576_ = l_Lean_Exception_isRuntime(v_a_4560_);
v___y_4562_ = v___x_4576_;
goto v___jp_4561_;
}
else
{
v___y_4562_ = v___x_4575_;
goto v___jp_4561_;
}
v___jp_4561_:
{
if (v___y_4562_ == 0)
{
lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4573_; 
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4559_);
if (v_isSharedCheck_4573_ == 0)
{
lean_object* v_unused_4574_; 
v_unused_4574_ = lean_ctor_get(v___x_4559_, 0);
lean_dec(v_unused_4574_);
v___x_4564_ = v___x_4559_;
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
else
{
lean_dec(v___x_4559_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4573_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4566_; lean_object* v___x_4568_; 
v___x_4566_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4558_);
if (v_isShared_4565_ == 0)
{
lean_ctor_set(v___x_4564_, 0, v_a_4558_);
v___x_4568_ = v___x_4564_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4558_);
v___x_4568_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; 
v___x_4569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4569_, 0, v___x_4566_);
lean_ctor_set(v___x_4569_, 1, v___x_4568_);
v___x_4570_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4569_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_object* v___x_4571_; 
lean_dec_ref_known(v___x_4570_, 1);
v___x_4571_ = l_Lean_MVarId_admit(v_a_4558_, v___x_4528_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
v___y_4546_ = v___x_4571_;
goto v___jp_4545_;
}
else
{
lean_dec(v_a_4558_);
v___y_4546_ = v___x_4570_;
goto v___jp_4545_;
}
}
}
}
else
{
lean_dec(v_a_4558_);
v___y_4546_ = v___x_4559_;
goto v___jp_4545_;
}
}
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec(v_a_4544_);
lean_dec_ref(v_alt_4532_);
v_a_4577_ = lean_ctor_get(v___x_4557_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4557_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4557_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
v___jp_4545_:
{
if (lean_obj_tag(v___y_4546_) == 0)
{
lean_object* v___x_4547_; 
lean_dec_ref_known(v___y_4546_, 1);
v___x_4547_ = l_Lean_Meta_mkEqMPR(v_a_4544_, v_alt_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
return v___x_4547_;
}
else
{
lean_object* v_a_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4555_; 
lean_dec(v_a_4544_);
lean_dec_ref(v_alt_4532_);
v_a_4548_ = lean_ctor_get(v___y_4546_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___y_4546_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4550_ = v___y_4546_;
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_a_4548_);
lean_dec(v___y_4546_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4555_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4532_);
return v___x_4543_;
}
}
else
{
lean_dec_ref(v_alt_4532_);
return v___x_4540_;
}
}
else
{
lean_dec_ref(v_alt_4532_);
lean_dec_ref(v_expAltType_4530_);
return v___x_4538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4585_, lean_object* v___altIdx_4586_, lean_object* v_expAltType_4587_, lean_object* v___altFVars_4588_, lean_object* v_alt_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
uint8_t v___x_32524__boxed_4595_; lean_object* v_res_4596_; 
v___x_32524__boxed_4595_ = lean_unbox(v___x_4585_);
v_res_4596_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32524__boxed_4595_, v___altIdx_4586_, v_expAltType_4587_, v___altFVars_4588_, v_alt_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec_ref(v___altFVars_4588_);
lean_dec(v___altIdx_4586_);
return v_res_4596_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4597_, lean_object* v_e_4598_){
_start:
{
uint8_t v___x_4599_; lean_object* v_d_4601_; lean_object* v_b_4602_; 
v___x_4599_ = l_Lean_Expr_hasFVar(v_e_4598_);
if (v___x_4599_ == 0)
{
return v___x_4599_;
}
else
{
switch(lean_obj_tag(v_e_4598_))
{
case 7:
{
lean_object* v_binderType_4605_; lean_object* v_body_4606_; 
v_binderType_4605_ = lean_ctor_get(v_e_4598_, 1);
v_body_4606_ = lean_ctor_get(v_e_4598_, 2);
v_d_4601_ = v_binderType_4605_;
v_b_4602_ = v_body_4606_;
goto v___jp_4600_;
}
case 6:
{
lean_object* v_binderType_4607_; lean_object* v_body_4608_; 
v_binderType_4607_ = lean_ctor_get(v_e_4598_, 1);
v_body_4608_ = lean_ctor_get(v_e_4598_, 2);
v_d_4601_ = v_binderType_4607_;
v_b_4602_ = v_body_4608_;
goto v___jp_4600_;
}
case 10:
{
lean_object* v_expr_4609_; 
v_expr_4609_ = lean_ctor_get(v_e_4598_, 1);
v_e_4598_ = v_expr_4609_;
goto _start;
}
case 8:
{
lean_object* v_type_4611_; lean_object* v_value_4612_; lean_object* v_body_4613_; uint8_t v___x_4614_; 
v_type_4611_ = lean_ctor_get(v_e_4598_, 1);
v_value_4612_ = lean_ctor_get(v_e_4598_, 2);
v_body_4613_ = lean_ctor_get(v_e_4598_, 3);
v___x_4614_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4597_, v_type_4611_);
if (v___x_4614_ == 0)
{
uint8_t v___x_4615_; 
v___x_4615_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4597_, v_value_4612_);
if (v___x_4615_ == 0)
{
v_e_4598_ = v_body_4613_;
goto _start;
}
else
{
return v___x_4599_;
}
}
else
{
return v___x_4599_;
}
}
case 5:
{
lean_object* v_fn_4617_; lean_object* v_arg_4618_; uint8_t v___x_4619_; 
v_fn_4617_ = lean_ctor_get(v_e_4598_, 0);
v_arg_4618_ = lean_ctor_get(v_e_4598_, 1);
v___x_4619_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4597_, v_fn_4617_);
if (v___x_4619_ == 0)
{
v_e_4598_ = v_arg_4618_;
goto _start;
}
else
{
return v___x_4599_;
}
}
case 11:
{
lean_object* v_struct_4621_; 
v_struct_4621_ = lean_ctor_get(v_e_4598_, 2);
v_e_4598_ = v_struct_4621_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4623_; lean_object* v___x_4624_; uint8_t v___x_4625_; 
v_fvarId_4623_ = lean_ctor_get(v_e_4598_, 0);
v___x_4624_ = l_Lean_Expr_fvarId_x21(v___x_4597_);
v___x_4625_ = l_Lean_instBEqFVarId_beq(v_fvarId_4623_, v___x_4624_);
lean_dec(v___x_4624_);
return v___x_4625_;
}
default: 
{
uint8_t v___x_4626_; 
v___x_4626_ = 0;
return v___x_4626_;
}
}
}
v___jp_4600_:
{
uint8_t v___x_4603_; 
v___x_4603_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4597_, v_d_4601_);
if (v___x_4603_ == 0)
{
v_e_4598_ = v_b_4602_;
goto _start;
}
else
{
return v___x_4599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4627_, lean_object* v_e_4628_){
_start:
{
uint8_t v_res_4629_; lean_object* v_r_4630_; 
v_res_4629_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4627_, v_e_4628_);
lean_dec_ref(v_e_4628_);
lean_dec_ref(v___x_4627_);
v_r_4630_ = lean_box(v_res_4629_);
return v_r_4630_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4633_ = l_Lean_stringToMessageData(v___x_4632_);
return v___x_4633_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4636_ = l_Lean_stringToMessageData(v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4639_ = l_Lean_stringToMessageData(v___x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4640_, lean_object* v_termAlt_4641_, lean_object* v_a_4642_, lean_object* v_b_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v_array_4649_; lean_object* v_start_4650_; lean_object* v_stop_4651_; lean_object* v___x_4653_; uint8_t v_isShared_4654_; uint8_t v_isSharedCheck_4679_; 
v_array_4649_ = lean_ctor_get(v_a_4642_, 0);
v_start_4650_ = lean_ctor_get(v_a_4642_, 1);
v_stop_4651_ = lean_ctor_get(v_a_4642_, 2);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_a_4642_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4653_ = v_a_4642_;
v_isShared_4654_ = v_isSharedCheck_4679_;
goto v_resetjp_4652_;
}
else
{
lean_inc(v_stop_4651_);
lean_inc(v_start_4650_);
lean_inc(v_array_4649_);
lean_dec(v_a_4642_);
v___x_4653_ = lean_box(0);
v_isShared_4654_ = v_isSharedCheck_4679_;
goto v_resetjp_4652_;
}
v_resetjp_4652_:
{
uint8_t v___x_4655_; 
v___x_4655_ = lean_nat_dec_lt(v_start_4650_, v_stop_4651_);
if (v___x_4655_ == 0)
{
lean_object* v___x_4656_; 
lean_del_object(v___x_4653_);
lean_dec(v_stop_4651_);
lean_dec(v_start_4650_);
lean_dec_ref(v_array_4649_);
lean_dec_ref(v_termAlt_4641_);
lean_dec_ref(v_a_4640_);
v___x_4656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4656_, 0, v_b_4643_);
return v___x_4656_;
}
else
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4661_; 
v___x_4657_ = lean_box(0);
v___x_4658_ = lean_unsigned_to_nat(1u);
v___x_4659_ = lean_nat_add(v_start_4650_, v___x_4658_);
lean_inc_ref(v_array_4649_);
if (v_isShared_4654_ == 0)
{
lean_ctor_set(v___x_4653_, 1, v___x_4659_);
v___x_4661_ = v___x_4653_;
goto v_reusejp_4660_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_array_4649_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v___x_4659_);
lean_ctor_set(v_reuseFailAlloc_4678_, 2, v_stop_4651_);
v___x_4661_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4660_;
}
v_reusejp_4660_:
{
lean_object* v___x_4662_; uint8_t v___x_4663_; 
v___x_4662_ = lean_array_fget(v_array_4649_, v_start_4650_);
lean_dec(v_start_4650_);
lean_dec_ref(v_array_4649_);
v___x_4663_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4662_, v_a_4640_);
if (v___x_4663_ == 0)
{
lean_dec(v___x_4662_);
v_a_4642_ = v___x_4661_;
v_b_4643_ = v___x_4657_;
goto _start;
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4665_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4640_);
v___x_4666_ = l_Lean_MessageData_ofExpr(v_a_4640_);
v___x_4667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4665_);
lean_ctor_set(v___x_4667_, 1, v___x_4666_);
v___x_4668_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4667_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
lean_inc_ref(v_termAlt_4641_);
v___x_4670_ = l_Lean_MessageData_ofExpr(v_termAlt_4641_);
v___x_4671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4669_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
v___x_4672_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4671_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
v___x_4674_ = l_Lean_MessageData_ofExpr(v___x_4662_);
v___x_4675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4673_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
v___x_4676_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4675_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_dec_ref_known(v___x_4676_, 1);
v_a_4642_ = v___x_4661_;
v_b_4643_ = v___x_4657_;
goto _start;
}
else
{
lean_dec_ref(v___x_4661_);
lean_dec_ref(v_termAlt_4641_);
lean_dec_ref(v_a_4640_);
return v___x_4676_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4680_, lean_object* v_termAlt_4681_, lean_object* v_a_4682_, lean_object* v_b_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4680_, v_termAlt_4681_, v_a_4682_, v_b_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4690_, lean_object* v_v_4691_, uint8_t v___x_4692_, uint8_t v___x_4693_, uint8_t v___x_4694_, lean_object* v_xs_4695_, lean_object* v_termAltBody_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; 
v___x_4702_ = lean_array_get_size(v_xs_4695_);
v___x_4703_ = lean_nat_sub(v___x_4702_, v_nExtra_4690_);
v___x_4704_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4703_);
lean_inc_ref(v_xs_4695_);
v___x_4705_ = l_Array_toSubarray___redArg(v_xs_4695_, v___x_4704_, v___x_4703_);
v___x_4706_ = l_Array_toSubarray___redArg(v_xs_4695_, v___x_4703_, v___x_4702_);
lean_inc(v___y_4700_);
lean_inc_ref(v___y_4699_);
lean_inc(v___y_4698_);
lean_inc_ref(v___y_4697_);
v___x_4707_ = lean_infer_type(v_termAltBody_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc_n(v_a_4708_, 2);
lean_dec_ref_known(v___x_4707_, 1);
v___x_4709_ = lean_box(0);
v___x_4710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4708_, v_v_4691_, v___x_4706_, v___x_4709_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
lean_dec_ref_known(v___x_4710_, 1);
v___x_4711_ = l_Subarray_copy___redArg(v___x_4705_);
v___x_4712_ = l_Lean_Meta_mkLambdaFVars(v___x_4711_, v_a_4708_, v___x_4692_, v___x_4693_, v___x_4692_, v___x_4693_, v___x_4694_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
lean_dec_ref(v___x_4711_);
return v___x_4712_;
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec(v_a_4708_);
lean_dec_ref(v___x_4705_);
v_a_4713_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4710_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4710_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
else
{
lean_dec_ref(v___x_4706_);
lean_dec_ref(v___x_4705_);
lean_dec(v_v_4691_);
return v___x_4707_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4721_, lean_object* v_v_4722_, lean_object* v___x_4723_, lean_object* v___x_4724_, lean_object* v___x_4725_, lean_object* v_xs_4726_, lean_object* v_termAltBody_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_){
_start:
{
uint8_t v___x_32813__boxed_4733_; uint8_t v___x_32814__boxed_4734_; uint8_t v___x_32815__boxed_4735_; lean_object* v_res_4736_; 
v___x_32813__boxed_4733_ = lean_unbox(v___x_4723_);
v___x_32814__boxed_4734_ = lean_unbox(v___x_4724_);
v___x_32815__boxed_4735_ = lean_unbox(v___x_4725_);
v_res_4736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4721_, v_v_4722_, v___x_32813__boxed_4733_, v___x_32814__boxed_4734_, v___x_32815__boxed_4735_, v_xs_4726_, v_termAltBody_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v_nExtra_4721_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4737_, size_t v_sz_4738_, size_t v_i_4739_, lean_object* v_bs_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_){
_start:
{
uint8_t v___x_4746_; 
v___x_4746_ = lean_usize_dec_lt(v_i_4739_, v_sz_4738_);
if (v___x_4746_ == 0)
{
lean_object* v___x_4747_; 
lean_dec(v_nExtra_4737_);
v___x_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4747_, 0, v_bs_4740_);
return v___x_4747_;
}
else
{
uint8_t v___x_4748_; uint8_t v___x_4749_; lean_object* v_v_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___f_4754_; lean_object* v___x_4755_; lean_object* v_bs_x27_4756_; lean_object* v___x_4757_; 
v___x_4748_ = 0;
v___x_4749_ = 1;
v_v_4750_ = lean_array_uget(v_bs_4740_, v_i_4739_);
v___x_4751_ = lean_box(v___x_4748_);
v___x_4752_ = lean_box(v___x_4746_);
v___x_4753_ = lean_box(v___x_4749_);
lean_inc(v_v_4750_);
lean_inc(v_nExtra_4737_);
v___f_4754_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4754_, 0, v_nExtra_4737_);
lean_closure_set(v___f_4754_, 1, v_v_4750_);
lean_closure_set(v___f_4754_, 2, v___x_4751_);
lean_closure_set(v___f_4754_, 3, v___x_4752_);
lean_closure_set(v___f_4754_, 4, v___x_4753_);
v___x_4755_ = lean_unsigned_to_nat(0u);
v_bs_x27_4756_ = lean_array_uset(v_bs_4740_, v_i_4739_, v___x_4755_);
v___x_4757_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4750_, v___f_4754_, v___x_4748_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; size_t v___x_4759_; size_t v___x_4760_; lean_object* v___x_4761_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref_known(v___x_4757_, 1);
v___x_4759_ = ((size_t)1ULL);
v___x_4760_ = lean_usize_add(v_i_4739_, v___x_4759_);
v___x_4761_ = lean_array_uset(v_bs_x27_4756_, v_i_4739_, v_a_4758_);
v_i_4739_ = v___x_4760_;
v_bs_4740_ = v___x_4761_;
goto _start;
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec_ref(v_bs_x27_4756_);
lean_dec(v_nExtra_4737_);
v_a_4763_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4757_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4757_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4771_, lean_object* v_sz_4772_, lean_object* v_i_4773_, lean_object* v_bs_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
size_t v_sz_boxed_4780_; size_t v_i_boxed_4781_; lean_object* v_res_4782_; 
v_sz_boxed_4780_ = lean_unbox_usize(v_sz_4772_);
lean_dec(v_sz_4772_);
v_i_boxed_4781_ = lean_unbox_usize(v_i_4773_);
lean_dec(v_i_4773_);
v_res_4782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4771_, v_sz_boxed_4780_, v_i_boxed_4781_, v_bs_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
return v_res_4782_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4783_ = lean_box(0);
v___x_4784_ = l_Lean_Expr_sort___override(v___x_4783_);
return v___x_4784_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4785_ = lean_box(0);
v___x_4786_ = l_Lean_Level_succ___override(v___x_4785_);
return v___x_4786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4787_, uint8_t v___x_4788_, uint8_t v___x_4789_, lean_object* v_alts_4790_, lean_object* v_toMatcherInfo_4791_, lean_object* v_matcherName_4792_, lean_object* v_params_4793_, lean_object* v_matcherLevels_4794_, lean_object* v_motiveArgs_4795_, lean_object* v_body_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
lean_object* v___x_4802_; 
lean_inc(v_nExtra_4787_);
v___x_4802_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4787_, v_body_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
if (lean_obj_tag(v___x_4802_) == 0)
{
lean_object* v_a_4803_; lean_object* v___x_4804_; uint8_t v___x_4805_; lean_object* v___x_4806_; 
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
lean_inc(v_a_4803_);
lean_dec_ref_known(v___x_4802_, 1);
v___x_4804_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4805_ = 1;
v___x_4806_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4795_, v___x_4804_, v___x_4788_, v___x_4789_, v___x_4788_, v___x_4789_, v___x_4805_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
if (lean_obj_tag(v___x_4806_) == 0)
{
lean_object* v_a_4807_; size_t v_sz_4808_; size_t v___x_4809_; lean_object* v___x_4810_; 
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
lean_inc(v_a_4807_);
lean_dec_ref_known(v___x_4806_, 1);
v_sz_4808_ = lean_array_size(v_alts_4790_);
v___x_4809_ = ((size_t)0ULL);
v___x_4810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4787_, v_sz_4808_, v___x_4809_, v_alts_4790_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v_matcherLevels_4813_; lean_object* v___y_4814_; lean_object* v___y_4815_; lean_object* v_uElimPos_x3f_4820_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
lean_inc(v_a_4811_);
lean_dec_ref_known(v___x_4810_, 1);
v_uElimPos_x3f_4820_ = lean_ctor_get(v_toMatcherInfo_4791_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4820_) == 0)
{
v_matcherLevels_4813_ = v_matcherLevels_4794_;
v___y_4814_ = v___y_4799_;
v___y_4815_ = v___y_4800_;
goto v___jp_4812_;
}
else
{
lean_object* v_val_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v_val_4821_ = lean_ctor_get(v_uElimPos_x3f_4820_, 0);
v___x_4822_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4823_ = lean_array_set(v_matcherLevels_4794_, v_val_4821_, v___x_4822_);
v_matcherLevels_4813_ = v___x_4823_;
v___y_4814_ = v___y_4799_;
v___y_4815_ = v___y_4800_;
goto v___jp_4812_;
}
v___jp_4812_:
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
v___x_4816_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4817_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4817_, 0, v_toMatcherInfo_4791_);
lean_ctor_set(v___x_4817_, 1, v_matcherName_4792_);
lean_ctor_set(v___x_4817_, 2, v_matcherLevels_4813_);
lean_ctor_set(v___x_4817_, 3, v_params_4793_);
lean_ctor_set(v___x_4817_, 4, v_a_4807_);
lean_ctor_set(v___x_4817_, 5, v_motiveArgs_4795_);
lean_ctor_set(v___x_4817_, 6, v_a_4811_);
lean_ctor_set(v___x_4817_, 7, v___x_4816_);
v___x_4818_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4817_);
v___x_4819_ = l_Lean_mkArrowN(v_a_4803_, v___x_4818_, v___y_4814_, v___y_4815_);
lean_dec(v_a_4803_);
return v___x_4819_;
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
lean_dec(v_a_4807_);
lean_dec(v_a_4803_);
lean_dec_ref(v_motiveArgs_4795_);
lean_dec_ref(v_matcherLevels_4794_);
lean_dec_ref(v_params_4793_);
lean_dec(v_matcherName_4792_);
lean_dec_ref(v_toMatcherInfo_4791_);
v_a_4824_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4810_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4810_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
else
{
lean_dec(v_a_4803_);
lean_dec_ref(v_motiveArgs_4795_);
lean_dec_ref(v_matcherLevels_4794_);
lean_dec_ref(v_params_4793_);
lean_dec(v_matcherName_4792_);
lean_dec_ref(v_toMatcherInfo_4791_);
lean_dec_ref(v_alts_4790_);
lean_dec(v_nExtra_4787_);
return v___x_4806_;
}
}
else
{
lean_object* v_a_4832_; lean_object* v___x_4834_; uint8_t v_isShared_4835_; uint8_t v_isSharedCheck_4839_; 
lean_dec_ref(v_motiveArgs_4795_);
lean_dec_ref(v_matcherLevels_4794_);
lean_dec_ref(v_params_4793_);
lean_dec(v_matcherName_4792_);
lean_dec_ref(v_toMatcherInfo_4791_);
lean_dec_ref(v_alts_4790_);
lean_dec(v_nExtra_4787_);
v_a_4832_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4839_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4839_ == 0)
{
v___x_4834_ = v___x_4802_;
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
else
{
lean_inc(v_a_4832_);
lean_dec(v___x_4802_);
v___x_4834_ = lean_box(0);
v_isShared_4835_ = v_isSharedCheck_4839_;
goto v_resetjp_4833_;
}
v_resetjp_4833_:
{
lean_object* v___x_4837_; 
if (v_isShared_4835_ == 0)
{
v___x_4837_ = v___x_4834_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4838_; 
v_reuseFailAlloc_4838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_a_4832_);
v___x_4837_ = v_reuseFailAlloc_4838_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
return v___x_4837_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4840_, lean_object* v___x_4841_, lean_object* v___x_4842_, lean_object* v_alts_4843_, lean_object* v_toMatcherInfo_4844_, lean_object* v_matcherName_4845_, lean_object* v_params_4846_, lean_object* v_matcherLevels_4847_, lean_object* v_motiveArgs_4848_, lean_object* v_body_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
uint8_t v___x_32948__boxed_4855_; uint8_t v___x_32949__boxed_4856_; lean_object* v_res_4857_; 
v___x_32948__boxed_4855_ = lean_unbox(v___x_4841_);
v___x_32949__boxed_4856_ = lean_unbox(v___x_4842_);
v_res_4857_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4840_, v___x_32948__boxed_4855_, v___x_32949__boxed_4856_, v_alts_4843_, v_toMatcherInfo_4844_, v_matcherName_4845_, v_params_4846_, v_matcherLevels_4847_, v_motiveArgs_4848_, v_body_4849_, v___y_4850_, v___y_4851_, v___y_4852_, v___y_4853_);
lean_dec(v___y_4853_);
lean_dec_ref(v___y_4852_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
return v_res_4857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4858_, lean_object* v_ys_4859_, lean_object* v_args_4860_, lean_object* v___mask_4861_, lean_object* v___bodyType_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v___x_4868_; 
lean_inc(v___y_4866_);
lean_inc_ref(v___y_4865_);
lean_inc(v___y_4864_);
lean_inc_ref(v___y_4863_);
v___x_4868_ = lean_apply_7(v_k_4858_, v_ys_4859_, v_args_4860_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, lean_box(0));
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4869_, lean_object* v_ys_4870_, lean_object* v_args_4871_, lean_object* v___mask_4872_, lean_object* v___bodyType_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_, lean_object* v___y_4878_){
_start:
{
lean_object* v_res_4879_; 
v_res_4879_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4869_, v_ys_4870_, v_args_4871_, v___mask_4872_, v___bodyType_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
lean_dec(v___y_4877_);
lean_dec_ref(v___y_4876_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec_ref(v___bodyType_4873_);
lean_dec_ref(v___mask_4872_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4880_, lean_object* v_altInfo_4881_, lean_object* v_k_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v___f_4888_; lean_object* v___x_4889_; 
v___f_4888_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4888_, 0, v_k_4882_);
v___x_4889_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4880_, v_altInfo_4881_, v___f_4888_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4897_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4892_ = v___x_4889_;
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
if (v_isShared_4893_ == 0)
{
v___x_4895_ = v___x_4892_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4890_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
else
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
v_a_4898_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4889_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4889_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
return v___x_4903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4906_, lean_object* v_altInfo_4907_, lean_object* v_k_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4906_, v_altInfo_4907_, v_k_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4915_, lean_object* v___x_4916_, lean_object* v___f_4917_, lean_object* v_fst_4918_, lean_object* v___x_4919_, lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v___x_4922_, lean_object* v___x_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_){
_start:
{
lean_object* v___x_4929_; 
v___x_4929_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4915_, v___x_4916_, v___f_4917_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v_a_4930_; lean_object* v___x_4932_; uint8_t v_isShared_4933_; uint8_t v_isSharedCheck_4944_; 
v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4932_ = v___x_4929_;
v_isShared_4933_ = v_isSharedCheck_4944_;
goto v_resetjp_4931_;
}
else
{
lean_inc(v_a_4930_);
lean_dec(v___x_4929_);
v___x_4932_ = lean_box(0);
v_isShared_4933_ = v_isSharedCheck_4944_;
goto v_resetjp_4931_;
}
v_resetjp_4931_:
{
lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4942_; 
v___x_4934_ = lean_array_push(v_fst_4918_, v_a_4930_);
v___x_4935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4919_);
lean_ctor_set(v___x_4935_, 1, v___x_4920_);
v___x_4936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4921_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4922_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4923_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4939_, 0, v___x_4934_);
lean_ctor_set(v___x_4939_, 1, v___x_4938_);
v___x_4940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4940_, 0, v___x_4939_);
if (v_isShared_4933_ == 0)
{
lean_ctor_set(v___x_4932_, 0, v___x_4940_);
v___x_4942_ = v___x_4932_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v___x_4940_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
else
{
lean_object* v_a_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4952_; 
lean_dec_ref(v___x_4923_);
lean_dec_ref(v___x_4922_);
lean_dec_ref(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec_ref(v___x_4919_);
lean_dec(v_fst_4918_);
v_a_4945_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4952_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4952_ == 0)
{
v___x_4947_ = v___x_4929_;
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_a_4945_);
lean_dec(v___x_4929_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4952_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4950_; 
if (v_isShared_4948_ == 0)
{
v___x_4950_ = v___x_4947_;
goto v_reusejp_4949_;
}
else
{
lean_object* v_reuseFailAlloc_4951_; 
v_reuseFailAlloc_4951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4951_, 0, v_a_4945_);
v___x_4950_ = v_reuseFailAlloc_4951_;
goto v_reusejp_4949_;
}
v_reusejp_4949_:
{
return v___x_4950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4953_, lean_object* v___x_4954_, lean_object* v___f_4955_, lean_object* v_fst_4956_, lean_object* v___x_4957_, lean_object* v___x_4958_, lean_object* v___x_4959_, lean_object* v___x_4960_, lean_object* v___x_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4953_, v___x_4954_, v___f_4955_, v_fst_4956_, v___x_4957_, v___x_4958_, v___x_4959_, v___x_4960_, v___x_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_4968_, lean_object* v_ys_4969_, lean_object* v_ys2_4970_, lean_object* v_ys3_4971_, lean_object* v_onAlt_4972_, lean_object* v_a_4973_, uint8_t v___x_4974_, uint8_t v_useSplitter_4975_, lean_object* v___x_4976_, lean_object* v_ys4_4977_, lean_object* v_altType_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v___y_4985_; lean_object* v___x_4995_; lean_object* v___x_4996_; 
lean_inc_ref(v_args_4968_);
v___x_4995_ = l_Array_append___redArg(v_args_4968_, v_ys3_4971_);
v___x_4996_ = l_Lean_Meta_instantiateLambda(v___x_4976_, v___x_4995_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
lean_dec_ref(v___x_4995_);
if (lean_obj_tag(v___x_4996_) == 0)
{
v___y_4985_ = v___x_4996_;
goto v___jp_4984_;
}
else
{
lean_object* v_a_4997_; uint8_t v___y_4999_; uint8_t v___x_5002_; 
v_a_4997_ = lean_ctor_get(v___x_4996_, 0);
v___x_5002_ = l_Lean_Exception_isInterrupt(v_a_4997_);
if (v___x_5002_ == 0)
{
uint8_t v___x_5003_; 
lean_inc(v_a_4997_);
v___x_5003_ = l_Lean_Exception_isRuntime(v_a_4997_);
v___y_4999_ = v___x_5003_;
goto v___jp_4998_;
}
else
{
v___y_4999_ = v___x_5002_;
goto v___jp_4998_;
}
v___jp_4998_:
{
if (v___y_4999_ == 0)
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
lean_dec_ref_known(v___x_4996_, 1);
v___x_5000_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_5001_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5000_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
v___y_4985_ = v___x_5001_;
goto v___jp_4984_;
}
else
{
v___y_4985_ = v___x_4996_;
goto v___jp_4984_;
}
}
}
v___jp_4984_:
{
if (lean_obj_tag(v___y_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; 
v_a_4986_ = lean_ctor_get(v___y_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___y_4985_, 1);
lean_inc_ref(v_ys4_4977_);
lean_inc_ref(v_ys3_4971_);
lean_inc_ref(v_ys2_4970_);
lean_inc_ref(v_ys_4969_);
v___x_4987_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4987_, 0, v_args_4968_);
lean_ctor_set(v___x_4987_, 1, v_ys_4969_);
lean_ctor_set(v___x_4987_, 2, v_ys2_4970_);
lean_ctor_set(v___x_4987_, 3, v_ys3_4971_);
lean_ctor_set(v___x_4987_, 4, v_ys4_4977_);
lean_inc(v___y_4982_);
lean_inc_ref(v___y_4981_);
lean_inc(v___y_4980_);
lean_inc_ref(v___y_4979_);
v___x_4988_ = lean_apply_9(v_onAlt_4972_, v_a_4973_, v_altType_4978_, v___x_4987_, v_a_4986_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, lean_box(0));
if (lean_obj_tag(v___x_4988_) == 0)
{
lean_object* v_a_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; uint8_t v___x_4993_; lean_object* v___x_4994_; 
v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
lean_inc(v_a_4989_);
lean_dec_ref_known(v___x_4988_, 1);
v___x_4990_ = l_Array_append___redArg(v_ys_4969_, v_ys2_4970_);
lean_dec_ref(v_ys2_4970_);
v___x_4991_ = l_Array_append___redArg(v___x_4990_, v_ys3_4971_);
lean_dec_ref(v_ys3_4971_);
v___x_4992_ = l_Array_append___redArg(v___x_4991_, v_ys4_4977_);
lean_dec_ref(v_ys4_4977_);
v___x_4993_ = 1;
v___x_4994_ = l_Lean_Meta_mkLambdaFVars(v___x_4992_, v_a_4989_, v___x_4974_, v_useSplitter_4975_, v___x_4974_, v_useSplitter_4975_, v___x_4993_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_);
lean_dec_ref(v___x_4992_);
return v___x_4994_;
}
else
{
lean_dec_ref(v_ys4_4977_);
lean_dec_ref(v_ys3_4971_);
lean_dec_ref(v_ys2_4970_);
lean_dec_ref(v_ys_4969_);
return v___x_4988_;
}
}
else
{
lean_dec_ref(v_altType_4978_);
lean_dec_ref(v_ys4_4977_);
lean_dec(v_a_4973_);
lean_dec_ref(v_onAlt_4972_);
lean_dec_ref(v_ys3_4971_);
lean_dec_ref(v_ys2_4970_);
lean_dec_ref(v_ys_4969_);
lean_dec_ref(v_args_4968_);
return v___y_4985_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5004_, lean_object* v_ys_5005_, lean_object* v_ys2_5006_, lean_object* v_ys3_5007_, lean_object* v_onAlt_5008_, lean_object* v_a_5009_, lean_object* v___x_5010_, lean_object* v_useSplitter_5011_, lean_object* v___x_5012_, lean_object* v_ys4_5013_, lean_object* v_altType_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_){
_start:
{
uint8_t v___x_33202__boxed_5020_; uint8_t v_useSplitter_boxed_5021_; lean_object* v_res_5022_; 
v___x_33202__boxed_5020_ = lean_unbox(v___x_5010_);
v_useSplitter_boxed_5021_ = lean_unbox(v_useSplitter_5011_);
v_res_5022_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5004_, v_ys_5005_, v_ys2_5006_, v_ys3_5007_, v_onAlt_5008_, v_a_5009_, v___x_33202__boxed_5020_, v_useSplitter_boxed_5021_, v___x_5012_, v_ys4_5013_, v_altType_5014_, v___y_5015_, v___y_5016_, v___y_5017_, v___y_5018_);
lean_dec(v___y_5018_);
lean_dec_ref(v___y_5017_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
return v_res_5022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5023_, lean_object* v_ys_5024_, lean_object* v_ys2_5025_, lean_object* v_onAlt_5026_, lean_object* v_a_5027_, uint8_t v___x_5028_, uint8_t v_useSplitter_5029_, lean_object* v___x_5030_, lean_object* v_extraEqualities_5031_, lean_object* v_ys3_5032_, lean_object* v_altType_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_, lean_object* v___y_5037_){
_start:
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___f_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; 
v___x_5039_ = lean_box(v___x_5028_);
v___x_5040_ = lean_box(v_useSplitter_5029_);
v___f_5041_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5041_, 0, v_args_5023_);
lean_closure_set(v___f_5041_, 1, v_ys_5024_);
lean_closure_set(v___f_5041_, 2, v_ys2_5025_);
lean_closure_set(v___f_5041_, 3, v_ys3_5032_);
lean_closure_set(v___f_5041_, 4, v_onAlt_5026_);
lean_closure_set(v___f_5041_, 5, v_a_5027_);
lean_closure_set(v___f_5041_, 6, v___x_5039_);
lean_closure_set(v___f_5041_, 7, v___x_5040_);
lean_closure_set(v___f_5041_, 8, v___x_5030_);
v___x_5042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5042_, 0, v_extraEqualities_5031_);
v___x_5043_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5033_, v___x_5042_, v___f_5041_, v___x_5028_, v___x_5028_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_);
return v___x_5043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5044_, lean_object* v_ys_5045_, lean_object* v_ys2_5046_, lean_object* v_onAlt_5047_, lean_object* v_a_5048_, lean_object* v___x_5049_, lean_object* v_useSplitter_5050_, lean_object* v___x_5051_, lean_object* v_extraEqualities_5052_, lean_object* v_ys3_5053_, lean_object* v_altType_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
uint8_t v___x_33267__boxed_5060_; uint8_t v_useSplitter_boxed_5061_; lean_object* v_res_5062_; 
v___x_33267__boxed_5060_ = lean_unbox(v___x_5049_);
v_useSplitter_boxed_5061_ = lean_unbox(v_useSplitter_5050_);
v_res_5062_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5044_, v_ys_5045_, v_ys2_5046_, v_onAlt_5047_, v_a_5048_, v___x_33267__boxed_5060_, v_useSplitter_boxed_5061_, v___x_5051_, v_extraEqualities_5052_, v_ys3_5053_, v_altType_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5063_, lean_object* v_ys_5064_, lean_object* v_onAlt_5065_, lean_object* v_a_5066_, uint8_t v___x_5067_, uint8_t v_useSplitter_5068_, lean_object* v___x_5069_, lean_object* v_extraEqualities_5070_, lean_object* v_numDiscrEqs_5071_, lean_object* v_ys2_5072_, lean_object* v_altType_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_){
_start:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___f_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
v___x_5079_ = lean_box(v___x_5067_);
v___x_5080_ = lean_box(v_useSplitter_5068_);
v___f_5081_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5081_, 0, v_args_5063_);
lean_closure_set(v___f_5081_, 1, v_ys_5064_);
lean_closure_set(v___f_5081_, 2, v_ys2_5072_);
lean_closure_set(v___f_5081_, 3, v_onAlt_5065_);
lean_closure_set(v___f_5081_, 4, v_a_5066_);
lean_closure_set(v___f_5081_, 5, v___x_5079_);
lean_closure_set(v___f_5081_, 6, v___x_5080_);
lean_closure_set(v___f_5081_, 7, v___x_5069_);
lean_closure_set(v___f_5081_, 8, v_extraEqualities_5070_);
v___x_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5082_, 0, v_numDiscrEqs_5071_);
v___x_5083_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5073_, v___x_5082_, v___f_5081_, v___x_5067_, v___x_5067_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5084_, lean_object* v_ys_5085_, lean_object* v_onAlt_5086_, lean_object* v_a_5087_, lean_object* v___x_5088_, lean_object* v_useSplitter_5089_, lean_object* v___x_5090_, lean_object* v_extraEqualities_5091_, lean_object* v_numDiscrEqs_5092_, lean_object* v_ys2_5093_, lean_object* v_altType_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_){
_start:
{
uint8_t v___x_33298__boxed_5100_; uint8_t v_useSplitter_boxed_5101_; lean_object* v_res_5102_; 
v___x_33298__boxed_5100_ = lean_unbox(v___x_5088_);
v_useSplitter_boxed_5101_ = lean_unbox(v_useSplitter_5089_);
v_res_5102_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5084_, v_ys_5085_, v_onAlt_5086_, v_a_5087_, v___x_33298__boxed_5100_, v_useSplitter_boxed_5101_, v___x_5090_, v_extraEqualities_5091_, v_numDiscrEqs_5092_, v_ys2_5093_, v_altType_5094_, v___y_5095_, v___y_5096_, v___y_5097_, v___y_5098_);
lean_dec(v___y_5098_);
lean_dec_ref(v___y_5097_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
return v_res_5102_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0(void){
_start:
{
lean_object* v___x_5103_; 
v___x_5103_ = l_instMonadEIO___redArg();
return v___x_5103_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v_toApplicative_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5177_; 
v___x_5114_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5115_ = l_StateRefT_x27_instMonad___redArg(v___x_5114_);
v_toApplicative_5116_ = lean_ctor_get(v___x_5115_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5115_);
if (v_isSharedCheck_5177_ == 0)
{
lean_object* v_unused_5178_; 
v_unused_5178_ = lean_ctor_get(v___x_5115_, 1);
lean_dec(v_unused_5178_);
v___x_5118_ = v___x_5115_;
v_isShared_5119_ = v_isSharedCheck_5177_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_toApplicative_5116_);
lean_dec(v___x_5115_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5177_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v_toFunctor_5120_; lean_object* v_toSeq_5121_; lean_object* v_toSeqLeft_5122_; lean_object* v_toSeqRight_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5175_; 
v_toFunctor_5120_ = lean_ctor_get(v_toApplicative_5116_, 0);
v_toSeq_5121_ = lean_ctor_get(v_toApplicative_5116_, 2);
v_toSeqLeft_5122_ = lean_ctor_get(v_toApplicative_5116_, 3);
v_toSeqRight_5123_ = lean_ctor_get(v_toApplicative_5116_, 4);
v_isSharedCheck_5175_ = !lean_is_exclusive(v_toApplicative_5116_);
if (v_isSharedCheck_5175_ == 0)
{
lean_object* v_unused_5176_; 
v_unused_5176_ = lean_ctor_get(v_toApplicative_5116_, 1);
lean_dec(v_unused_5176_);
v___x_5125_ = v_toApplicative_5116_;
v_isShared_5126_ = v_isSharedCheck_5175_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_toSeqRight_5123_);
lean_inc(v_toSeqLeft_5122_);
lean_inc(v_toSeq_5121_);
lean_inc(v_toFunctor_5120_);
lean_dec(v_toApplicative_5116_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5175_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v___f_5127_; lean_object* v___f_5128_; lean_object* v___f_5129_; lean_object* v___f_5130_; lean_object* v___x_5131_; lean_object* v___f_5132_; lean_object* v___f_5133_; lean_object* v___f_5134_; lean_object* v___x_5136_; 
v___f_5127_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5128_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5120_);
v___f_5129_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5129_, 0, v_toFunctor_5120_);
v___f_5130_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5130_, 0, v_toFunctor_5120_);
v___x_5131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5131_, 0, v___f_5129_);
lean_ctor_set(v___x_5131_, 1, v___f_5130_);
v___f_5132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5132_, 0, v_toSeqRight_5123_);
v___f_5133_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5133_, 0, v_toSeqLeft_5122_);
v___f_5134_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5134_, 0, v_toSeq_5121_);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 4, v___f_5132_);
lean_ctor_set(v___x_5125_, 3, v___f_5133_);
lean_ctor_set(v___x_5125_, 2, v___f_5134_);
lean_ctor_set(v___x_5125_, 1, v___f_5127_);
lean_ctor_set(v___x_5125_, 0, v___x_5131_);
v___x_5136_ = v___x_5125_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5131_);
lean_ctor_set(v_reuseFailAlloc_5174_, 1, v___f_5127_);
lean_ctor_set(v_reuseFailAlloc_5174_, 2, v___f_5134_);
lean_ctor_set(v_reuseFailAlloc_5174_, 3, v___f_5133_);
lean_ctor_set(v_reuseFailAlloc_5174_, 4, v___f_5132_);
v___x_5136_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
lean_object* v___x_5138_; 
if (v_isShared_5119_ == 0)
{
lean_ctor_set(v___x_5118_, 1, v___f_5128_);
lean_ctor_set(v___x_5118_, 0, v___x_5136_);
v___x_5138_ = v___x_5118_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v___x_5136_);
lean_ctor_set(v_reuseFailAlloc_5173_, 1, v___f_5128_);
v___x_5138_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
lean_object* v___x_5139_; lean_object* v_toApplicative_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5171_; 
v___x_5139_ = l_StateRefT_x27_instMonad___redArg(v___x_5138_);
v_toApplicative_5140_ = lean_ctor_get(v___x_5139_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5139_);
if (v_isSharedCheck_5171_ == 0)
{
lean_object* v_unused_5172_; 
v_unused_5172_ = lean_ctor_get(v___x_5139_, 1);
lean_dec(v_unused_5172_);
v___x_5142_ = v___x_5139_;
v_isShared_5143_ = v_isSharedCheck_5171_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_toApplicative_5140_);
lean_dec(v___x_5139_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5171_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v_toFunctor_5144_; lean_object* v_toSeq_5145_; lean_object* v_toSeqLeft_5146_; lean_object* v_toSeqRight_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5169_; 
v_toFunctor_5144_ = lean_ctor_get(v_toApplicative_5140_, 0);
v_toSeq_5145_ = lean_ctor_get(v_toApplicative_5140_, 2);
v_toSeqLeft_5146_ = lean_ctor_get(v_toApplicative_5140_, 3);
v_toSeqRight_5147_ = lean_ctor_get(v_toApplicative_5140_, 4);
v_isSharedCheck_5169_ = !lean_is_exclusive(v_toApplicative_5140_);
if (v_isSharedCheck_5169_ == 0)
{
lean_object* v_unused_5170_; 
v_unused_5170_ = lean_ctor_get(v_toApplicative_5140_, 1);
lean_dec(v_unused_5170_);
v___x_5149_ = v_toApplicative_5140_;
v_isShared_5150_ = v_isSharedCheck_5169_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_toSeqRight_5147_);
lean_inc(v_toSeqLeft_5146_);
lean_inc(v_toSeq_5145_);
lean_inc(v_toFunctor_5144_);
lean_dec(v_toApplicative_5140_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5169_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v___f_5151_; lean_object* v___f_5152_; lean_object* v___f_5153_; lean_object* v___f_5154_; lean_object* v___x_5155_; lean_object* v___f_5156_; lean_object* v___f_5157_; lean_object* v___f_5158_; lean_object* v___x_5160_; 
v___f_5151_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5152_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5144_);
v___f_5153_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5153_, 0, v_toFunctor_5144_);
v___f_5154_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5154_, 0, v_toFunctor_5144_);
v___x_5155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5155_, 0, v___f_5153_);
lean_ctor_set(v___x_5155_, 1, v___f_5154_);
v___f_5156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5156_, 0, v_toSeqRight_5147_);
v___f_5157_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5157_, 0, v_toSeqLeft_5146_);
v___f_5158_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5158_, 0, v_toSeq_5145_);
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 4, v___f_5156_);
lean_ctor_set(v___x_5149_, 3, v___f_5157_);
lean_ctor_set(v___x_5149_, 2, v___f_5158_);
lean_ctor_set(v___x_5149_, 1, v___f_5151_);
lean_ctor_set(v___x_5149_, 0, v___x_5155_);
v___x_5160_ = v___x_5149_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5168_; 
v_reuseFailAlloc_5168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5168_, 0, v___x_5155_);
lean_ctor_set(v_reuseFailAlloc_5168_, 1, v___f_5151_);
lean_ctor_set(v_reuseFailAlloc_5168_, 2, v___f_5158_);
lean_ctor_set(v_reuseFailAlloc_5168_, 3, v___f_5157_);
lean_ctor_set(v_reuseFailAlloc_5168_, 4, v___f_5156_);
v___x_5160_ = v_reuseFailAlloc_5168_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
lean_object* v___x_5162_; 
if (v_isShared_5143_ == 0)
{
lean_ctor_set(v___x_5142_, 1, v___f_5152_);
lean_ctor_set(v___x_5142_, 0, v___x_5160_);
v___x_5162_ = v___x_5142_;
goto v_reusejp_5161_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5160_);
lean_ctor_set(v_reuseFailAlloc_5167_, 1, v___f_5152_);
v___x_5162_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5161_;
}
v_reusejp_5161_:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_27317__overap_5165_; lean_object* v___x_5166_; 
v___x_5163_ = l_Lean_instInhabitedExpr;
v___x_5164_ = l_instInhabitedOfMonad___redArg(v___x_5162_, v___x_5163_);
v___x_27317__overap_5165_ = lean_panic_fn_borrowed(v___x_5164_, v_msg_5108_);
lean_dec(v___x_5164_);
lean_inc(v___y_5112_);
lean_inc_ref(v___y_5111_);
lean_inc(v___y_5110_);
lean_inc_ref(v___y_5109_);
v___x_5166_ = lean_apply_5(v___x_27317__overap_5165_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_, lean_box(0));
return v___x_5166_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_, lean_object* v___y_5184_){
_start:
{
lean_object* v_res_5185_; 
v_res_5185_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
lean_dec(v___y_5183_);
lean_dec_ref(v___y_5182_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
return v_res_5185_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5186_, lean_object* v_onAlt_5187_, lean_object* v_a_5188_, uint8_t v___x_5189_, uint8_t v_useSplitter_5190_, lean_object* v___x_5191_, lean_object* v_extraEqualities_5192_, lean_object* v_numDiscrEqs_5193_, lean_object* v___x_5194_, lean_object* v___x_5195_, lean_object* v___x_5196_, lean_object* v_ys_5197_, lean_object* v_args_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_, lean_object* v___y_5201_, lean_object* v___y_5202_){
_start:
{
lean_object* v_numFields_5204_; lean_object* v_numOverlaps_5205_; uint8_t v_hasUnitThunk_5206_; lean_object* v___x_5207_; uint8_t v___x_5208_; 
v_numFields_5204_ = lean_ctor_get(v___x_5186_, 0);
v_numOverlaps_5205_ = lean_ctor_get(v___x_5186_, 1);
v_hasUnitThunk_5206_ = lean_ctor_get_uint8(v___x_5186_, sizeof(void*)*2);
v___x_5207_ = lean_array_get_size(v_ys_5197_);
v___x_5208_ = lean_nat_dec_eq(v___x_5207_, v_numFields_5204_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; lean_object* v___x_5210_; 
lean_dec_ref(v_args_5198_);
lean_dec_ref(v_ys_5197_);
lean_dec_ref(v___x_5194_);
lean_dec(v_numDiscrEqs_5193_);
lean_dec(v_extraEqualities_5192_);
lean_dec_ref(v___x_5191_);
lean_dec(v_a_5188_);
lean_dec_ref(v_onAlt_5187_);
v___x_5209_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5210_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v___x_5209_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
return v___x_5210_;
}
else
{
lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___f_5213_; lean_object* v_altType_5215_; lean_object* v___y_5216_; lean_object* v___y_5217_; lean_object* v___y_5218_; lean_object* v___y_5219_; lean_object* v___x_5229_; 
v___x_5211_ = lean_box(v___x_5189_);
v___x_5212_ = lean_box(v_useSplitter_5190_);
lean_inc_ref(v_ys_5197_);
v___f_5213_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5213_, 0, v_args_5198_);
lean_closure_set(v___f_5213_, 1, v_ys_5197_);
lean_closure_set(v___f_5213_, 2, v_onAlt_5187_);
lean_closure_set(v___f_5213_, 3, v_a_5188_);
lean_closure_set(v___f_5213_, 4, v___x_5211_);
lean_closure_set(v___f_5213_, 5, v___x_5212_);
lean_closure_set(v___f_5213_, 6, v___x_5191_);
lean_closure_set(v___f_5213_, 7, v_extraEqualities_5192_);
lean_closure_set(v___f_5213_, 8, v_numDiscrEqs_5193_);
v___x_5229_ = l_Lean_Meta_instantiateForall(v___x_5194_, v_ys_5197_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
lean_dec_ref(v_ys_5197_);
if (lean_obj_tag(v___x_5229_) == 0)
{
uint8_t v_hasUnitThunk_5230_; 
v_hasUnitThunk_5230_ = lean_ctor_get_uint8(v___x_5195_, sizeof(void*)*2);
if (v_hasUnitThunk_5230_ == 0)
{
lean_object* v_a_5231_; 
v_a_5231_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5231_);
lean_dec_ref_known(v___x_5229_, 1);
v_altType_5215_ = v_a_5231_;
v___y_5216_ = v___y_5199_;
v___y_5217_ = v___y_5200_;
v___y_5218_ = v___y_5201_;
v___y_5219_ = v___y_5202_;
goto v___jp_5214_;
}
else
{
lean_object* v_a_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v_a_5232_ = lean_ctor_get(v___x_5229_, 0);
lean_inc(v_a_5232_);
lean_dec_ref_known(v___x_5229_, 1);
v___x_5233_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5234_ = lean_mk_empty_array_with_capacity(v___x_5196_);
v___x_5235_ = lean_array_push(v___x_5234_, v___x_5233_);
v___x_5236_ = l_Lean_Meta_instantiateForall(v_a_5232_, v___x_5235_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
lean_dec_ref(v___x_5235_);
if (lean_obj_tag(v___x_5236_) == 0)
{
lean_object* v_a_5237_; 
v_a_5237_ = lean_ctor_get(v___x_5236_, 0);
lean_inc(v_a_5237_);
lean_dec_ref_known(v___x_5236_, 1);
v_altType_5215_ = v_a_5237_;
v___y_5216_ = v___y_5199_;
v___y_5217_ = v___y_5200_;
v___y_5218_ = v___y_5201_;
v___y_5219_ = v___y_5202_;
goto v___jp_5214_;
}
else
{
lean_dec_ref(v___f_5213_);
return v___x_5236_;
}
}
}
else
{
lean_dec_ref(v___f_5213_);
return v___x_5229_;
}
v___jp_5214_:
{
lean_object* v___x_5220_; lean_object* v___x_5221_; 
lean_inc(v_numOverlaps_5205_);
v___x_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5220_, 0, v_numOverlaps_5205_);
v___x_5221_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5215_, v___x_5220_, v___f_5213_, v___x_5189_, v___x_5189_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
if (lean_obj_tag(v___x_5221_) == 0)
{
if (v_hasUnitThunk_5206_ == 0)
{
return v___x_5221_;
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; 
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
lean_inc(v_a_5222_);
lean_dec_ref_known(v___x_5221_, 1);
v___x_5223_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5224_ = lean_unsigned_to_nat(2u);
v___x_5225_ = lean_mk_empty_array_with_capacity(v___x_5224_);
lean_dec_ref(v___x_5225_);
v___x_5226_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5227_ = lean_array_push(v___x_5226_, v_a_5222_);
v___x_5228_ = l_Lean_Meta_mkAppM(v___x_5223_, v___x_5227_, v___y_5216_, v___y_5217_, v___y_5218_, v___y_5219_);
return v___x_5228_;
}
}
else
{
return v___x_5221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5238_ = _args[0];
lean_object* v_onAlt_5239_ = _args[1];
lean_object* v_a_5240_ = _args[2];
lean_object* v___x_5241_ = _args[3];
lean_object* v_useSplitter_5242_ = _args[4];
lean_object* v___x_5243_ = _args[5];
lean_object* v_extraEqualities_5244_ = _args[6];
lean_object* v_numDiscrEqs_5245_ = _args[7];
lean_object* v___x_5246_ = _args[8];
lean_object* v___x_5247_ = _args[9];
lean_object* v___x_5248_ = _args[10];
lean_object* v_ys_5249_ = _args[11];
lean_object* v_args_5250_ = _args[12];
lean_object* v___y_5251_ = _args[13];
lean_object* v___y_5252_ = _args[14];
lean_object* v___y_5253_ = _args[15];
lean_object* v___y_5254_ = _args[16];
lean_object* v___y_5255_ = _args[17];
_start:
{
uint8_t v___x_33500__boxed_5256_; uint8_t v_useSplitter_boxed_5257_; lean_object* v_res_5258_; 
v___x_33500__boxed_5256_ = lean_unbox(v___x_5241_);
v_useSplitter_boxed_5257_ = lean_unbox(v_useSplitter_5242_);
v_res_5258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5238_, v_onAlt_5239_, v_a_5240_, v___x_33500__boxed_5256_, v_useSplitter_boxed_5257_, v___x_5243_, v_extraEqualities_5244_, v_numDiscrEqs_5245_, v___x_5246_, v___x_5247_, v___x_5248_, v_ys_5249_, v_args_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___x_5248_);
lean_dec_ref(v___x_5247_);
lean_dec_ref(v___x_5238_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_){
_start:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v_toApplicative_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5328_; 
v___x_5265_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5266_ = l_StateRefT_x27_instMonad___redArg(v___x_5265_);
v_toApplicative_5267_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5328_ == 0)
{
lean_object* v_unused_5329_; 
v_unused_5329_ = lean_ctor_get(v___x_5266_, 1);
lean_dec(v_unused_5329_);
v___x_5269_ = v___x_5266_;
v_isShared_5270_ = v_isSharedCheck_5328_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_toApplicative_5267_);
lean_dec(v___x_5266_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5328_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v_toFunctor_5271_; lean_object* v_toSeq_5272_; lean_object* v_toSeqLeft_5273_; lean_object* v_toSeqRight_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5326_; 
v_toFunctor_5271_ = lean_ctor_get(v_toApplicative_5267_, 0);
v_toSeq_5272_ = lean_ctor_get(v_toApplicative_5267_, 2);
v_toSeqLeft_5273_ = lean_ctor_get(v_toApplicative_5267_, 3);
v_toSeqRight_5274_ = lean_ctor_get(v_toApplicative_5267_, 4);
v_isSharedCheck_5326_ = !lean_is_exclusive(v_toApplicative_5267_);
if (v_isSharedCheck_5326_ == 0)
{
lean_object* v_unused_5327_; 
v_unused_5327_ = lean_ctor_get(v_toApplicative_5267_, 1);
lean_dec(v_unused_5327_);
v___x_5276_ = v_toApplicative_5267_;
v_isShared_5277_ = v_isSharedCheck_5326_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_toSeqRight_5274_);
lean_inc(v_toSeqLeft_5273_);
lean_inc(v_toSeq_5272_);
lean_inc(v_toFunctor_5271_);
lean_dec(v_toApplicative_5267_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5326_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___f_5278_; lean_object* v___f_5279_; lean_object* v___f_5280_; lean_object* v___f_5281_; lean_object* v___x_5282_; lean_object* v___f_5283_; lean_object* v___f_5284_; lean_object* v___f_5285_; lean_object* v___x_5287_; 
v___f_5278_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5279_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5271_);
v___f_5280_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5280_, 0, v_toFunctor_5271_);
v___f_5281_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5281_, 0, v_toFunctor_5271_);
v___x_5282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5282_, 0, v___f_5280_);
lean_ctor_set(v___x_5282_, 1, v___f_5281_);
v___f_5283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5283_, 0, v_toSeqRight_5274_);
v___f_5284_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5284_, 0, v_toSeqLeft_5273_);
v___f_5285_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5285_, 0, v_toSeq_5272_);
if (v_isShared_5277_ == 0)
{
lean_ctor_set(v___x_5276_, 4, v___f_5283_);
lean_ctor_set(v___x_5276_, 3, v___f_5284_);
lean_ctor_set(v___x_5276_, 2, v___f_5285_);
lean_ctor_set(v___x_5276_, 1, v___f_5278_);
lean_ctor_set(v___x_5276_, 0, v___x_5282_);
v___x_5287_ = v___x_5276_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5282_);
lean_ctor_set(v_reuseFailAlloc_5325_, 1, v___f_5278_);
lean_ctor_set(v_reuseFailAlloc_5325_, 2, v___f_5285_);
lean_ctor_set(v_reuseFailAlloc_5325_, 3, v___f_5284_);
lean_ctor_set(v_reuseFailAlloc_5325_, 4, v___f_5283_);
v___x_5287_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
lean_object* v___x_5289_; 
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 1, v___f_5279_);
lean_ctor_set(v___x_5269_, 0, v___x_5287_);
v___x_5289_ = v___x_5269_;
goto v_reusejp_5288_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v___x_5287_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v___f_5279_);
v___x_5289_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5288_;
}
v_reusejp_5288_:
{
lean_object* v___x_5290_; lean_object* v_toApplicative_5291_; lean_object* v___x_5293_; uint8_t v_isShared_5294_; uint8_t v_isSharedCheck_5322_; 
v___x_5290_ = l_StateRefT_x27_instMonad___redArg(v___x_5289_);
v_toApplicative_5291_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5322_ == 0)
{
lean_object* v_unused_5323_; 
v_unused_5323_ = lean_ctor_get(v___x_5290_, 1);
lean_dec(v_unused_5323_);
v___x_5293_ = v___x_5290_;
v_isShared_5294_ = v_isSharedCheck_5322_;
goto v_resetjp_5292_;
}
else
{
lean_inc(v_toApplicative_5291_);
lean_dec(v___x_5290_);
v___x_5293_ = lean_box(0);
v_isShared_5294_ = v_isSharedCheck_5322_;
goto v_resetjp_5292_;
}
v_resetjp_5292_:
{
lean_object* v_toFunctor_5295_; lean_object* v_toSeq_5296_; lean_object* v_toSeqLeft_5297_; lean_object* v_toSeqRight_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5320_; 
v_toFunctor_5295_ = lean_ctor_get(v_toApplicative_5291_, 0);
v_toSeq_5296_ = lean_ctor_get(v_toApplicative_5291_, 2);
v_toSeqLeft_5297_ = lean_ctor_get(v_toApplicative_5291_, 3);
v_toSeqRight_5298_ = lean_ctor_get(v_toApplicative_5291_, 4);
v_isSharedCheck_5320_ = !lean_is_exclusive(v_toApplicative_5291_);
if (v_isSharedCheck_5320_ == 0)
{
lean_object* v_unused_5321_; 
v_unused_5321_ = lean_ctor_get(v_toApplicative_5291_, 1);
lean_dec(v_unused_5321_);
v___x_5300_ = v_toApplicative_5291_;
v_isShared_5301_ = v_isSharedCheck_5320_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_toSeqRight_5298_);
lean_inc(v_toSeqLeft_5297_);
lean_inc(v_toSeq_5296_);
lean_inc(v_toFunctor_5295_);
lean_dec(v_toApplicative_5291_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5320_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___f_5302_; lean_object* v___f_5303_; lean_object* v___f_5304_; lean_object* v___f_5305_; lean_object* v___x_5306_; lean_object* v___f_5307_; lean_object* v___f_5308_; lean_object* v___f_5309_; lean_object* v___x_5311_; 
v___f_5302_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5303_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5295_);
v___f_5304_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5304_, 0, v_toFunctor_5295_);
v___f_5305_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5305_, 0, v_toFunctor_5295_);
v___x_5306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5306_, 0, v___f_5304_);
lean_ctor_set(v___x_5306_, 1, v___f_5305_);
v___f_5307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5307_, 0, v_toSeqRight_5298_);
v___f_5308_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5308_, 0, v_toSeqLeft_5297_);
v___f_5309_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5309_, 0, v_toSeq_5296_);
if (v_isShared_5301_ == 0)
{
lean_ctor_set(v___x_5300_, 4, v___f_5307_);
lean_ctor_set(v___x_5300_, 3, v___f_5308_);
lean_ctor_set(v___x_5300_, 2, v___f_5309_);
lean_ctor_set(v___x_5300_, 1, v___f_5302_);
lean_ctor_set(v___x_5300_, 0, v___x_5306_);
v___x_5311_ = v___x_5300_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v___x_5306_);
lean_ctor_set(v_reuseFailAlloc_5319_, 1, v___f_5302_);
lean_ctor_set(v_reuseFailAlloc_5319_, 2, v___f_5309_);
lean_ctor_set(v_reuseFailAlloc_5319_, 3, v___f_5308_);
lean_ctor_set(v_reuseFailAlloc_5319_, 4, v___f_5307_);
v___x_5311_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
lean_object* v___x_5313_; 
if (v_isShared_5294_ == 0)
{
lean_ctor_set(v___x_5293_, 1, v___f_5303_);
lean_ctor_set(v___x_5293_, 0, v___x_5311_);
v___x_5313_ = v___x_5293_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v___x_5311_);
lean_ctor_set(v_reuseFailAlloc_5318_, 1, v___f_5303_);
v___x_5313_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_27337__overap_5316_; lean_object* v___x_5317_; 
v___x_5314_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
v___x_5315_ = l_instInhabitedOfMonad___redArg(v___x_5313_, v___x_5314_);
v___x_27337__overap_5316_ = lean_panic_fn_borrowed(v___x_5315_, v_msg_5259_);
lean_dec(v___x_5315_);
lean_inc(v___y_5263_);
lean_inc_ref(v___y_5262_);
lean_inc(v___y_5261_);
lean_inc_ref(v___y_5260_);
v___x_5317_ = lean_apply_5(v___x_27337__overap_5316_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, lean_box(0));
return v___x_5317_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v___x_5343_; 
v___x_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5343_, 0, v___x_5337_);
return v___x_5343_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5351_, lean_object* v_onAlt_5352_, uint8_t v_useSplitter_5353_, lean_object* v_extraEqualities_5354_, lean_object* v_numDiscrEqs_5355_, lean_object* v_a_5356_, lean_object* v_b_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_, lean_object* v___y_5361_){
_start:
{
lean_object* v___y_5364_; uint8_t v___x_5387_; 
v___x_5387_ = lean_nat_dec_lt(v_a_5356_, v_upperBound_5351_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5388_; 
lean_dec(v_a_5356_);
lean_dec(v_numDiscrEqs_5355_);
lean_dec(v_extraEqualities_5354_);
lean_dec_ref(v_onAlt_5352_);
v___x_5388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5388_, 0, v_b_5357_);
return v___x_5388_;
}
else
{
lean_object* v_snd_5389_; lean_object* v_snd_5390_; lean_object* v_snd_5391_; lean_object* v_snd_5392_; lean_object* v_snd_5393_; lean_object* v_fst_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5598_; 
v_snd_5389_ = lean_ctor_get(v_b_5357_, 1);
lean_inc(v_snd_5389_);
v_snd_5390_ = lean_ctor_get(v_snd_5389_, 1);
lean_inc(v_snd_5390_);
v_snd_5391_ = lean_ctor_get(v_snd_5390_, 1);
lean_inc(v_snd_5391_);
v_snd_5392_ = lean_ctor_get(v_snd_5391_, 1);
lean_inc(v_snd_5392_);
v_snd_5393_ = lean_ctor_get(v_snd_5392_, 1);
lean_inc(v_snd_5393_);
v_fst_5394_ = lean_ctor_get(v_b_5357_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v_b_5357_);
if (v_isSharedCheck_5598_ == 0)
{
lean_object* v_unused_5599_; 
v_unused_5599_ = lean_ctor_get(v_b_5357_, 1);
lean_dec(v_unused_5599_);
v___x_5396_ = v_b_5357_;
v_isShared_5397_ = v_isSharedCheck_5598_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_fst_5394_);
lean_dec(v_b_5357_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5598_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v_fst_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5596_; 
v_fst_5398_ = lean_ctor_get(v_snd_5389_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_snd_5389_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v_snd_5389_, 1);
lean_dec(v_unused_5597_);
v___x_5400_ = v_snd_5389_;
v_isShared_5401_ = v_isSharedCheck_5596_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_fst_5398_);
lean_dec(v_snd_5389_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5596_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v_fst_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5594_; 
v_fst_5402_ = lean_ctor_get(v_snd_5390_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_snd_5390_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; 
v_unused_5595_ = lean_ctor_get(v_snd_5390_, 1);
lean_dec(v_unused_5595_);
v___x_5404_ = v_snd_5390_;
v_isShared_5405_ = v_isSharedCheck_5594_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_fst_5402_);
lean_dec(v_snd_5390_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5594_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v_fst_5406_; lean_object* v___x_5408_; uint8_t v_isShared_5409_; uint8_t v_isSharedCheck_5592_; 
v_fst_5406_ = lean_ctor_get(v_snd_5391_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v_snd_5391_);
if (v_isSharedCheck_5592_ == 0)
{
lean_object* v_unused_5593_; 
v_unused_5593_ = lean_ctor_get(v_snd_5391_, 1);
lean_dec(v_unused_5593_);
v___x_5408_ = v_snd_5391_;
v_isShared_5409_ = v_isSharedCheck_5592_;
goto v_resetjp_5407_;
}
else
{
lean_inc(v_fst_5406_);
lean_dec(v_snd_5391_);
v___x_5408_ = lean_box(0);
v_isShared_5409_ = v_isSharedCheck_5592_;
goto v_resetjp_5407_;
}
v_resetjp_5407_:
{
lean_object* v_fst_5410_; lean_object* v___x_5412_; uint8_t v_isShared_5413_; uint8_t v_isSharedCheck_5590_; 
v_fst_5410_ = lean_ctor_get(v_snd_5392_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v_snd_5392_);
if (v_isSharedCheck_5590_ == 0)
{
lean_object* v_unused_5591_; 
v_unused_5591_ = lean_ctor_get(v_snd_5392_, 1);
lean_dec(v_unused_5591_);
v___x_5412_ = v_snd_5392_;
v_isShared_5413_ = v_isSharedCheck_5590_;
goto v_resetjp_5411_;
}
else
{
lean_inc(v_fst_5410_);
lean_dec(v_snd_5392_);
v___x_5412_ = lean_box(0);
v_isShared_5413_ = v_isSharedCheck_5590_;
goto v_resetjp_5411_;
}
v_resetjp_5411_:
{
lean_object* v_array_5414_; lean_object* v_start_5415_; lean_object* v_stop_5416_; uint8_t v___x_5417_; 
v_array_5414_ = lean_ctor_get(v_snd_5393_, 0);
v_start_5415_ = lean_ctor_get(v_snd_5393_, 1);
v_stop_5416_ = lean_ctor_get(v_snd_5393_, 2);
v___x_5417_ = lean_nat_dec_lt(v_start_5415_, v_stop_5416_);
if (v___x_5417_ == 0)
{
lean_object* v___x_5419_; 
if (v_isShared_5413_ == 0)
{
v___x_5419_ = v___x_5412_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_fst_5410_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_snd_5393_);
v___x_5419_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
lean_object* v___x_5421_; 
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 1, v___x_5419_);
v___x_5421_ = v___x_5408_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5433_; 
v_reuseFailAlloc_5433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5433_, 0, v_fst_5406_);
lean_ctor_set(v_reuseFailAlloc_5433_, 1, v___x_5419_);
v___x_5421_ = v_reuseFailAlloc_5433_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v___x_5421_);
v___x_5423_ = v___x_5404_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_fst_5402_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v___x_5421_);
v___x_5423_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
lean_object* v___x_5425_; 
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 1, v___x_5423_);
v___x_5425_ = v___x_5400_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_fst_5398_);
lean_ctor_set(v_reuseFailAlloc_5431_, 1, v___x_5423_);
v___x_5425_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
lean_object* v___x_5427_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5425_);
v___x_5427_ = v___x_5396_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_fst_5394_);
lean_ctor_set(v_reuseFailAlloc_5430_, 1, v___x_5425_);
v___x_5427_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
lean_object* v___x_5428_; lean_object* v___f_5429_; 
v___x_5428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5428_, 0, v___x_5427_);
v___f_5429_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5429_, 0, v___x_5428_);
v___y_5364_ = v___f_5429_;
goto v___jp_5363_;
}
}
}
}
}
}
else
{
lean_object* v___x_5436_; uint8_t v_isShared_5437_; uint8_t v_isSharedCheck_5586_; 
lean_inc(v_stop_5416_);
lean_inc(v_start_5415_);
lean_inc_ref(v_array_5414_);
v_isSharedCheck_5586_ = !lean_is_exclusive(v_snd_5393_);
if (v_isSharedCheck_5586_ == 0)
{
lean_object* v_unused_5587_; lean_object* v_unused_5588_; lean_object* v_unused_5589_; 
v_unused_5587_ = lean_ctor_get(v_snd_5393_, 2);
lean_dec(v_unused_5587_);
v_unused_5588_ = lean_ctor_get(v_snd_5393_, 1);
lean_dec(v_unused_5588_);
v_unused_5589_ = lean_ctor_get(v_snd_5393_, 0);
lean_dec(v_unused_5589_);
v___x_5436_ = v_snd_5393_;
v_isShared_5437_ = v_isSharedCheck_5586_;
goto v_resetjp_5435_;
}
else
{
lean_dec(v_snd_5393_);
v___x_5436_ = lean_box(0);
v_isShared_5437_ = v_isSharedCheck_5586_;
goto v_resetjp_5435_;
}
v_resetjp_5435_:
{
lean_object* v_array_5438_; lean_object* v_start_5439_; lean_object* v_stop_5440_; lean_object* v___x_5441_; lean_object* v___x_5442_; lean_object* v___x_5443_; lean_object* v___x_5445_; 
v_array_5438_ = lean_ctor_get(v_fst_5410_, 0);
v_start_5439_ = lean_ctor_get(v_fst_5410_, 1);
v_stop_5440_ = lean_ctor_get(v_fst_5410_, 2);
v___x_5441_ = lean_array_fget(v_array_5414_, v_start_5415_);
v___x_5442_ = lean_unsigned_to_nat(1u);
v___x_5443_ = lean_nat_add(v_start_5415_, v___x_5442_);
lean_dec(v_start_5415_);
if (v_isShared_5437_ == 0)
{
lean_ctor_set(v___x_5436_, 1, v___x_5443_);
v___x_5445_ = v___x_5436_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_array_5414_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5585_, 2, v_stop_5416_);
v___x_5445_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
uint8_t v___x_5446_; 
v___x_5446_ = lean_nat_dec_lt(v_start_5439_, v_stop_5440_);
if (v___x_5446_ == 0)
{
lean_object* v___x_5448_; 
lean_dec(v___x_5441_);
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 1, v___x_5445_);
v___x_5448_ = v___x_5412_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_fst_5410_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v___x_5445_);
v___x_5448_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
lean_object* v___x_5450_; 
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 1, v___x_5448_);
v___x_5450_ = v___x_5408_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v_fst_5406_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v___x_5448_);
v___x_5450_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
lean_object* v___x_5452_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v___x_5450_);
v___x_5452_ = v___x_5404_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_fst_5402_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v___x_5450_);
v___x_5452_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
lean_object* v___x_5454_; 
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 1, v___x_5452_);
v___x_5454_ = v___x_5400_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_fst_5398_);
lean_ctor_set(v_reuseFailAlloc_5460_, 1, v___x_5452_);
v___x_5454_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5456_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5454_);
v___x_5456_ = v___x_5396_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_fst_5394_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v___x_5454_);
v___x_5456_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
lean_object* v___x_5457_; lean_object* v___f_5458_; 
v___x_5457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5457_, 0, v___x_5456_);
v___f_5458_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5458_, 0, v___x_5457_);
v___y_5364_ = v___f_5458_;
goto v___jp_5363_;
}
}
}
}
}
}
else
{
lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5581_; 
lean_inc(v_stop_5440_);
lean_inc(v_start_5439_);
lean_inc_ref(v_array_5438_);
v_isSharedCheck_5581_ = !lean_is_exclusive(v_fst_5410_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; lean_object* v_unused_5583_; lean_object* v_unused_5584_; 
v_unused_5582_ = lean_ctor_get(v_fst_5410_, 2);
lean_dec(v_unused_5582_);
v_unused_5583_ = lean_ctor_get(v_fst_5410_, 1);
lean_dec(v_unused_5583_);
v_unused_5584_ = lean_ctor_get(v_fst_5410_, 0);
lean_dec(v_unused_5584_);
v___x_5465_ = v_fst_5410_;
v_isShared_5466_ = v_isSharedCheck_5581_;
goto v_resetjp_5464_;
}
else
{
lean_dec(v_fst_5410_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5581_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v_array_5467_; lean_object* v_start_5468_; lean_object* v_stop_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5473_; 
v_array_5467_ = lean_ctor_get(v_fst_5406_, 0);
v_start_5468_ = lean_ctor_get(v_fst_5406_, 1);
v_stop_5469_ = lean_ctor_get(v_fst_5406_, 2);
v___x_5470_ = lean_array_fget(v_array_5438_, v_start_5439_);
v___x_5471_ = lean_nat_add(v_start_5439_, v___x_5442_);
lean_dec(v_start_5439_);
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 1, v___x_5471_);
v___x_5473_ = v___x_5465_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v_array_5438_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5580_, 2, v_stop_5440_);
v___x_5473_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
uint8_t v___x_5474_; 
v___x_5474_ = lean_nat_dec_lt(v_start_5468_, v_stop_5469_);
if (v___x_5474_ == 0)
{
lean_object* v___x_5476_; 
lean_dec(v___x_5470_);
lean_dec(v___x_5441_);
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 1, v___x_5445_);
lean_ctor_set(v___x_5412_, 0, v___x_5473_);
v___x_5476_ = v___x_5412_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v___x_5445_);
v___x_5476_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
lean_object* v___x_5478_; 
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 1, v___x_5476_);
v___x_5478_ = v___x_5408_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_fst_5406_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v___x_5476_);
v___x_5478_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
lean_object* v___x_5480_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v___x_5478_);
v___x_5480_ = v___x_5404_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v_fst_5402_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v___x_5478_);
v___x_5480_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
lean_object* v___x_5482_; 
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 1, v___x_5480_);
v___x_5482_ = v___x_5400_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_fst_5398_);
lean_ctor_set(v_reuseFailAlloc_5488_, 1, v___x_5480_);
v___x_5482_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
lean_object* v___x_5484_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5482_);
v___x_5484_ = v___x_5396_;
goto v_reusejp_5483_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_fst_5394_);
lean_ctor_set(v_reuseFailAlloc_5487_, 1, v___x_5482_);
v___x_5484_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5483_;
}
v_reusejp_5483_:
{
lean_object* v___x_5485_; lean_object* v___f_5486_; 
v___x_5485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5484_);
v___f_5486_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5486_, 0, v___x_5485_);
v___y_5364_ = v___f_5486_;
goto v___jp_5363_;
}
}
}
}
}
}
else
{
lean_object* v___x_5493_; uint8_t v_isShared_5494_; uint8_t v_isSharedCheck_5576_; 
lean_inc(v_stop_5469_);
lean_inc(v_start_5468_);
lean_inc_ref(v_array_5467_);
v_isSharedCheck_5576_ = !lean_is_exclusive(v_fst_5406_);
if (v_isSharedCheck_5576_ == 0)
{
lean_object* v_unused_5577_; lean_object* v_unused_5578_; lean_object* v_unused_5579_; 
v_unused_5577_ = lean_ctor_get(v_fst_5406_, 2);
lean_dec(v_unused_5577_);
v_unused_5578_ = lean_ctor_get(v_fst_5406_, 1);
lean_dec(v_unused_5578_);
v_unused_5579_ = lean_ctor_get(v_fst_5406_, 0);
lean_dec(v_unused_5579_);
v___x_5493_ = v_fst_5406_;
v_isShared_5494_ = v_isSharedCheck_5576_;
goto v_resetjp_5492_;
}
else
{
lean_dec(v_fst_5406_);
v___x_5493_ = lean_box(0);
v_isShared_5494_ = v_isSharedCheck_5576_;
goto v_resetjp_5492_;
}
v_resetjp_5492_:
{
lean_object* v_array_5495_; lean_object* v_start_5496_; lean_object* v_stop_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5501_; 
v_array_5495_ = lean_ctor_get(v_fst_5402_, 0);
v_start_5496_ = lean_ctor_get(v_fst_5402_, 1);
v_stop_5497_ = lean_ctor_get(v_fst_5402_, 2);
v___x_5498_ = lean_array_fget(v_array_5467_, v_start_5468_);
v___x_5499_ = lean_nat_add(v_start_5468_, v___x_5442_);
lean_dec(v_start_5468_);
if (v_isShared_5494_ == 0)
{
lean_ctor_set(v___x_5493_, 1, v___x_5499_);
v___x_5501_ = v___x_5493_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_array_5467_);
lean_ctor_set(v_reuseFailAlloc_5575_, 1, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5575_, 2, v_stop_5469_);
v___x_5501_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
uint8_t v___x_5502_; 
v___x_5502_ = lean_nat_dec_lt(v_start_5496_, v_stop_5497_);
if (v___x_5502_ == 0)
{
lean_object* v___x_5504_; 
lean_dec(v___x_5498_);
lean_dec(v___x_5470_);
lean_dec(v___x_5441_);
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 1, v___x_5445_);
lean_ctor_set(v___x_5412_, 0, v___x_5473_);
v___x_5504_ = v___x_5412_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5519_, 1, v___x_5445_);
v___x_5504_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5506_; 
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 1, v___x_5504_);
lean_ctor_set(v___x_5408_, 0, v___x_5501_);
v___x_5506_ = v___x_5408_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5501_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5504_);
v___x_5506_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5508_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v___x_5506_);
v___x_5508_ = v___x_5404_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_fst_5402_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v___x_5506_);
v___x_5508_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
lean_object* v___x_5510_; 
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 1, v___x_5508_);
v___x_5510_ = v___x_5400_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_fst_5398_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v___x_5508_);
v___x_5510_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5512_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5510_);
v___x_5512_ = v___x_5396_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_fst_5394_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v___x_5510_);
v___x_5512_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
lean_object* v___x_5513_; lean_object* v___f_5514_; 
v___x_5513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5513_, 0, v___x_5512_);
v___f_5514_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5514_, 0, v___x_5513_);
v___y_5364_ = v___f_5514_;
goto v___jp_5363_;
}
}
}
}
}
}
else
{
lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5571_; 
lean_inc(v_stop_5497_);
lean_inc(v_start_5496_);
lean_inc_ref(v_array_5495_);
v_isSharedCheck_5571_ = !lean_is_exclusive(v_fst_5402_);
if (v_isSharedCheck_5571_ == 0)
{
lean_object* v_unused_5572_; lean_object* v_unused_5573_; lean_object* v_unused_5574_; 
v_unused_5572_ = lean_ctor_get(v_fst_5402_, 2);
lean_dec(v_unused_5572_);
v_unused_5573_ = lean_ctor_get(v_fst_5402_, 1);
lean_dec(v_unused_5573_);
v_unused_5574_ = lean_ctor_get(v_fst_5402_, 0);
lean_dec(v_unused_5574_);
v___x_5521_ = v_fst_5402_;
v_isShared_5522_ = v_isSharedCheck_5571_;
goto v_resetjp_5520_;
}
else
{
lean_dec(v_fst_5402_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5571_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v_array_5523_; lean_object* v_start_5524_; lean_object* v_stop_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5529_; 
v_array_5523_ = lean_ctor_get(v_fst_5398_, 0);
v_start_5524_ = lean_ctor_get(v_fst_5398_, 1);
v_stop_5525_ = lean_ctor_get(v_fst_5398_, 2);
v___x_5526_ = lean_array_fget(v_array_5495_, v_start_5496_);
v___x_5527_ = lean_nat_add(v_start_5496_, v___x_5442_);
lean_dec(v_start_5496_);
if (v_isShared_5522_ == 0)
{
lean_ctor_set(v___x_5521_, 1, v___x_5527_);
v___x_5529_ = v___x_5521_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v_array_5495_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5570_, 2, v_stop_5497_);
v___x_5529_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
uint8_t v___x_5530_; 
v___x_5530_ = lean_nat_dec_lt(v_start_5524_, v_stop_5525_);
if (v___x_5530_ == 0)
{
lean_object* v___x_5532_; 
lean_dec(v___x_5526_);
lean_dec(v___x_5498_);
lean_dec(v___x_5470_);
lean_dec(v___x_5441_);
if (v_isShared_5413_ == 0)
{
lean_ctor_set(v___x_5412_, 1, v___x_5445_);
lean_ctor_set(v___x_5412_, 0, v___x_5473_);
v___x_5532_ = v___x_5412_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v___x_5445_);
v___x_5532_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
lean_object* v___x_5534_; 
if (v_isShared_5409_ == 0)
{
lean_ctor_set(v___x_5408_, 1, v___x_5532_);
lean_ctor_set(v___x_5408_, 0, v___x_5501_);
v___x_5534_ = v___x_5408_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5501_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v___x_5532_);
v___x_5534_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5536_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 1, v___x_5534_);
lean_ctor_set(v___x_5404_, 0, v___x_5529_);
v___x_5536_ = v___x_5404_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v___x_5529_);
lean_ctor_set(v_reuseFailAlloc_5545_, 1, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
lean_object* v___x_5538_; 
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 1, v___x_5536_);
v___x_5538_ = v___x_5400_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_fst_5398_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5536_);
v___x_5538_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
lean_object* v___x_5540_; 
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 1, v___x_5538_);
v___x_5540_ = v___x_5396_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_fst_5394_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v___x_5538_);
v___x_5540_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
lean_object* v___x_5541_; lean_object* v___f_5542_; 
v___x_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5541_, 0, v___x_5540_);
v___f_5542_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5542_, 0, v___x_5541_);
v___y_5364_ = v___f_5542_;
goto v___jp_5363_;
}
}
}
}
}
}
else
{
lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5566_; 
lean_inc(v_stop_5525_);
lean_inc(v_start_5524_);
lean_inc_ref(v_array_5523_);
lean_del_object(v___x_5412_);
lean_del_object(v___x_5408_);
lean_del_object(v___x_5404_);
lean_del_object(v___x_5400_);
lean_del_object(v___x_5396_);
v_isSharedCheck_5566_ = !lean_is_exclusive(v_fst_5398_);
if (v_isSharedCheck_5566_ == 0)
{
lean_object* v_unused_5567_; lean_object* v_unused_5568_; lean_object* v_unused_5569_; 
v_unused_5567_ = lean_ctor_get(v_fst_5398_, 2);
lean_dec(v_unused_5567_);
v_unused_5568_ = lean_ctor_get(v_fst_5398_, 1);
lean_dec(v_unused_5568_);
v_unused_5569_ = lean_ctor_get(v_fst_5398_, 0);
lean_dec(v_unused_5569_);
v___x_5549_ = v_fst_5398_;
v_isShared_5550_ = v_isSharedCheck_5566_;
goto v_resetjp_5548_;
}
else
{
lean_dec(v_fst_5398_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5566_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v_numOverlaps_5551_; lean_object* v___x_5552_; uint8_t v___x_5553_; 
v_numOverlaps_5551_ = lean_ctor_get(v___x_5526_, 1);
v___x_5552_ = lean_unsigned_to_nat(0u);
v___x_5553_ = lean_nat_dec_eq(v_numOverlaps_5551_, v___x_5552_);
if (v___x_5553_ == 0)
{
lean_object* v___x_5554_; lean_object* v___x_5555_; 
lean_del_object(v___x_5549_);
lean_dec_ref(v___x_5529_);
lean_dec(v___x_5526_);
lean_dec(v_stop_5525_);
lean_dec(v_start_5524_);
lean_dec_ref(v_array_5523_);
lean_dec_ref(v___x_5501_);
lean_dec(v___x_5498_);
lean_dec_ref(v___x_5473_);
lean_dec(v___x_5470_);
lean_dec_ref(v___x_5445_);
lean_dec(v___x_5441_);
lean_dec(v_fst_5394_);
v___x_5554_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_5555_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed), 6, 1);
lean_closure_set(v___x_5555_, 0, v___x_5554_);
v___y_5364_ = v___x_5555_;
goto v___jp_5363_;
}
else
{
uint8_t v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___f_5560_; lean_object* v___x_5561_; lean_object* v___x_5563_; 
v___x_5556_ = 0;
v___x_5557_ = lean_array_fget_borrowed(v_array_5523_, v_start_5524_);
v___x_5558_ = lean_box(v___x_5556_);
v___x_5559_ = lean_box(v_useSplitter_5353_);
lean_inc(v___x_5526_);
lean_inc(v_numDiscrEqs_5355_);
lean_inc(v_extraEqualities_5354_);
lean_inc(v___x_5557_);
lean_inc(v_a_5356_);
lean_inc_ref(v_onAlt_5352_);
v___f_5560_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5560_, 0, v___x_5498_);
lean_closure_set(v___f_5560_, 1, v_onAlt_5352_);
lean_closure_set(v___f_5560_, 2, v_a_5356_);
lean_closure_set(v___f_5560_, 3, v___x_5558_);
lean_closure_set(v___f_5560_, 4, v___x_5559_);
lean_closure_set(v___f_5560_, 5, v___x_5557_);
lean_closure_set(v___f_5560_, 6, v_extraEqualities_5354_);
lean_closure_set(v___f_5560_, 7, v_numDiscrEqs_5355_);
lean_closure_set(v___f_5560_, 8, v___x_5441_);
lean_closure_set(v___f_5560_, 9, v___x_5526_);
lean_closure_set(v___f_5560_, 10, v___x_5442_);
v___x_5561_ = lean_nat_add(v_start_5524_, v___x_5442_);
lean_dec(v_start_5524_);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 1, v___x_5561_);
v___x_5563_ = v___x_5549_;
goto v_reusejp_5562_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_array_5523_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5561_);
lean_ctor_set(v_reuseFailAlloc_5565_, 2, v_stop_5525_);
v___x_5563_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5562_;
}
v_reusejp_5562_:
{
lean_object* v___f_5564_; 
v___f_5564_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5564_, 0, v___x_5470_);
lean_closure_set(v___f_5564_, 1, v___x_5526_);
lean_closure_set(v___f_5564_, 2, v___f_5560_);
lean_closure_set(v___f_5564_, 3, v_fst_5394_);
lean_closure_set(v___f_5564_, 4, v___x_5473_);
lean_closure_set(v___f_5564_, 5, v___x_5445_);
lean_closure_set(v___f_5564_, 6, v___x_5501_);
lean_closure_set(v___f_5564_, 7, v___x_5529_);
lean_closure_set(v___f_5564_, 8, v___x_5563_);
v___y_5364_ = v___f_5564_;
goto v___jp_5363_;
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
v___jp_5363_:
{
lean_object* v___x_5365_; 
lean_inc(v___y_5361_);
lean_inc_ref(v___y_5360_);
lean_inc(v___y_5359_);
lean_inc_ref(v___y_5358_);
v___x_5365_ = lean_apply_5(v___y_5364_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, lean_box(0));
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v_a_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5378_; 
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
v_isSharedCheck_5378_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5378_ == 0)
{
v___x_5368_ = v___x_5365_;
v_isShared_5369_ = v_isSharedCheck_5378_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_a_5366_);
lean_dec(v___x_5365_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5378_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
if (lean_obj_tag(v_a_5366_) == 0)
{
lean_object* v_a_5370_; lean_object* v___x_5372_; 
lean_dec(v_a_5356_);
lean_dec(v_numDiscrEqs_5355_);
lean_dec(v_extraEqualities_5354_);
lean_dec_ref(v_onAlt_5352_);
v_a_5370_ = lean_ctor_get(v_a_5366_, 0);
lean_inc(v_a_5370_);
lean_dec_ref_known(v_a_5366_, 1);
if (v_isShared_5369_ == 0)
{
lean_ctor_set(v___x_5368_, 0, v_a_5370_);
v___x_5372_ = v___x_5368_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5370_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
else
{
lean_object* v_a_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; 
lean_del_object(v___x_5368_);
v_a_5374_ = lean_ctor_get(v_a_5366_, 0);
lean_inc(v_a_5374_);
lean_dec_ref_known(v_a_5366_, 1);
v___x_5375_ = lean_unsigned_to_nat(1u);
v___x_5376_ = lean_nat_add(v_a_5356_, v___x_5375_);
lean_dec(v_a_5356_);
v_a_5356_ = v___x_5376_;
v_b_5357_ = v_a_5374_;
goto _start;
}
}
}
else
{
lean_object* v_a_5379_; lean_object* v___x_5381_; uint8_t v_isShared_5382_; uint8_t v_isSharedCheck_5386_; 
lean_dec(v_a_5356_);
lean_dec(v_numDiscrEqs_5355_);
lean_dec(v_extraEqualities_5354_);
lean_dec_ref(v_onAlt_5352_);
v_a_5379_ = lean_ctor_get(v___x_5365_, 0);
v_isSharedCheck_5386_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5386_ == 0)
{
v___x_5381_ = v___x_5365_;
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
else
{
lean_inc(v_a_5379_);
lean_dec(v___x_5365_);
v___x_5381_ = lean_box(0);
v_isShared_5382_ = v_isSharedCheck_5386_;
goto v_resetjp_5380_;
}
v_resetjp_5380_:
{
lean_object* v___x_5384_; 
if (v_isShared_5382_ == 0)
{
v___x_5384_ = v___x_5381_;
goto v_reusejp_5383_;
}
else
{
lean_object* v_reuseFailAlloc_5385_; 
v_reuseFailAlloc_5385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5385_, 0, v_a_5379_);
v___x_5384_ = v_reuseFailAlloc_5385_;
goto v_reusejp_5383_;
}
v_reusejp_5383_:
{
return v___x_5384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5600_, lean_object* v_onAlt_5601_, lean_object* v_useSplitter_5602_, lean_object* v_extraEqualities_5603_, lean_object* v_numDiscrEqs_5604_, lean_object* v_a_5605_, lean_object* v_b_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
uint8_t v_useSplitter_boxed_5612_; lean_object* v_res_5613_; 
v_useSplitter_boxed_5612_ = lean_unbox(v_useSplitter_5602_);
v_res_5613_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5600_, v_onAlt_5601_, v_useSplitter_boxed_5612_, v_extraEqualities_5603_, v_numDiscrEqs_5604_, v_a_5605_, v_b_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
lean_dec(v___y_5610_);
lean_dec_ref(v___y_5609_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v_upperBound_5600_);
return v_res_5613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5614_, lean_object* v_as_5615_, size_t v_sz_5616_, size_t v_i_5617_, lean_object* v_b_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_){
_start:
{
lean_object* v_a_5625_; uint8_t v___x_5629_; 
v___x_5629_ = lean_usize_dec_lt(v_i_5617_, v_sz_5616_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5630_; 
v___x_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5630_, 0, v_b_5618_);
return v___x_5630_;
}
else
{
lean_object* v_snd_5631_; lean_object* v_snd_5632_; lean_object* v_snd_5633_; lean_object* v_snd_5634_; lean_object* v_fst_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5781_; 
v_snd_5631_ = lean_ctor_get(v_b_5618_, 1);
lean_inc(v_snd_5631_);
v_snd_5632_ = lean_ctor_get(v_snd_5631_, 1);
lean_inc(v_snd_5632_);
v_snd_5633_ = lean_ctor_get(v_snd_5632_, 1);
lean_inc(v_snd_5633_);
v_snd_5634_ = lean_ctor_get(v_snd_5633_, 1);
lean_inc(v_snd_5634_);
v_fst_5635_ = lean_ctor_get(v_b_5618_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v_b_5618_);
if (v_isSharedCheck_5781_ == 0)
{
lean_object* v_unused_5782_; 
v_unused_5782_ = lean_ctor_get(v_b_5618_, 1);
lean_dec(v_unused_5782_);
v___x_5637_ = v_b_5618_;
v_isShared_5638_ = v_isSharedCheck_5781_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_fst_5635_);
lean_dec(v_b_5618_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5781_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v_fst_5639_; lean_object* v___x_5641_; uint8_t v_isShared_5642_; uint8_t v_isSharedCheck_5779_; 
v_fst_5639_ = lean_ctor_get(v_snd_5631_, 0);
v_isSharedCheck_5779_ = !lean_is_exclusive(v_snd_5631_);
if (v_isSharedCheck_5779_ == 0)
{
lean_object* v_unused_5780_; 
v_unused_5780_ = lean_ctor_get(v_snd_5631_, 1);
lean_dec(v_unused_5780_);
v___x_5641_ = v_snd_5631_;
v_isShared_5642_ = v_isSharedCheck_5779_;
goto v_resetjp_5640_;
}
else
{
lean_inc(v_fst_5639_);
lean_dec(v_snd_5631_);
v___x_5641_ = lean_box(0);
v_isShared_5642_ = v_isSharedCheck_5779_;
goto v_resetjp_5640_;
}
v_resetjp_5640_:
{
lean_object* v_fst_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5777_; 
v_fst_5643_ = lean_ctor_get(v_snd_5632_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v_snd_5632_);
if (v_isSharedCheck_5777_ == 0)
{
lean_object* v_unused_5778_; 
v_unused_5778_ = lean_ctor_get(v_snd_5632_, 1);
lean_dec(v_unused_5778_);
v___x_5645_ = v_snd_5632_;
v_isShared_5646_ = v_isSharedCheck_5777_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_fst_5643_);
lean_dec(v_snd_5632_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5777_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v_fst_5647_; lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5775_; 
v_fst_5647_ = lean_ctor_get(v_snd_5633_, 0);
v_isSharedCheck_5775_ = !lean_is_exclusive(v_snd_5633_);
if (v_isSharedCheck_5775_ == 0)
{
lean_object* v_unused_5776_; 
v_unused_5776_ = lean_ctor_get(v_snd_5633_, 1);
lean_dec(v_unused_5776_);
v___x_5649_ = v_snd_5633_;
v_isShared_5650_ = v_isSharedCheck_5775_;
goto v_resetjp_5648_;
}
else
{
lean_inc(v_fst_5647_);
lean_dec(v_snd_5633_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5775_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v_array_5651_; lean_object* v_start_5652_; lean_object* v_stop_5653_; uint8_t v___x_5654_; 
v_array_5651_ = lean_ctor_get(v_snd_5634_, 0);
v_start_5652_ = lean_ctor_get(v_snd_5634_, 1);
v_stop_5653_ = lean_ctor_get(v_snd_5634_, 2);
v___x_5654_ = lean_nat_dec_lt(v_start_5652_, v_stop_5653_);
if (v___x_5654_ == 0)
{
lean_object* v___x_5656_; 
if (v_isShared_5650_ == 0)
{
v___x_5656_ = v___x_5649_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v_fst_5647_);
lean_ctor_set(v_reuseFailAlloc_5667_, 1, v_snd_5634_);
v___x_5656_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5658_; 
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 1, v___x_5656_);
v___x_5658_ = v___x_5645_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5666_; 
v_reuseFailAlloc_5666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5666_, 0, v_fst_5643_);
lean_ctor_set(v_reuseFailAlloc_5666_, 1, v___x_5656_);
v___x_5658_ = v_reuseFailAlloc_5666_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
lean_object* v___x_5660_; 
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 1, v___x_5658_);
v___x_5660_ = v___x_5641_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_fst_5639_);
lean_ctor_set(v_reuseFailAlloc_5665_, 1, v___x_5658_);
v___x_5660_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
lean_object* v___x_5662_; 
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v___x_5660_);
v___x_5662_ = v___x_5637_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_fst_5635_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v___x_5660_);
v___x_5662_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5663_; 
v___x_5663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
return v___x_5663_;
}
}
}
}
}
else
{
lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5771_; 
lean_inc(v_stop_5653_);
lean_inc(v_start_5652_);
lean_inc_ref(v_array_5651_);
v_isSharedCheck_5771_ = !lean_is_exclusive(v_snd_5634_);
if (v_isSharedCheck_5771_ == 0)
{
lean_object* v_unused_5772_; lean_object* v_unused_5773_; lean_object* v_unused_5774_; 
v_unused_5772_ = lean_ctor_get(v_snd_5634_, 2);
lean_dec(v_unused_5772_);
v_unused_5773_ = lean_ctor_get(v_snd_5634_, 1);
lean_dec(v_unused_5773_);
v_unused_5774_ = lean_ctor_get(v_snd_5634_, 0);
lean_dec(v_unused_5774_);
v___x_5669_ = v_snd_5634_;
v_isShared_5670_ = v_isSharedCheck_5771_;
goto v_resetjp_5668_;
}
else
{
lean_dec(v_snd_5634_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5771_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v_array_5671_; lean_object* v_start_5672_; lean_object* v_stop_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5678_; 
v_array_5671_ = lean_ctor_get(v_fst_5647_, 0);
v_start_5672_ = lean_ctor_get(v_fst_5647_, 1);
v_stop_5673_ = lean_ctor_get(v_fst_5647_, 2);
v___x_5674_ = lean_array_fget(v_array_5651_, v_start_5652_);
v___x_5675_ = lean_unsigned_to_nat(1u);
v___x_5676_ = lean_nat_add(v_start_5652_, v___x_5675_);
lean_dec(v_start_5652_);
if (v_isShared_5670_ == 0)
{
lean_ctor_set(v___x_5669_, 1, v___x_5676_);
v___x_5678_ = v___x_5669_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_array_5651_);
lean_ctor_set(v_reuseFailAlloc_5770_, 1, v___x_5676_);
lean_ctor_set(v_reuseFailAlloc_5770_, 2, v_stop_5653_);
v___x_5678_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
uint8_t v___x_5679_; 
v___x_5679_ = lean_nat_dec_lt(v_start_5672_, v_stop_5673_);
if (v___x_5679_ == 0)
{
lean_object* v___x_5681_; 
lean_dec(v___x_5674_);
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 1, v___x_5678_);
v___x_5681_ = v___x_5649_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_fst_5647_);
lean_ctor_set(v_reuseFailAlloc_5692_, 1, v___x_5678_);
v___x_5681_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
lean_object* v___x_5683_; 
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 1, v___x_5681_);
v___x_5683_ = v___x_5645_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5691_; 
v_reuseFailAlloc_5691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5691_, 0, v_fst_5643_);
lean_ctor_set(v_reuseFailAlloc_5691_, 1, v___x_5681_);
v___x_5683_ = v_reuseFailAlloc_5691_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
lean_object* v___x_5685_; 
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 1, v___x_5683_);
v___x_5685_ = v___x_5641_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_fst_5639_);
lean_ctor_set(v_reuseFailAlloc_5690_, 1, v___x_5683_);
v___x_5685_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
lean_object* v___x_5687_; 
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v___x_5685_);
v___x_5687_ = v___x_5637_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_fst_5635_);
lean_ctor_set(v_reuseFailAlloc_5689_, 1, v___x_5685_);
v___x_5687_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
lean_object* v___x_5688_; 
v___x_5688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
return v___x_5688_;
}
}
}
}
}
else
{
lean_object* v___x_5694_; uint8_t v_isShared_5695_; uint8_t v_isSharedCheck_5766_; 
lean_inc(v_stop_5673_);
lean_inc(v_start_5672_);
lean_inc_ref(v_array_5671_);
v_isSharedCheck_5766_ = !lean_is_exclusive(v_fst_5647_);
if (v_isSharedCheck_5766_ == 0)
{
lean_object* v_unused_5767_; lean_object* v_unused_5768_; lean_object* v_unused_5769_; 
v_unused_5767_ = lean_ctor_get(v_fst_5647_, 2);
lean_dec(v_unused_5767_);
v_unused_5768_ = lean_ctor_get(v_fst_5647_, 1);
lean_dec(v_unused_5768_);
v_unused_5769_ = lean_ctor_get(v_fst_5647_, 0);
lean_dec(v_unused_5769_);
v___x_5694_ = v_fst_5647_;
v_isShared_5695_ = v_isSharedCheck_5766_;
goto v_resetjp_5693_;
}
else
{
lean_dec(v_fst_5647_);
v___x_5694_ = lean_box(0);
v_isShared_5695_ = v_isSharedCheck_5766_;
goto v_resetjp_5693_;
}
v_resetjp_5693_:
{
lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5699_; 
v___x_5696_ = lean_array_fget(v_array_5671_, v_start_5672_);
v___x_5697_ = lean_nat_add(v_start_5672_, v___x_5675_);
lean_dec(v_start_5672_);
if (v_isShared_5695_ == 0)
{
lean_ctor_set(v___x_5694_, 1, v___x_5697_);
v___x_5699_ = v___x_5694_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5765_; 
v_reuseFailAlloc_5765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_array_5671_);
lean_ctor_set(v_reuseFailAlloc_5765_, 1, v___x_5697_);
lean_ctor_set(v_reuseFailAlloc_5765_, 2, v_stop_5673_);
v___x_5699_ = v_reuseFailAlloc_5765_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
if (v_addEqualities_5614_ == 0)
{
lean_dec(v___x_5696_);
goto v___jp_5700_;
}
else
{
if (lean_obj_tag(v___x_5674_) == 0)
{
lean_object* v_a_5716_; lean_object* v___x_5717_; 
lean_del_object(v___x_5649_);
lean_del_object(v___x_5645_);
lean_del_object(v___x_5641_);
lean_del_object(v___x_5637_);
v_a_5716_ = lean_array_uget_borrowed(v_as_5615_, v_i_5617_);
lean_inc(v_a_5716_);
v___x_5717_ = l_Lean_Meta_isProof(v_a_5716_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_);
if (lean_obj_tag(v___x_5717_) == 0)
{
lean_object* v_a_5718_; uint8_t v___x_5719_; 
v_a_5718_ = lean_ctor_get(v___x_5717_, 0);
lean_inc(v_a_5718_);
lean_dec_ref_known(v___x_5717_, 1);
v___x_5719_ = lean_unbox(v_a_5718_);
lean_dec(v_a_5718_);
if (v___x_5719_ == 0)
{
lean_object* v___x_5720_; 
lean_inc(v_a_5716_);
v___x_5720_ = l_Lean_Meta_mkEqHEq(v___x_5696_, v_a_5716_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_object* v_a_5721_; lean_object* v___x_5722_; 
v_a_5721_ = lean_ctor_get(v___x_5720_, 0);
lean_inc_n(v_a_5721_, 2);
lean_dec_ref_known(v___x_5720_, 1);
v___x_5722_ = l_Lean_mkArrow(v_a_5721_, v_fst_5635_, v___y_5621_, v___y_5622_);
if (lean_obj_tag(v___x_5722_) == 0)
{
lean_object* v_a_5723_; uint8_t v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v___x_5733_; 
v_a_5723_ = lean_ctor_get(v___x_5722_, 0);
lean_inc(v_a_5723_);
lean_dec_ref_known(v___x_5722_, 1);
v___x_5724_ = l_Lean_Expr_isHEq(v_a_5721_);
lean_dec(v_a_5721_);
v___x_5725_ = lean_box(v___x_5724_);
v___x_5726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5726_, 0, v___x_5725_);
v___x_5727_ = lean_array_push(v_fst_5639_, v___x_5726_);
v___x_5728_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_5729_ = lean_array_push(v_fst_5643_, v___x_5728_);
v___x_5730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5699_);
lean_ctor_set(v___x_5730_, 1, v___x_5678_);
v___x_5731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5729_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
v___x_5732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5727_);
lean_ctor_set(v___x_5732_, 1, v___x_5731_);
v___x_5733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5733_, 0, v_a_5723_);
lean_ctor_set(v___x_5733_, 1, v___x_5732_);
v_a_5625_ = v___x_5733_;
goto v___jp_5624_;
}
else
{
lean_object* v_a_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5741_; 
lean_dec(v_a_5721_);
lean_dec_ref(v___x_5699_);
lean_dec_ref(v___x_5678_);
lean_dec(v_fst_5643_);
lean_dec(v_fst_5639_);
v_a_5734_ = lean_ctor_get(v___x_5722_, 0);
v_isSharedCheck_5741_ = !lean_is_exclusive(v___x_5722_);
if (v_isSharedCheck_5741_ == 0)
{
v___x_5736_ = v___x_5722_;
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_a_5734_);
lean_dec(v___x_5722_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5741_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v___x_5739_; 
if (v_isShared_5737_ == 0)
{
v___x_5739_ = v___x_5736_;
goto v_reusejp_5738_;
}
else
{
lean_object* v_reuseFailAlloc_5740_; 
v_reuseFailAlloc_5740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5740_, 0, v_a_5734_);
v___x_5739_ = v_reuseFailAlloc_5740_;
goto v_reusejp_5738_;
}
v_reusejp_5738_:
{
return v___x_5739_;
}
}
}
}
else
{
lean_object* v_a_5742_; lean_object* v___x_5744_; uint8_t v_isShared_5745_; uint8_t v_isSharedCheck_5749_; 
lean_dec_ref(v___x_5699_);
lean_dec_ref(v___x_5678_);
lean_dec(v_fst_5643_);
lean_dec(v_fst_5639_);
lean_dec(v_fst_5635_);
v_a_5742_ = lean_ctor_get(v___x_5720_, 0);
v_isSharedCheck_5749_ = !lean_is_exclusive(v___x_5720_);
if (v_isSharedCheck_5749_ == 0)
{
v___x_5744_ = v___x_5720_;
v_isShared_5745_ = v_isSharedCheck_5749_;
goto v_resetjp_5743_;
}
else
{
lean_inc(v_a_5742_);
lean_dec(v___x_5720_);
v___x_5744_ = lean_box(0);
v_isShared_5745_ = v_isSharedCheck_5749_;
goto v_resetjp_5743_;
}
v_resetjp_5743_:
{
lean_object* v___x_5747_; 
if (v_isShared_5745_ == 0)
{
v___x_5747_ = v___x_5744_;
goto v_reusejp_5746_;
}
else
{
lean_object* v_reuseFailAlloc_5748_; 
v_reuseFailAlloc_5748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5748_, 0, v_a_5742_);
v___x_5747_ = v_reuseFailAlloc_5748_;
goto v_reusejp_5746_;
}
v_reusejp_5746_:
{
return v___x_5747_;
}
}
}
}
else
{
lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
lean_dec(v___x_5696_);
v___x_5750_ = lean_box(0);
v___x_5751_ = lean_array_push(v_fst_5639_, v___x_5750_);
v___x_5752_ = lean_array_push(v_fst_5643_, v___x_5674_);
v___x_5753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5699_);
lean_ctor_set(v___x_5753_, 1, v___x_5678_);
v___x_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5754_, 0, v___x_5752_);
lean_ctor_set(v___x_5754_, 1, v___x_5753_);
v___x_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___x_5751_);
lean_ctor_set(v___x_5755_, 1, v___x_5754_);
v___x_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5756_, 0, v_fst_5635_);
lean_ctor_set(v___x_5756_, 1, v___x_5755_);
v_a_5625_ = v___x_5756_;
goto v___jp_5624_;
}
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
lean_dec_ref(v___x_5699_);
lean_dec(v___x_5696_);
lean_dec_ref(v___x_5678_);
lean_dec(v_fst_5643_);
lean_dec(v_fst_5639_);
lean_dec(v_fst_5635_);
v_a_5757_ = lean_ctor_get(v___x_5717_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5717_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5717_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5717_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
else
{
lean_dec(v___x_5696_);
goto v___jp_5700_;
}
}
v___jp_5700_:
{
lean_object* v___x_5701_; lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5705_; 
v___x_5701_ = lean_box(0);
v___x_5702_ = lean_array_push(v_fst_5639_, v___x_5701_);
v___x_5703_ = lean_array_push(v_fst_5643_, v___x_5674_);
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 1, v___x_5678_);
lean_ctor_set(v___x_5649_, 0, v___x_5699_);
v___x_5705_ = v___x_5649_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5699_);
lean_ctor_set(v_reuseFailAlloc_5715_, 1, v___x_5678_);
v___x_5705_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
lean_object* v___x_5707_; 
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 1, v___x_5705_);
lean_ctor_set(v___x_5645_, 0, v___x_5703_);
v___x_5707_ = v___x_5645_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v___x_5703_);
lean_ctor_set(v_reuseFailAlloc_5714_, 1, v___x_5705_);
v___x_5707_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
lean_object* v___x_5709_; 
if (v_isShared_5642_ == 0)
{
lean_ctor_set(v___x_5641_, 1, v___x_5707_);
lean_ctor_set(v___x_5641_, 0, v___x_5702_);
v___x_5709_ = v___x_5641_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5702_);
lean_ctor_set(v_reuseFailAlloc_5713_, 1, v___x_5707_);
v___x_5709_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
lean_object* v___x_5711_; 
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v___x_5709_);
v___x_5711_ = v___x_5637_;
goto v_reusejp_5710_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v_fst_5635_);
lean_ctor_set(v_reuseFailAlloc_5712_, 1, v___x_5709_);
v___x_5711_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5710_;
}
v_reusejp_5710_:
{
v_a_5625_ = v___x_5711_;
goto v___jp_5624_;
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
v___jp_5624_:
{
size_t v___x_5626_; size_t v___x_5627_; 
v___x_5626_ = ((size_t)1ULL);
v___x_5627_ = lean_usize_add(v_i_5617_, v___x_5626_);
v_i_5617_ = v___x_5627_;
v_b_5618_ = v_a_5625_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5783_, lean_object* v_as_5784_, lean_object* v_sz_5785_, lean_object* v_i_5786_, lean_object* v_b_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_){
_start:
{
uint8_t v_addEqualities_boxed_5793_; size_t v_sz_boxed_5794_; size_t v_i_boxed_5795_; lean_object* v_res_5796_; 
v_addEqualities_boxed_5793_ = lean_unbox(v_addEqualities_5783_);
v_sz_boxed_5794_ = lean_unbox_usize(v_sz_5785_);
lean_dec(v_sz_5785_);
v_i_boxed_5795_ = lean_unbox_usize(v_i_5786_);
lean_dec(v_i_5786_);
v_res_5796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5793_, v_as_5784_, v_sz_boxed_5794_, v_i_boxed_5795_, v_b_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_);
lean_dec(v___y_5791_);
lean_dec_ref(v___y_5790_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec_ref(v_as_5784_);
return v_res_5796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5797_, lean_object* v_toMatcherInfo_5798_, lean_object* v_a_5799_, uint8_t v_addEqualities_5800_, size_t v___x_5801_, lean_object* v_discrs_5802_, lean_object* v_motiveArgs_5803_, lean_object* v_motiveBody_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; uint8_t v___x_5904_; 
v___x_5902_ = lean_array_get_size(v_motiveArgs_5803_);
v___x_5903_ = lean_array_get_size(v_discrs_5802_);
v___x_5904_ = lean_nat_dec_eq(v___x_5902_, v___x_5903_);
if (v___x_5904_ == 0)
{
lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5920_; 
lean_dec_ref(v_motiveBody_5804_);
lean_dec_ref(v_motiveArgs_5803_);
lean_dec_ref(v_a_5799_);
lean_dec_ref(v_toMatcherInfo_5798_);
lean_dec_ref(v_onMotive_5797_);
v___x_5905_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5906_ = l_Nat_reprFast(v___x_5903_);
v___x_5907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5906_);
v___x_5908_ = l_Lean_MessageData_ofFormat(v___x_5907_);
v___x_5909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5905_);
lean_ctor_set(v___x_5909_, 1, v___x_5908_);
v___x_5910_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5909_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
v___x_5912_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5911_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_5920_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_5920_ == 0)
{
v___x_5915_ = v___x_5912_;
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5912_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5920_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___x_5918_; 
if (v_isShared_5916_ == 0)
{
v___x_5918_ = v___x_5915_;
goto v_reusejp_5917_;
}
else
{
lean_object* v_reuseFailAlloc_5919_; 
v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
v___x_5918_ = v_reuseFailAlloc_5919_;
goto v_reusejp_5917_;
}
v_reusejp_5917_:
{
return v___x_5918_;
}
}
}
else
{
goto v___jp_5810_;
}
v___jp_5810_:
{
lean_object* v___x_5811_; 
lean_inc(v___y_5808_);
lean_inc_ref(v___y_5807_);
lean_inc(v___y_5806_);
lean_inc_ref(v___y_5805_);
lean_inc_ref(v_motiveArgs_5803_);
v___x_5811_ = lean_apply_7(v_onMotive_5797_, v_motiveArgs_5803_, v_motiveBody_5804_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, lean_box(0));
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v_discrInfos_5813_; lean_object* v___x_5814_; lean_object* v_addHEqualities_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; size_t v_sz_5824_; lean_object* v___x_5825_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
lean_inc(v_a_5812_);
lean_dec_ref_known(v___x_5811_, 1);
v_discrInfos_5813_ = lean_ctor_get(v_toMatcherInfo_5798_, 4);
lean_inc_ref(v_discrInfos_5813_);
lean_dec_ref(v_toMatcherInfo_5798_);
v___x_5814_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5815_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5816_ = lean_array_get_size(v_a_5799_);
v___x_5817_ = l_Array_toSubarray___redArg(v_a_5799_, v___x_5814_, v___x_5816_);
v___x_5818_ = lean_array_get_size(v_discrInfos_5813_);
v___x_5819_ = l_Array_toSubarray___redArg(v_discrInfos_5813_, v___x_5814_, v___x_5818_);
v___x_5820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5820_, 0, v___x_5817_);
lean_ctor_set(v___x_5820_, 1, v___x_5819_);
v___x_5821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5821_, 0, v_addHEqualities_5815_);
lean_ctor_set(v___x_5821_, 1, v___x_5820_);
v___x_5822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5822_, 0, v_addHEqualities_5815_);
lean_ctor_set(v___x_5822_, 1, v___x_5821_);
v___x_5823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5823_, 0, v_a_5812_);
lean_ctor_set(v___x_5823_, 1, v___x_5822_);
v_sz_5824_ = lean_array_size(v_motiveArgs_5803_);
v___x_5825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5800_, v_motiveArgs_5803_, v_sz_5824_, v___x_5801_, v___x_5823_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
if (lean_obj_tag(v___x_5825_) == 0)
{
lean_object* v_a_5826_; lean_object* v_snd_5827_; lean_object* v_snd_5828_; lean_object* v_fst_5829_; lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5884_; 
v_a_5826_ = lean_ctor_get(v___x_5825_, 0);
lean_inc(v_a_5826_);
lean_dec_ref_known(v___x_5825_, 1);
v_snd_5827_ = lean_ctor_get(v_a_5826_, 1);
lean_inc(v_snd_5827_);
v_snd_5828_ = lean_ctor_get(v_snd_5827_, 1);
lean_inc(v_snd_5828_);
v_fst_5829_ = lean_ctor_get(v_a_5826_, 0);
v_isSharedCheck_5884_ = !lean_is_exclusive(v_a_5826_);
if (v_isSharedCheck_5884_ == 0)
{
lean_object* v_unused_5885_; 
v_unused_5885_ = lean_ctor_get(v_a_5826_, 1);
lean_dec(v_unused_5885_);
v___x_5831_ = v_a_5826_;
v_isShared_5832_ = v_isSharedCheck_5884_;
goto v_resetjp_5830_;
}
else
{
lean_inc(v_fst_5829_);
lean_dec(v_a_5826_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5884_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v_fst_5833_; lean_object* v___x_5835_; uint8_t v_isShared_5836_; uint8_t v_isSharedCheck_5882_; 
v_fst_5833_ = lean_ctor_get(v_snd_5827_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v_snd_5827_);
if (v_isSharedCheck_5882_ == 0)
{
lean_object* v_unused_5883_; 
v_unused_5883_ = lean_ctor_get(v_snd_5827_, 1);
lean_dec(v_unused_5883_);
v___x_5835_ = v_snd_5827_;
v_isShared_5836_ = v_isSharedCheck_5882_;
goto v_resetjp_5834_;
}
else
{
lean_inc(v_fst_5833_);
lean_dec(v_snd_5827_);
v___x_5835_ = lean_box(0);
v_isShared_5836_ = v_isSharedCheck_5882_;
goto v_resetjp_5834_;
}
v_resetjp_5834_:
{
lean_object* v_fst_5837_; lean_object* v___x_5839_; uint8_t v_isShared_5840_; uint8_t v_isSharedCheck_5880_; 
v_fst_5837_ = lean_ctor_get(v_snd_5828_, 0);
v_isSharedCheck_5880_ = !lean_is_exclusive(v_snd_5828_);
if (v_isSharedCheck_5880_ == 0)
{
lean_object* v_unused_5881_; 
v_unused_5881_ = lean_ctor_get(v_snd_5828_, 1);
lean_dec(v_unused_5881_);
v___x_5839_ = v_snd_5828_;
v_isShared_5840_ = v_isSharedCheck_5880_;
goto v_resetjp_5838_;
}
else
{
lean_inc(v_fst_5837_);
lean_dec(v_snd_5828_);
v___x_5839_ = lean_box(0);
v_isShared_5840_ = v_isSharedCheck_5880_;
goto v_resetjp_5838_;
}
v_resetjp_5838_:
{
uint8_t v___x_5841_; uint8_t v___x_5842_; uint8_t v___x_5843_; lean_object* v___x_5844_; 
v___x_5841_ = 0;
v___x_5842_ = 1;
v___x_5843_ = 1;
lean_inc(v_fst_5829_);
v___x_5844_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5803_, v_fst_5829_, v___x_5841_, v___x_5842_, v___x_5841_, v___x_5842_, v___x_5843_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
lean_dec_ref(v_motiveArgs_5803_);
if (lean_obj_tag(v___x_5844_) == 0)
{
lean_object* v_a_5845_; lean_object* v___x_5846_; 
v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
lean_inc(v_a_5845_);
lean_dec_ref_known(v___x_5844_, 1);
v___x_5846_ = l_Lean_Meta_getLevel(v_fst_5829_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
if (lean_obj_tag(v___x_5846_) == 0)
{
lean_object* v_a_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5863_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5863_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5863_ == 0)
{
v___x_5849_ = v___x_5846_;
v_isShared_5850_ = v_isSharedCheck_5863_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_a_5847_);
lean_dec(v___x_5846_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5863_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5852_; 
if (v_isShared_5840_ == 0)
{
lean_ctor_set(v___x_5839_, 1, v_fst_5837_);
lean_ctor_set(v___x_5839_, 0, v_fst_5833_);
v___x_5852_ = v___x_5839_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5862_; 
v_reuseFailAlloc_5862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_fst_5833_);
lean_ctor_set(v_reuseFailAlloc_5862_, 1, v_fst_5837_);
v___x_5852_ = v_reuseFailAlloc_5862_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
lean_object* v___x_5854_; 
if (v_isShared_5836_ == 0)
{
lean_ctor_set(v___x_5835_, 1, v___x_5852_);
lean_ctor_set(v___x_5835_, 0, v_a_5847_);
v___x_5854_ = v___x_5835_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5861_; 
v_reuseFailAlloc_5861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5847_);
lean_ctor_set(v_reuseFailAlloc_5861_, 1, v___x_5852_);
v___x_5854_ = v_reuseFailAlloc_5861_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
lean_object* v___x_5856_; 
if (v_isShared_5832_ == 0)
{
lean_ctor_set(v___x_5831_, 1, v___x_5854_);
lean_ctor_set(v___x_5831_, 0, v_a_5845_);
v___x_5856_ = v___x_5831_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_a_5845_);
lean_ctor_set(v_reuseFailAlloc_5860_, 1, v___x_5854_);
v___x_5856_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
lean_object* v___x_5858_; 
if (v_isShared_5850_ == 0)
{
lean_ctor_set(v___x_5849_, 0, v___x_5856_);
v___x_5858_ = v___x_5849_;
goto v_reusejp_5857_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v___x_5856_);
v___x_5858_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5857_;
}
v_reusejp_5857_:
{
return v___x_5858_;
}
}
}
}
}
}
else
{
lean_object* v_a_5864_; lean_object* v___x_5866_; uint8_t v_isShared_5867_; uint8_t v_isSharedCheck_5871_; 
lean_dec(v_a_5845_);
lean_del_object(v___x_5839_);
lean_dec(v_fst_5837_);
lean_del_object(v___x_5835_);
lean_dec(v_fst_5833_);
lean_del_object(v___x_5831_);
v_a_5864_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_5871_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_5871_ == 0)
{
v___x_5866_ = v___x_5846_;
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
else
{
lean_inc(v_a_5864_);
lean_dec(v___x_5846_);
v___x_5866_ = lean_box(0);
v_isShared_5867_ = v_isSharedCheck_5871_;
goto v_resetjp_5865_;
}
v_resetjp_5865_:
{
lean_object* v___x_5869_; 
if (v_isShared_5867_ == 0)
{
v___x_5869_ = v___x_5866_;
goto v_reusejp_5868_;
}
else
{
lean_object* v_reuseFailAlloc_5870_; 
v_reuseFailAlloc_5870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5870_, 0, v_a_5864_);
v___x_5869_ = v_reuseFailAlloc_5870_;
goto v_reusejp_5868_;
}
v_reusejp_5868_:
{
return v___x_5869_;
}
}
}
}
else
{
lean_object* v_a_5872_; lean_object* v___x_5874_; uint8_t v_isShared_5875_; uint8_t v_isSharedCheck_5879_; 
lean_del_object(v___x_5839_);
lean_dec(v_fst_5837_);
lean_del_object(v___x_5835_);
lean_dec(v_fst_5833_);
lean_del_object(v___x_5831_);
lean_dec(v_fst_5829_);
v_a_5872_ = lean_ctor_get(v___x_5844_, 0);
v_isSharedCheck_5879_ = !lean_is_exclusive(v___x_5844_);
if (v_isSharedCheck_5879_ == 0)
{
v___x_5874_ = v___x_5844_;
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
else
{
lean_inc(v_a_5872_);
lean_dec(v___x_5844_);
v___x_5874_ = lean_box(0);
v_isShared_5875_ = v_isSharedCheck_5879_;
goto v_resetjp_5873_;
}
v_resetjp_5873_:
{
lean_object* v___x_5877_; 
if (v_isShared_5875_ == 0)
{
v___x_5877_ = v___x_5874_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5878_; 
v_reuseFailAlloc_5878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5878_, 0, v_a_5872_);
v___x_5877_ = v_reuseFailAlloc_5878_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
return v___x_5877_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5886_; lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5893_; 
lean_dec_ref(v_motiveArgs_5803_);
v_a_5886_ = lean_ctor_get(v___x_5825_, 0);
v_isSharedCheck_5893_ = !lean_is_exclusive(v___x_5825_);
if (v_isSharedCheck_5893_ == 0)
{
v___x_5888_ = v___x_5825_;
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
else
{
lean_inc(v_a_5886_);
lean_dec(v___x_5825_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v___x_5891_; 
if (v_isShared_5889_ == 0)
{
v___x_5891_ = v___x_5888_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5892_; 
v_reuseFailAlloc_5892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5892_, 0, v_a_5886_);
v___x_5891_ = v_reuseFailAlloc_5892_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
return v___x_5891_;
}
}
}
}
else
{
lean_object* v_a_5894_; lean_object* v___x_5896_; uint8_t v_isShared_5897_; uint8_t v_isSharedCheck_5901_; 
lean_dec_ref(v_motiveArgs_5803_);
lean_dec_ref(v_a_5799_);
lean_dec_ref(v_toMatcherInfo_5798_);
v_a_5894_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5901_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5901_ == 0)
{
v___x_5896_ = v___x_5811_;
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
else
{
lean_inc(v_a_5894_);
lean_dec(v___x_5811_);
v___x_5896_ = lean_box(0);
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
v_resetjp_5895_:
{
lean_object* v___x_5899_; 
if (v_isShared_5897_ == 0)
{
v___x_5899_ = v___x_5896_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_a_5894_);
v___x_5899_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
return v___x_5899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5921_, lean_object* v_toMatcherInfo_5922_, lean_object* v_a_5923_, lean_object* v_addEqualities_5924_, lean_object* v___x_5925_, lean_object* v_discrs_5926_, lean_object* v_motiveArgs_5927_, lean_object* v_motiveBody_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_, lean_object* v___y_5933_){
_start:
{
uint8_t v_addEqualities_boxed_5934_; size_t v___x_34551__boxed_5935_; lean_object* v_res_5936_; 
v_addEqualities_boxed_5934_ = lean_unbox(v_addEqualities_5924_);
v___x_34551__boxed_5935_ = lean_unbox_usize(v___x_5925_);
lean_dec(v___x_5925_);
v_res_5936_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5921_, v_toMatcherInfo_5922_, v_a_5923_, v_addEqualities_boxed_5934_, v___x_34551__boxed_5935_, v_discrs_5926_, v_motiveArgs_5927_, v_motiveBody_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
lean_dec(v___y_5932_);
lean_dec_ref(v___y_5931_);
lean_dec(v___y_5930_);
lean_dec_ref(v___y_5929_);
lean_dec_ref(v_discrs_5926_);
return v_res_5936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5937_, size_t v_sz_5938_, size_t v_i_5939_, lean_object* v_b_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_, lean_object* v___y_5943_, lean_object* v___y_5944_){
_start:
{
lean_object* v_a_5947_; uint8_t v___x_5951_; 
v___x_5951_ = lean_usize_dec_lt(v_i_5939_, v_sz_5938_);
if (v___x_5951_ == 0)
{
lean_object* v___x_5952_; 
v___x_5952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5952_, 0, v_b_5940_);
return v___x_5952_;
}
else
{
lean_object* v_snd_5953_; lean_object* v_snd_5954_; lean_object* v_fst_5955_; lean_object* v___x_5957_; uint8_t v_isShared_5958_; uint8_t v_isSharedCheck_6015_; 
v_snd_5953_ = lean_ctor_get(v_b_5940_, 1);
lean_inc(v_snd_5953_);
v_snd_5954_ = lean_ctor_get(v_snd_5953_, 1);
lean_inc(v_snd_5954_);
v_fst_5955_ = lean_ctor_get(v_b_5940_, 0);
v_isSharedCheck_6015_ = !lean_is_exclusive(v_b_5940_);
if (v_isSharedCheck_6015_ == 0)
{
lean_object* v_unused_6016_; 
v_unused_6016_ = lean_ctor_get(v_b_5940_, 1);
lean_dec(v_unused_6016_);
v___x_5957_ = v_b_5940_;
v_isShared_5958_ = v_isSharedCheck_6015_;
goto v_resetjp_5956_;
}
else
{
lean_inc(v_fst_5955_);
lean_dec(v_b_5940_);
v___x_5957_ = lean_box(0);
v_isShared_5958_ = v_isSharedCheck_6015_;
goto v_resetjp_5956_;
}
v_resetjp_5956_:
{
lean_object* v_fst_5959_; lean_object* v___x_5961_; uint8_t v_isShared_5962_; uint8_t v_isSharedCheck_6013_; 
v_fst_5959_ = lean_ctor_get(v_snd_5953_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v_snd_5953_);
if (v_isSharedCheck_6013_ == 0)
{
lean_object* v_unused_6014_; 
v_unused_6014_ = lean_ctor_get(v_snd_5953_, 1);
lean_dec(v_unused_6014_);
v___x_5961_ = v_snd_5953_;
v_isShared_5962_ = v_isSharedCheck_6013_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_fst_5959_);
lean_dec(v_snd_5953_);
v___x_5961_ = lean_box(0);
v_isShared_5962_ = v_isSharedCheck_6013_;
goto v_resetjp_5960_;
}
v_resetjp_5960_:
{
lean_object* v_array_5963_; lean_object* v_start_5964_; lean_object* v_stop_5965_; uint8_t v___x_5966_; 
v_array_5963_ = lean_ctor_get(v_snd_5954_, 0);
v_start_5964_ = lean_ctor_get(v_snd_5954_, 1);
v_stop_5965_ = lean_ctor_get(v_snd_5954_, 2);
v___x_5966_ = lean_nat_dec_lt(v_start_5964_, v_stop_5965_);
if (v___x_5966_ == 0)
{
lean_object* v___x_5968_; 
if (v_isShared_5962_ == 0)
{
v___x_5968_ = v___x_5961_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5973_; 
v_reuseFailAlloc_5973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5973_, 0, v_fst_5959_);
lean_ctor_set(v_reuseFailAlloc_5973_, 1, v_snd_5954_);
v___x_5968_ = v_reuseFailAlloc_5973_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5970_; 
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5968_);
v___x_5970_ = v___x_5957_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_fst_5955_);
lean_ctor_set(v_reuseFailAlloc_5972_, 1, v___x_5968_);
v___x_5970_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5969_;
}
v_reusejp_5969_:
{
lean_object* v___x_5971_; 
v___x_5971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5970_);
return v___x_5971_;
}
}
}
else
{
lean_object* v___x_5975_; uint8_t v_isShared_5976_; uint8_t v_isSharedCheck_6009_; 
lean_inc(v_stop_5965_);
lean_inc(v_start_5964_);
lean_inc_ref(v_array_5963_);
v_isSharedCheck_6009_ = !lean_is_exclusive(v_snd_5954_);
if (v_isSharedCheck_6009_ == 0)
{
lean_object* v_unused_6010_; lean_object* v_unused_6011_; lean_object* v_unused_6012_; 
v_unused_6010_ = lean_ctor_get(v_snd_5954_, 2);
lean_dec(v_unused_6010_);
v_unused_6011_ = lean_ctor_get(v_snd_5954_, 1);
lean_dec(v_unused_6011_);
v_unused_6012_ = lean_ctor_get(v_snd_5954_, 0);
lean_dec(v_unused_6012_);
v___x_5975_ = v_snd_5954_;
v_isShared_5976_ = v_isSharedCheck_6009_;
goto v_resetjp_5974_;
}
else
{
lean_dec(v_snd_5954_);
v___x_5975_ = lean_box(0);
v_isShared_5976_ = v_isSharedCheck_6009_;
goto v_resetjp_5974_;
}
v_resetjp_5974_:
{
lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5981_; 
v___x_5977_ = lean_array_fget(v_array_5963_, v_start_5964_);
v___x_5978_ = lean_unsigned_to_nat(1u);
v___x_5979_ = lean_nat_add(v_start_5964_, v___x_5978_);
lean_dec(v_start_5964_);
if (v_isShared_5976_ == 0)
{
lean_ctor_set(v___x_5975_, 1, v___x_5979_);
v___x_5981_ = v___x_5975_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_6008_; 
v_reuseFailAlloc_6008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6008_, 0, v_array_5963_);
lean_ctor_set(v_reuseFailAlloc_6008_, 1, v___x_5979_);
lean_ctor_set(v_reuseFailAlloc_6008_, 2, v_stop_5965_);
v___x_5981_ = v_reuseFailAlloc_6008_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
lean_object* v___y_5983_; 
if (lean_obj_tag(v___x_5977_) == 0)
{
lean_object* v___x_6001_; lean_object* v___x_6002_; 
lean_del_object(v___x_5961_);
lean_del_object(v___x_5957_);
v___x_6001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6001_, 0, v_fst_5959_);
lean_ctor_set(v___x_6001_, 1, v___x_5981_);
v___x_6002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6002_, 0, v_fst_5955_);
lean_ctor_set(v___x_6002_, 1, v___x_6001_);
v_a_5947_ = v___x_6002_;
goto v___jp_5946_;
}
else
{
lean_object* v_val_6003_; lean_object* v_a_6004_; uint8_t v___x_6005_; 
v_val_6003_ = lean_ctor_get(v___x_5977_, 0);
lean_inc(v_val_6003_);
lean_dec_ref_known(v___x_5977_, 1);
v_a_6004_ = lean_array_uget_borrowed(v_as_5937_, v_i_5939_);
v___x_6005_ = lean_unbox(v_val_6003_);
lean_dec(v_val_6003_);
if (v___x_6005_ == 0)
{
lean_object* v___x_6006_; 
lean_inc(v_a_6004_);
v___x_6006_ = l_Lean_Meta_mkEqRefl(v_a_6004_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
v___y_5983_ = v___x_6006_;
goto v___jp_5982_;
}
else
{
lean_object* v___x_6007_; 
lean_inc(v_a_6004_);
v___x_6007_ = l_Lean_Meta_mkHEqRefl(v_a_6004_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
v___y_5983_ = v___x_6007_;
goto v___jp_5982_;
}
}
v___jp_5982_:
{
if (lean_obj_tag(v___y_5983_) == 0)
{
lean_object* v_a_5984_; lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5988_; 
v_a_5984_ = lean_ctor_get(v___y_5983_, 0);
lean_inc(v_a_5984_);
lean_dec_ref_known(v___y_5983_, 1);
v___x_5985_ = lean_array_push(v_fst_5955_, v_a_5984_);
v___x_5986_ = lean_nat_add(v_fst_5959_, v___x_5978_);
lean_dec(v_fst_5959_);
if (v_isShared_5962_ == 0)
{
lean_ctor_set(v___x_5961_, 1, v___x_5981_);
lean_ctor_set(v___x_5961_, 0, v___x_5986_);
v___x_5988_ = v___x_5961_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5986_);
lean_ctor_set(v_reuseFailAlloc_5992_, 1, v___x_5981_);
v___x_5988_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
lean_object* v___x_5990_; 
if (v_isShared_5958_ == 0)
{
lean_ctor_set(v___x_5957_, 1, v___x_5988_);
lean_ctor_set(v___x_5957_, 0, v___x_5985_);
v___x_5990_ = v___x_5957_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v___x_5985_);
lean_ctor_set(v_reuseFailAlloc_5991_, 1, v___x_5988_);
v___x_5990_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
v_a_5947_ = v___x_5990_;
goto v___jp_5946_;
}
}
}
else
{
lean_object* v_a_5993_; lean_object* v___x_5995_; uint8_t v_isShared_5996_; uint8_t v_isSharedCheck_6000_; 
lean_dec_ref(v___x_5981_);
lean_del_object(v___x_5961_);
lean_dec(v_fst_5959_);
lean_del_object(v___x_5957_);
lean_dec(v_fst_5955_);
v_a_5993_ = lean_ctor_get(v___y_5983_, 0);
v_isSharedCheck_6000_ = !lean_is_exclusive(v___y_5983_);
if (v_isSharedCheck_6000_ == 0)
{
v___x_5995_ = v___y_5983_;
v_isShared_5996_ = v_isSharedCheck_6000_;
goto v_resetjp_5994_;
}
else
{
lean_inc(v_a_5993_);
lean_dec(v___y_5983_);
v___x_5995_ = lean_box(0);
v_isShared_5996_ = v_isSharedCheck_6000_;
goto v_resetjp_5994_;
}
v_resetjp_5994_:
{
lean_object* v___x_5998_; 
if (v_isShared_5996_ == 0)
{
v___x_5998_ = v___x_5995_;
goto v_reusejp_5997_;
}
else
{
lean_object* v_reuseFailAlloc_5999_; 
v_reuseFailAlloc_5999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5993_);
v___x_5998_ = v_reuseFailAlloc_5999_;
goto v_reusejp_5997_;
}
v_reusejp_5997_:
{
return v___x_5998_;
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
v___jp_5946_:
{
size_t v___x_5948_; size_t v___x_5949_; 
v___x_5948_ = ((size_t)1ULL);
v___x_5949_ = lean_usize_add(v_i_5939_, v___x_5948_);
v_i_5939_ = v___x_5949_;
v_b_5940_ = v_a_5947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6017_, lean_object* v_sz_6018_, lean_object* v_i_6019_, lean_object* v_b_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_){
_start:
{
size_t v_sz_boxed_6026_; size_t v_i_boxed_6027_; lean_object* v_res_6028_; 
v_sz_boxed_6026_ = lean_unbox_usize(v_sz_6018_);
lean_dec(v_sz_6018_);
v_i_boxed_6027_ = lean_unbox_usize(v_i_6019_);
lean_dec(v_i_6019_);
v_res_6028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6017_, v_sz_boxed_6026_, v_i_boxed_6027_, v_b_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
lean_dec(v___y_6024_);
lean_dec_ref(v___y_6023_);
lean_dec(v___y_6022_);
lean_dec_ref(v___y_6021_);
lean_dec_ref(v_as_6017_);
return v_res_6028_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_, lean_object* v___y_6033_){
_start:
{
lean_object* v___x_6035_; 
v___x_6035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6029_);
return v___x_6035_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
lean_object* v_res_6042_; 
v_res_6042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_);
lean_dec(v___y_6040_);
lean_dec_ref(v___y_6039_);
lean_dec(v___y_6038_);
lean_dec_ref(v___y_6037_);
return v_res_6042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6043_, size_t v_i_6044_, lean_object* v_bs_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_){
_start:
{
uint8_t v___x_6050_; 
v___x_6050_ = lean_usize_dec_lt(v_i_6044_, v_sz_6043_);
if (v___x_6050_ == 0)
{
lean_object* v___x_6051_; 
v___x_6051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6051_, 0, v_bs_6045_);
return v___x_6051_;
}
else
{
lean_object* v_v_6052_; lean_object* v___x_6053_; lean_object* v_bs_x27_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; 
v_v_6052_ = lean_array_uget(v_bs_6045_, v_i_6044_);
v___x_6053_ = lean_unsigned_to_nat(0u);
v_bs_x27_6054_ = lean_array_uset(v_bs_6045_, v_i_6044_, v___x_6053_);
v___x_6055_ = l_Lean_Expr_fvarId_x21(v_v_6052_);
lean_dec(v_v_6052_);
v___x_6056_ = l_Lean_FVarId_getUserName___redArg(v___x_6055_, v___y_6046_, v___y_6047_, v___y_6048_);
if (lean_obj_tag(v___x_6056_) == 0)
{
lean_object* v_a_6057_; size_t v___x_6058_; size_t v___x_6059_; lean_object* v___x_6060_; 
v_a_6057_ = lean_ctor_get(v___x_6056_, 0);
lean_inc(v_a_6057_);
lean_dec_ref_known(v___x_6056_, 1);
v___x_6058_ = ((size_t)1ULL);
v___x_6059_ = lean_usize_add(v_i_6044_, v___x_6058_);
v___x_6060_ = lean_array_uset(v_bs_x27_6054_, v_i_6044_, v_a_6057_);
v_i_6044_ = v___x_6059_;
v_bs_6045_ = v___x_6060_;
goto _start;
}
else
{
lean_object* v_a_6062_; lean_object* v___x_6064_; uint8_t v_isShared_6065_; uint8_t v_isSharedCheck_6069_; 
lean_dec_ref(v_bs_x27_6054_);
v_a_6062_ = lean_ctor_get(v___x_6056_, 0);
v_isSharedCheck_6069_ = !lean_is_exclusive(v___x_6056_);
if (v_isSharedCheck_6069_ == 0)
{
v___x_6064_ = v___x_6056_;
v_isShared_6065_ = v_isSharedCheck_6069_;
goto v_resetjp_6063_;
}
else
{
lean_inc(v_a_6062_);
lean_dec(v___x_6056_);
v___x_6064_ = lean_box(0);
v_isShared_6065_ = v_isSharedCheck_6069_;
goto v_resetjp_6063_;
}
v_resetjp_6063_:
{
lean_object* v___x_6067_; 
if (v_isShared_6065_ == 0)
{
v___x_6067_ = v___x_6064_;
goto v_reusejp_6066_;
}
else
{
lean_object* v_reuseFailAlloc_6068_; 
v_reuseFailAlloc_6068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6068_, 0, v_a_6062_);
v___x_6067_ = v_reuseFailAlloc_6068_;
goto v_reusejp_6066_;
}
v_reusejp_6066_:
{
return v___x_6067_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6070_, lean_object* v_i_6071_, lean_object* v_bs_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_){
_start:
{
size_t v_sz_boxed_6077_; size_t v_i_boxed_6078_; lean_object* v_res_6079_; 
v_sz_boxed_6077_ = lean_unbox_usize(v_sz_6070_);
lean_dec(v_sz_6070_);
v_i_boxed_6078_ = lean_unbox_usize(v_i_6071_);
lean_dec(v_i_6071_);
v_res_6079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6077_, v_i_boxed_6078_, v_bs_6072_, v___y_6073_, v___y_6074_, v___y_6075_);
lean_dec(v___y_6075_);
lean_dec_ref(v___y_6074_);
lean_dec_ref(v___y_6073_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6080_, lean_object* v_x_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_){
_start:
{
size_t v_sz_6087_; size_t v___x_6088_; lean_object* v___x_6089_; 
v_sz_6087_ = lean_array_size(v_xs_6080_);
v___x_6088_ = ((size_t)0ULL);
v___x_6089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6087_, v___x_6088_, v_xs_6080_, v___y_6082_, v___y_6084_, v___y_6085_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6090_, lean_object* v_x_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_){
_start:
{
lean_object* v_res_6097_; 
v_res_6097_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6090_, v_x_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
lean_dec(v___y_6095_);
lean_dec_ref(v___y_6094_);
lean_dec(v___y_6093_);
lean_dec_ref(v___y_6092_);
lean_dec_ref(v_x_6091_);
return v_res_6097_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6098_, lean_object* v___x_6099_, lean_object* v___f_6100_, uint8_t v___x_6101_, lean_object* v_fst_6102_, lean_object* v___x_6103_, lean_object* v___x_6104_, lean_object* v___x_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_, lean_object* v___y_6108_, lean_object* v___y_6109_){
_start:
{
lean_object* v___x_6111_; 
v___x_6111_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v___x_6098_, v___x_6099_, v___f_6100_, v___x_6101_, v___x_6101_, v___y_6106_, v___y_6107_, v___y_6108_, v___y_6109_);
if (lean_obj_tag(v___x_6111_) == 0)
{
lean_object* v_a_6112_; lean_object* v___x_6114_; uint8_t v_isShared_6115_; uint8_t v_isSharedCheck_6124_; 
v_a_6112_ = lean_ctor_get(v___x_6111_, 0);
v_isSharedCheck_6124_ = !lean_is_exclusive(v___x_6111_);
if (v_isSharedCheck_6124_ == 0)
{
v___x_6114_ = v___x_6111_;
v_isShared_6115_ = v_isSharedCheck_6124_;
goto v_resetjp_6113_;
}
else
{
lean_inc(v_a_6112_);
lean_dec(v___x_6111_);
v___x_6114_ = lean_box(0);
v_isShared_6115_ = v_isSharedCheck_6124_;
goto v_resetjp_6113_;
}
v_resetjp_6113_:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6122_; 
v___x_6116_ = lean_array_push(v_fst_6102_, v_a_6112_);
v___x_6117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6103_);
lean_ctor_set(v___x_6117_, 1, v___x_6104_);
v___x_6118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6105_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6119_, 0, v___x_6116_);
lean_ctor_set(v___x_6119_, 1, v___x_6118_);
v___x_6120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6119_);
if (v_isShared_6115_ == 0)
{
lean_ctor_set(v___x_6114_, 0, v___x_6120_);
v___x_6122_ = v___x_6114_;
goto v_reusejp_6121_;
}
else
{
lean_object* v_reuseFailAlloc_6123_; 
v_reuseFailAlloc_6123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6123_, 0, v___x_6120_);
v___x_6122_ = v_reuseFailAlloc_6123_;
goto v_reusejp_6121_;
}
v_reusejp_6121_:
{
return v___x_6122_;
}
}
}
else
{
lean_object* v_a_6125_; lean_object* v___x_6127_; uint8_t v_isShared_6128_; uint8_t v_isSharedCheck_6132_; 
lean_dec_ref(v___x_6105_);
lean_dec_ref(v___x_6104_);
lean_dec_ref(v___x_6103_);
lean_dec(v_fst_6102_);
v_a_6125_ = lean_ctor_get(v___x_6111_, 0);
v_isSharedCheck_6132_ = !lean_is_exclusive(v___x_6111_);
if (v_isSharedCheck_6132_ == 0)
{
v___x_6127_ = v___x_6111_;
v_isShared_6128_ = v_isSharedCheck_6132_;
goto v_resetjp_6126_;
}
else
{
lean_inc(v_a_6125_);
lean_dec(v___x_6111_);
v___x_6127_ = lean_box(0);
v_isShared_6128_ = v_isSharedCheck_6132_;
goto v_resetjp_6126_;
}
v_resetjp_6126_:
{
lean_object* v___x_6130_; 
if (v_isShared_6128_ == 0)
{
v___x_6130_ = v___x_6127_;
goto v_reusejp_6129_;
}
else
{
lean_object* v_reuseFailAlloc_6131_; 
v_reuseFailAlloc_6131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6131_, 0, v_a_6125_);
v___x_6130_ = v_reuseFailAlloc_6131_;
goto v_reusejp_6129_;
}
v_reusejp_6129_:
{
return v___x_6130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6133_, lean_object* v___x_6134_, lean_object* v___f_6135_, lean_object* v___x_6136_, lean_object* v_fst_6137_, lean_object* v___x_6138_, lean_object* v___x_6139_, lean_object* v___x_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_){
_start:
{
uint8_t v___x_35014__boxed_6146_; lean_object* v_res_6147_; 
v___x_35014__boxed_6146_ = lean_unbox(v___x_6136_);
v_res_6147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6133_, v___x_6134_, v___f_6135_, v___x_35014__boxed_6146_, v_fst_6137_, v___x_6138_, v___x_6139_, v___x_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_);
lean_dec(v___y_6144_);
lean_dec_ref(v___y_6143_);
lean_dec(v___y_6142_);
lean_dec_ref(v___y_6141_);
return v_res_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6148_, lean_object* v_names_6149_, lean_object* v_k_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_){
_start:
{
lean_object* v___x_6156_; 
v___x_6156_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6148_, v_names_6149_, v_k_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_);
if (lean_obj_tag(v___x_6156_) == 0)
{
lean_object* v_a_6157_; lean_object* v___x_6159_; uint8_t v_isShared_6160_; uint8_t v_isSharedCheck_6164_; 
v_a_6157_ = lean_ctor_get(v___x_6156_, 0);
v_isSharedCheck_6164_ = !lean_is_exclusive(v___x_6156_);
if (v_isSharedCheck_6164_ == 0)
{
v___x_6159_ = v___x_6156_;
v_isShared_6160_ = v_isSharedCheck_6164_;
goto v_resetjp_6158_;
}
else
{
lean_inc(v_a_6157_);
lean_dec(v___x_6156_);
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
v_reuseFailAlloc_6163_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_6165_; lean_object* v___x_6167_; uint8_t v_isShared_6168_; uint8_t v_isSharedCheck_6172_; 
v_a_6165_ = lean_ctor_get(v___x_6156_, 0);
v_isSharedCheck_6172_ = !lean_is_exclusive(v___x_6156_);
if (v_isSharedCheck_6172_ == 0)
{
v___x_6167_ = v___x_6156_;
v_isShared_6168_ = v_isSharedCheck_6172_;
goto v_resetjp_6166_;
}
else
{
lean_inc(v_a_6165_);
lean_dec(v___x_6156_);
v___x_6167_ = lean_box(0);
v_isShared_6168_ = v_isSharedCheck_6172_;
goto v_resetjp_6166_;
}
v_resetjp_6166_:
{
lean_object* v___x_6170_; 
if (v_isShared_6168_ == 0)
{
v___x_6170_ = v___x_6167_;
goto v_reusejp_6169_;
}
else
{
lean_object* v_reuseFailAlloc_6171_; 
v_reuseFailAlloc_6171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_a_6165_);
v___x_6170_ = v_reuseFailAlloc_6171_;
goto v_reusejp_6169_;
}
v_reusejp_6169_:
{
return v___x_6170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6173_, lean_object* v_names_6174_, lean_object* v_k_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_){
_start:
{
lean_object* v_res_6181_; 
v_res_6181_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6173_, v_names_6174_, v_k_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec_ref(v_names_6174_);
lean_dec_ref(v_fvars_6173_);
return v_res_6181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6182_, lean_object* v_xs_6183_, lean_object* v_remaining_x27_6184_, lean_object* v_ys4_6185_, lean_object* v_onAlt_6186_, lean_object* v_a_6187_, lean_object* v_altType_6188_, uint8_t v___x_6189_, uint8_t v___x_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
lean_object* v___x_6196_; 
v___x_6196_ = l_Lean_Meta_instantiateLambda(v___x_6182_, v_xs_6183_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_);
if (lean_obj_tag(v___x_6196_) == 0)
{
lean_object* v_a_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; 
v_a_6197_ = lean_ctor_get(v___x_6196_, 0);
lean_inc(v_a_6197_);
lean_dec_ref_known(v___x_6196_, 1);
lean_inc_ref(v_ys4_6185_);
lean_inc_ref(v_remaining_x27_6184_);
lean_inc_ref_n(v_xs_6183_, 2);
v___x_6198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6198_, 0, v_xs_6183_);
lean_ctor_set(v___x_6198_, 1, v_xs_6183_);
lean_ctor_set(v___x_6198_, 2, v_remaining_x27_6184_);
lean_ctor_set(v___x_6198_, 3, v_remaining_x27_6184_);
lean_ctor_set(v___x_6198_, 4, v_ys4_6185_);
lean_inc(v___y_6194_);
lean_inc_ref(v___y_6193_);
lean_inc(v___y_6192_);
lean_inc_ref(v___y_6191_);
v___x_6199_ = lean_apply_9(v_onAlt_6186_, v_a_6187_, v_altType_6188_, v___x_6198_, v_a_6197_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_, lean_box(0));
if (lean_obj_tag(v___x_6199_) == 0)
{
lean_object* v_a_6200_; lean_object* v___x_6201_; uint8_t v___x_6202_; lean_object* v___x_6203_; 
v_a_6200_ = lean_ctor_get(v___x_6199_, 0);
lean_inc(v_a_6200_);
lean_dec_ref_known(v___x_6199_, 1);
v___x_6201_ = l_Array_append___redArg(v_xs_6183_, v_ys4_6185_);
lean_dec_ref(v_ys4_6185_);
v___x_6202_ = 1;
v___x_6203_ = l_Lean_Meta_mkLambdaFVars(v___x_6201_, v_a_6200_, v___x_6189_, v___x_6190_, v___x_6189_, v___x_6190_, v___x_6202_, v___y_6191_, v___y_6192_, v___y_6193_, v___y_6194_);
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6193_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec_ref(v___x_6201_);
return v___x_6203_;
}
else
{
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6193_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec_ref(v_ys4_6185_);
lean_dec_ref(v_xs_6183_);
return v___x_6199_;
}
}
else
{
lean_dec(v___y_6194_);
lean_dec_ref(v___y_6193_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec_ref(v_altType_6188_);
lean_dec(v_a_6187_);
lean_dec_ref(v_onAlt_6186_);
lean_dec_ref(v_ys4_6185_);
lean_dec_ref(v_remaining_x27_6184_);
lean_dec_ref(v_xs_6183_);
return v___x_6196_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6204_, lean_object* v_xs_6205_, lean_object* v_remaining_x27_6206_, lean_object* v_ys4_6207_, lean_object* v_onAlt_6208_, lean_object* v_a_6209_, lean_object* v_altType_6210_, lean_object* v___x_6211_, lean_object* v___x_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_){
_start:
{
uint8_t v___x_35141__boxed_6218_; uint8_t v___x_35142__boxed_6219_; lean_object* v_res_6220_; 
v___x_35141__boxed_6218_ = lean_unbox(v___x_6211_);
v___x_35142__boxed_6219_ = lean_unbox(v___x_6212_);
v_res_6220_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6204_, v_xs_6205_, v_remaining_x27_6206_, v_ys4_6207_, v_onAlt_6208_, v_a_6209_, v_altType_6210_, v___x_35141__boxed_6218_, v___x_35142__boxed_6219_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_);
return v_res_6220_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6221_, lean_object* v_xs_6222_, lean_object* v_remaining_x27_6223_, lean_object* v_onAlt_6224_, lean_object* v_a_6225_, uint8_t v___x_6226_, uint8_t v___x_6227_, lean_object* v___f_6228_, lean_object* v_ys4_6229_, lean_object* v_altType_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_, lean_object* v___y_6234_){
_start:
{
lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___f_6238_; lean_object* v___x_6239_; 
v___x_6236_ = lean_box(v___x_6226_);
v___x_6237_ = lean_box(v___x_6227_);
lean_inc_ref(v_xs_6222_);
lean_inc_ref(v___x_6221_);
v___f_6238_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6238_, 0, v___x_6221_);
lean_closure_set(v___f_6238_, 1, v_xs_6222_);
lean_closure_set(v___f_6238_, 2, v_remaining_x27_6223_);
lean_closure_set(v___f_6238_, 3, v_ys4_6229_);
lean_closure_set(v___f_6238_, 4, v_onAlt_6224_);
lean_closure_set(v___f_6238_, 5, v_a_6225_);
lean_closure_set(v___f_6238_, 6, v_altType_6230_);
lean_closure_set(v___f_6238_, 7, v___x_6236_);
lean_closure_set(v___f_6238_, 8, v___x_6237_);
v___x_6239_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6221_, v___f_6228_, v___x_6226_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
if (lean_obj_tag(v___x_6239_) == 0)
{
lean_object* v_a_6240_; lean_object* v___x_6241_; 
v_a_6240_ = lean_ctor_get(v___x_6239_, 0);
lean_inc(v_a_6240_);
lean_dec_ref_known(v___x_6239_, 1);
v___x_6241_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6222_, v_a_6240_, v___f_6238_, v___y_6231_, v___y_6232_, v___y_6233_, v___y_6234_);
lean_dec(v_a_6240_);
lean_dec_ref(v_xs_6222_);
return v___x_6241_;
}
else
{
lean_object* v_a_6242_; lean_object* v___x_6244_; uint8_t v_isShared_6245_; uint8_t v_isSharedCheck_6249_; 
lean_dec_ref(v___f_6238_);
lean_dec_ref(v_xs_6222_);
v_a_6242_ = lean_ctor_get(v___x_6239_, 0);
v_isSharedCheck_6249_ = !lean_is_exclusive(v___x_6239_);
if (v_isSharedCheck_6249_ == 0)
{
v___x_6244_ = v___x_6239_;
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
else
{
lean_inc(v_a_6242_);
lean_dec(v___x_6239_);
v___x_6244_ = lean_box(0);
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
v_resetjp_6243_:
{
lean_object* v___x_6247_; 
if (v_isShared_6245_ == 0)
{
v___x_6247_ = v___x_6244_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6248_; 
v_reuseFailAlloc_6248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_a_6242_);
v___x_6247_ = v_reuseFailAlloc_6248_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
return v___x_6247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6250_, lean_object* v_xs_6251_, lean_object* v_remaining_x27_6252_, lean_object* v_onAlt_6253_, lean_object* v_a_6254_, lean_object* v___x_6255_, lean_object* v___x_6256_, lean_object* v___f_6257_, lean_object* v_ys4_6258_, lean_object* v_altType_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_){
_start:
{
uint8_t v___x_35183__boxed_6265_; uint8_t v___x_35184__boxed_6266_; lean_object* v_res_6267_; 
v___x_35183__boxed_6265_ = lean_unbox(v___x_6255_);
v___x_35184__boxed_6266_ = lean_unbox(v___x_6256_);
v_res_6267_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6250_, v_xs_6251_, v_remaining_x27_6252_, v_onAlt_6253_, v_a_6254_, v___x_35183__boxed_6265_, v___x_35184__boxed_6266_, v___f_6257_, v_ys4_6258_, v_altType_6259_, v___y_6260_, v___y_6261_, v___y_6262_, v___y_6263_);
lean_dec(v___y_6263_);
lean_dec_ref(v___y_6262_);
lean_dec(v___y_6261_);
lean_dec_ref(v___y_6260_);
return v_res_6267_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6268_, lean_object* v_remaining_x27_6269_, lean_object* v_onAlt_6270_, lean_object* v_a_6271_, uint8_t v___x_6272_, uint8_t v___x_6273_, lean_object* v___f_6274_, lean_object* v_extraEqualities_6275_, lean_object* v_xs_6276_, lean_object* v_altType_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_, lean_object* v___y_6280_, lean_object* v___y_6281_){
_start:
{
lean_object* v___x_6283_; lean_object* v___x_6284_; lean_object* v___f_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; 
v___x_6283_ = lean_box(v___x_6272_);
v___x_6284_ = lean_box(v___x_6273_);
v___f_6285_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6285_, 0, v___x_6268_);
lean_closure_set(v___f_6285_, 1, v_xs_6276_);
lean_closure_set(v___f_6285_, 2, v_remaining_x27_6269_);
lean_closure_set(v___f_6285_, 3, v_onAlt_6270_);
lean_closure_set(v___f_6285_, 4, v_a_6271_);
lean_closure_set(v___f_6285_, 5, v___x_6283_);
lean_closure_set(v___f_6285_, 6, v___x_6284_);
lean_closure_set(v___f_6285_, 7, v___f_6274_);
v___x_6286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6286_, 0, v_extraEqualities_6275_);
v___x_6287_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_6277_, v___x_6286_, v___f_6285_, v___x_6272_, v___x_6272_, v___y_6278_, v___y_6279_, v___y_6280_, v___y_6281_);
return v___x_6287_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6288_, lean_object* v_remaining_x27_6289_, lean_object* v_onAlt_6290_, lean_object* v_a_6291_, lean_object* v___x_6292_, lean_object* v___x_6293_, lean_object* v___f_6294_, lean_object* v_extraEqualities_6295_, lean_object* v_xs_6296_, lean_object* v_altType_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_){
_start:
{
uint8_t v___x_35238__boxed_6303_; uint8_t v___x_35239__boxed_6304_; lean_object* v_res_6305_; 
v___x_35238__boxed_6303_ = lean_unbox(v___x_6292_);
v___x_35239__boxed_6304_ = lean_unbox(v___x_6293_);
v_res_6305_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6288_, v_remaining_x27_6289_, v_onAlt_6290_, v_a_6291_, v___x_35238__boxed_6303_, v___x_35239__boxed_6304_, v___f_6294_, v_extraEqualities_6295_, v_xs_6296_, v_altType_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_);
lean_dec(v___y_6301_);
lean_dec_ref(v___y_6300_);
lean_dec(v___y_6299_);
lean_dec_ref(v___y_6298_);
return v_res_6305_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6307_, lean_object* v_onAlt_6308_, lean_object* v_extraEqualities_6309_, lean_object* v_a_6310_, lean_object* v_b_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_, lean_object* v___y_6314_, lean_object* v___y_6315_){
_start:
{
lean_object* v___y_6318_; uint8_t v___x_6341_; 
v___x_6341_ = lean_nat_dec_lt(v_a_6310_, v_upperBound_6307_);
if (v___x_6341_ == 0)
{
lean_object* v___x_6342_; 
lean_dec(v_a_6310_);
lean_dec(v_extraEqualities_6309_);
lean_dec_ref(v_onAlt_6308_);
v___x_6342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6342_, 0, v_b_6311_);
return v___x_6342_;
}
else
{
lean_object* v_snd_6343_; lean_object* v_snd_6344_; lean_object* v_snd_6345_; lean_object* v_fst_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6453_; 
v_snd_6343_ = lean_ctor_get(v_b_6311_, 1);
lean_inc(v_snd_6343_);
v_snd_6344_ = lean_ctor_get(v_snd_6343_, 1);
lean_inc(v_snd_6344_);
v_snd_6345_ = lean_ctor_get(v_snd_6344_, 1);
lean_inc(v_snd_6345_);
v_fst_6346_ = lean_ctor_get(v_b_6311_, 0);
v_isSharedCheck_6453_ = !lean_is_exclusive(v_b_6311_);
if (v_isSharedCheck_6453_ == 0)
{
lean_object* v_unused_6454_; 
v_unused_6454_ = lean_ctor_get(v_b_6311_, 1);
lean_dec(v_unused_6454_);
v___x_6348_ = v_b_6311_;
v_isShared_6349_ = v_isSharedCheck_6453_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_fst_6346_);
lean_dec(v_b_6311_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6453_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
lean_object* v_fst_6350_; lean_object* v___x_6352_; uint8_t v_isShared_6353_; uint8_t v_isSharedCheck_6451_; 
v_fst_6350_ = lean_ctor_get(v_snd_6343_, 0);
v_isSharedCheck_6451_ = !lean_is_exclusive(v_snd_6343_);
if (v_isSharedCheck_6451_ == 0)
{
lean_object* v_unused_6452_; 
v_unused_6452_ = lean_ctor_get(v_snd_6343_, 1);
lean_dec(v_unused_6452_);
v___x_6352_ = v_snd_6343_;
v_isShared_6353_ = v_isSharedCheck_6451_;
goto v_resetjp_6351_;
}
else
{
lean_inc(v_fst_6350_);
lean_dec(v_snd_6343_);
v___x_6352_ = lean_box(0);
v_isShared_6353_ = v_isSharedCheck_6451_;
goto v_resetjp_6351_;
}
v_resetjp_6351_:
{
lean_object* v_fst_6354_; lean_object* v___x_6356_; uint8_t v_isShared_6357_; uint8_t v_isSharedCheck_6449_; 
v_fst_6354_ = lean_ctor_get(v_snd_6344_, 0);
v_isSharedCheck_6449_ = !lean_is_exclusive(v_snd_6344_);
if (v_isSharedCheck_6449_ == 0)
{
lean_object* v_unused_6450_; 
v_unused_6450_ = lean_ctor_get(v_snd_6344_, 1);
lean_dec(v_unused_6450_);
v___x_6356_ = v_snd_6344_;
v_isShared_6357_ = v_isSharedCheck_6449_;
goto v_resetjp_6355_;
}
else
{
lean_inc(v_fst_6354_);
lean_dec(v_snd_6344_);
v___x_6356_ = lean_box(0);
v_isShared_6357_ = v_isSharedCheck_6449_;
goto v_resetjp_6355_;
}
v_resetjp_6355_:
{
lean_object* v_array_6358_; lean_object* v_start_6359_; lean_object* v_stop_6360_; uint8_t v___x_6361_; 
v_array_6358_ = lean_ctor_get(v_snd_6345_, 0);
v_start_6359_ = lean_ctor_get(v_snd_6345_, 1);
v_stop_6360_ = lean_ctor_get(v_snd_6345_, 2);
v___x_6361_ = lean_nat_dec_lt(v_start_6359_, v_stop_6360_);
if (v___x_6361_ == 0)
{
lean_object* v___x_6363_; 
if (v_isShared_6357_ == 0)
{
v___x_6363_ = v___x_6356_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6372_; 
v_reuseFailAlloc_6372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_fst_6354_);
lean_ctor_set(v_reuseFailAlloc_6372_, 1, v_snd_6345_);
v___x_6363_ = v_reuseFailAlloc_6372_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
lean_object* v___x_6365_; 
if (v_isShared_6353_ == 0)
{
lean_ctor_set(v___x_6352_, 1, v___x_6363_);
v___x_6365_ = v___x_6352_;
goto v_reusejp_6364_;
}
else
{
lean_object* v_reuseFailAlloc_6371_; 
v_reuseFailAlloc_6371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6371_, 0, v_fst_6350_);
lean_ctor_set(v_reuseFailAlloc_6371_, 1, v___x_6363_);
v___x_6365_ = v_reuseFailAlloc_6371_;
goto v_reusejp_6364_;
}
v_reusejp_6364_:
{
lean_object* v___x_6367_; 
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 1, v___x_6365_);
v___x_6367_ = v___x_6348_;
goto v_reusejp_6366_;
}
else
{
lean_object* v_reuseFailAlloc_6370_; 
v_reuseFailAlloc_6370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6370_, 0, v_fst_6346_);
lean_ctor_set(v_reuseFailAlloc_6370_, 1, v___x_6365_);
v___x_6367_ = v_reuseFailAlloc_6370_;
goto v_reusejp_6366_;
}
v_reusejp_6366_:
{
lean_object* v___x_6368_; lean_object* v___f_6369_; 
v___x_6368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6368_, 0, v___x_6367_);
v___f_6369_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6369_, 0, v___x_6368_);
v___y_6318_ = v___f_6369_;
goto v___jp_6317_;
}
}
}
}
else
{
lean_object* v___x_6374_; uint8_t v_isShared_6375_; uint8_t v_isSharedCheck_6445_; 
lean_inc(v_stop_6360_);
lean_inc(v_start_6359_);
lean_inc_ref(v_array_6358_);
v_isSharedCheck_6445_ = !lean_is_exclusive(v_snd_6345_);
if (v_isSharedCheck_6445_ == 0)
{
lean_object* v_unused_6446_; lean_object* v_unused_6447_; lean_object* v_unused_6448_; 
v_unused_6446_ = lean_ctor_get(v_snd_6345_, 2);
lean_dec(v_unused_6446_);
v_unused_6447_ = lean_ctor_get(v_snd_6345_, 1);
lean_dec(v_unused_6447_);
v_unused_6448_ = lean_ctor_get(v_snd_6345_, 0);
lean_dec(v_unused_6448_);
v___x_6374_ = v_snd_6345_;
v_isShared_6375_ = v_isSharedCheck_6445_;
goto v_resetjp_6373_;
}
else
{
lean_dec(v_snd_6345_);
v___x_6374_ = lean_box(0);
v_isShared_6375_ = v_isSharedCheck_6445_;
goto v_resetjp_6373_;
}
v_resetjp_6373_:
{
lean_object* v_array_6376_; lean_object* v_start_6377_; lean_object* v_stop_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; lean_object* v___x_6381_; lean_object* v___x_6383_; 
v_array_6376_ = lean_ctor_get(v_fst_6354_, 0);
v_start_6377_ = lean_ctor_get(v_fst_6354_, 1);
v_stop_6378_ = lean_ctor_get(v_fst_6354_, 2);
v___x_6379_ = lean_array_fget(v_array_6358_, v_start_6359_);
v___x_6380_ = lean_unsigned_to_nat(1u);
v___x_6381_ = lean_nat_add(v_start_6359_, v___x_6380_);
lean_dec(v_start_6359_);
if (v_isShared_6375_ == 0)
{
lean_ctor_set(v___x_6374_, 1, v___x_6381_);
v___x_6383_ = v___x_6374_;
goto v_reusejp_6382_;
}
else
{
lean_object* v_reuseFailAlloc_6444_; 
v_reuseFailAlloc_6444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6444_, 0, v_array_6358_);
lean_ctor_set(v_reuseFailAlloc_6444_, 1, v___x_6381_);
lean_ctor_set(v_reuseFailAlloc_6444_, 2, v_stop_6360_);
v___x_6383_ = v_reuseFailAlloc_6444_;
goto v_reusejp_6382_;
}
v_reusejp_6382_:
{
uint8_t v___x_6384_; 
v___x_6384_ = lean_nat_dec_lt(v_start_6377_, v_stop_6378_);
if (v___x_6384_ == 0)
{
lean_object* v___x_6386_; 
lean_dec(v___x_6379_);
if (v_isShared_6357_ == 0)
{
lean_ctor_set(v___x_6356_, 1, v___x_6383_);
v___x_6386_ = v___x_6356_;
goto v_reusejp_6385_;
}
else
{
lean_object* v_reuseFailAlloc_6395_; 
v_reuseFailAlloc_6395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6395_, 0, v_fst_6354_);
lean_ctor_set(v_reuseFailAlloc_6395_, 1, v___x_6383_);
v___x_6386_ = v_reuseFailAlloc_6395_;
goto v_reusejp_6385_;
}
v_reusejp_6385_:
{
lean_object* v___x_6388_; 
if (v_isShared_6353_ == 0)
{
lean_ctor_set(v___x_6352_, 1, v___x_6386_);
v___x_6388_ = v___x_6352_;
goto v_reusejp_6387_;
}
else
{
lean_object* v_reuseFailAlloc_6394_; 
v_reuseFailAlloc_6394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6394_, 0, v_fst_6350_);
lean_ctor_set(v_reuseFailAlloc_6394_, 1, v___x_6386_);
v___x_6388_ = v_reuseFailAlloc_6394_;
goto v_reusejp_6387_;
}
v_reusejp_6387_:
{
lean_object* v___x_6390_; 
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 1, v___x_6388_);
v___x_6390_ = v___x_6348_;
goto v_reusejp_6389_;
}
else
{
lean_object* v_reuseFailAlloc_6393_; 
v_reuseFailAlloc_6393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6393_, 0, v_fst_6346_);
lean_ctor_set(v_reuseFailAlloc_6393_, 1, v___x_6388_);
v___x_6390_ = v_reuseFailAlloc_6393_;
goto v_reusejp_6389_;
}
v_reusejp_6389_:
{
lean_object* v___x_6391_; lean_object* v___f_6392_; 
v___x_6391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6391_, 0, v___x_6390_);
v___f_6392_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6392_, 0, v___x_6391_);
v___y_6318_ = v___f_6392_;
goto v___jp_6317_;
}
}
}
}
else
{
lean_object* v___x_6397_; uint8_t v_isShared_6398_; uint8_t v_isSharedCheck_6440_; 
lean_inc(v_stop_6378_);
lean_inc(v_start_6377_);
lean_inc_ref(v_array_6376_);
v_isSharedCheck_6440_ = !lean_is_exclusive(v_fst_6354_);
if (v_isSharedCheck_6440_ == 0)
{
lean_object* v_unused_6441_; lean_object* v_unused_6442_; lean_object* v_unused_6443_; 
v_unused_6441_ = lean_ctor_get(v_fst_6354_, 2);
lean_dec(v_unused_6441_);
v_unused_6442_ = lean_ctor_get(v_fst_6354_, 1);
lean_dec(v_unused_6442_);
v_unused_6443_ = lean_ctor_get(v_fst_6354_, 0);
lean_dec(v_unused_6443_);
v___x_6397_ = v_fst_6354_;
v_isShared_6398_ = v_isSharedCheck_6440_;
goto v_resetjp_6396_;
}
else
{
lean_dec(v_fst_6354_);
v___x_6397_ = lean_box(0);
v_isShared_6398_ = v_isSharedCheck_6440_;
goto v_resetjp_6396_;
}
v_resetjp_6396_:
{
lean_object* v_array_6399_; lean_object* v_start_6400_; lean_object* v_stop_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6405_; 
v_array_6399_ = lean_ctor_get(v_fst_6350_, 0);
v_start_6400_ = lean_ctor_get(v_fst_6350_, 1);
v_stop_6401_ = lean_ctor_get(v_fst_6350_, 2);
v___x_6402_ = lean_array_fget(v_array_6376_, v_start_6377_);
v___x_6403_ = lean_nat_add(v_start_6377_, v___x_6380_);
lean_dec(v_start_6377_);
if (v_isShared_6398_ == 0)
{
lean_ctor_set(v___x_6397_, 1, v___x_6403_);
v___x_6405_ = v___x_6397_;
goto v_reusejp_6404_;
}
else
{
lean_object* v_reuseFailAlloc_6439_; 
v_reuseFailAlloc_6439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6439_, 0, v_array_6376_);
lean_ctor_set(v_reuseFailAlloc_6439_, 1, v___x_6403_);
lean_ctor_set(v_reuseFailAlloc_6439_, 2, v_stop_6378_);
v___x_6405_ = v_reuseFailAlloc_6439_;
goto v_reusejp_6404_;
}
v_reusejp_6404_:
{
uint8_t v___x_6406_; 
v___x_6406_ = lean_nat_dec_lt(v_start_6400_, v_stop_6401_);
if (v___x_6406_ == 0)
{
lean_object* v___x_6408_; 
lean_dec(v___x_6402_);
lean_dec(v___x_6379_);
if (v_isShared_6357_ == 0)
{
lean_ctor_set(v___x_6356_, 1, v___x_6383_);
lean_ctor_set(v___x_6356_, 0, v___x_6405_);
v___x_6408_ = v___x_6356_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6417_; 
v_reuseFailAlloc_6417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6417_, 0, v___x_6405_);
lean_ctor_set(v_reuseFailAlloc_6417_, 1, v___x_6383_);
v___x_6408_ = v_reuseFailAlloc_6417_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
lean_object* v___x_6410_; 
if (v_isShared_6353_ == 0)
{
lean_ctor_set(v___x_6352_, 1, v___x_6408_);
v___x_6410_ = v___x_6352_;
goto v_reusejp_6409_;
}
else
{
lean_object* v_reuseFailAlloc_6416_; 
v_reuseFailAlloc_6416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6416_, 0, v_fst_6350_);
lean_ctor_set(v_reuseFailAlloc_6416_, 1, v___x_6408_);
v___x_6410_ = v_reuseFailAlloc_6416_;
goto v_reusejp_6409_;
}
v_reusejp_6409_:
{
lean_object* v___x_6412_; 
if (v_isShared_6349_ == 0)
{
lean_ctor_set(v___x_6348_, 1, v___x_6410_);
v___x_6412_ = v___x_6348_;
goto v_reusejp_6411_;
}
else
{
lean_object* v_reuseFailAlloc_6415_; 
v_reuseFailAlloc_6415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6415_, 0, v_fst_6346_);
lean_ctor_set(v_reuseFailAlloc_6415_, 1, v___x_6410_);
v___x_6412_ = v_reuseFailAlloc_6415_;
goto v_reusejp_6411_;
}
v_reusejp_6411_:
{
lean_object* v___x_6413_; lean_object* v___f_6414_; 
v___x_6413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6413_, 0, v___x_6412_);
v___f_6414_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6414_, 0, v___x_6413_);
v___y_6318_ = v___f_6414_;
goto v___jp_6317_;
}
}
}
}
else
{
lean_object* v___x_6419_; uint8_t v_isShared_6420_; uint8_t v_isSharedCheck_6435_; 
lean_inc(v_stop_6401_);
lean_inc(v_start_6400_);
lean_inc_ref(v_array_6399_);
lean_del_object(v___x_6356_);
lean_del_object(v___x_6352_);
lean_del_object(v___x_6348_);
v_isSharedCheck_6435_ = !lean_is_exclusive(v_fst_6350_);
if (v_isSharedCheck_6435_ == 0)
{
lean_object* v_unused_6436_; lean_object* v_unused_6437_; lean_object* v_unused_6438_; 
v_unused_6436_ = lean_ctor_get(v_fst_6350_, 2);
lean_dec(v_unused_6436_);
v_unused_6437_ = lean_ctor_get(v_fst_6350_, 1);
lean_dec(v_unused_6437_);
v_unused_6438_ = lean_ctor_get(v_fst_6350_, 0);
lean_dec(v_unused_6438_);
v___x_6419_ = v_fst_6350_;
v_isShared_6420_ = v_isSharedCheck_6435_;
goto v_resetjp_6418_;
}
else
{
lean_dec(v_fst_6350_);
v___x_6419_ = lean_box(0);
v_isShared_6420_ = v_isSharedCheck_6435_;
goto v_resetjp_6418_;
}
v_resetjp_6418_:
{
lean_object* v___f_6421_; uint8_t v___x_6422_; lean_object* v_remaining_x27_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___f_6427_; lean_object* v___x_6428_; lean_object* v___x_6430_; 
v___f_6421_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6422_ = 0;
v_remaining_x27_6423_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6424_ = lean_array_fget_borrowed(v_array_6399_, v_start_6400_);
v___x_6425_ = lean_box(v___x_6422_);
v___x_6426_ = lean_box(v___x_6406_);
lean_inc(v_extraEqualities_6309_);
lean_inc(v_a_6310_);
lean_inc_ref(v_onAlt_6308_);
lean_inc(v___x_6424_);
v___f_6427_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6427_, 0, v___x_6424_);
lean_closure_set(v___f_6427_, 1, v_remaining_x27_6423_);
lean_closure_set(v___f_6427_, 2, v_onAlt_6308_);
lean_closure_set(v___f_6427_, 3, v_a_6310_);
lean_closure_set(v___f_6427_, 4, v___x_6425_);
lean_closure_set(v___f_6427_, 5, v___x_6426_);
lean_closure_set(v___f_6427_, 6, v___f_6421_);
lean_closure_set(v___f_6427_, 7, v_extraEqualities_6309_);
v___x_6428_ = lean_nat_add(v_start_6400_, v___x_6380_);
lean_dec(v_start_6400_);
if (v_isShared_6420_ == 0)
{
lean_ctor_set(v___x_6419_, 1, v___x_6428_);
v___x_6430_ = v___x_6419_;
goto v_reusejp_6429_;
}
else
{
lean_object* v_reuseFailAlloc_6434_; 
v_reuseFailAlloc_6434_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6434_, 0, v_array_6399_);
lean_ctor_set(v_reuseFailAlloc_6434_, 1, v___x_6428_);
lean_ctor_set(v_reuseFailAlloc_6434_, 2, v_stop_6401_);
v___x_6430_ = v_reuseFailAlloc_6434_;
goto v_reusejp_6429_;
}
v_reusejp_6429_:
{
lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___f_6433_; 
v___x_6431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6431_, 0, v___x_6402_);
v___x_6432_ = lean_box(v___x_6422_);
v___f_6433_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6433_, 0, v___x_6379_);
lean_closure_set(v___f_6433_, 1, v___x_6431_);
lean_closure_set(v___f_6433_, 2, v___f_6427_);
lean_closure_set(v___f_6433_, 3, v___x_6432_);
lean_closure_set(v___f_6433_, 4, v_fst_6346_);
lean_closure_set(v___f_6433_, 5, v___x_6405_);
lean_closure_set(v___f_6433_, 6, v___x_6383_);
lean_closure_set(v___f_6433_, 7, v___x_6430_);
v___y_6318_ = v___f_6433_;
goto v___jp_6317_;
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
v___jp_6317_:
{
lean_object* v___x_6319_; 
lean_inc(v___y_6315_);
lean_inc_ref(v___y_6314_);
lean_inc(v___y_6313_);
lean_inc_ref(v___y_6312_);
v___x_6319_ = lean_apply_5(v___y_6318_, v___y_6312_, v___y_6313_, v___y_6314_, v___y_6315_, lean_box(0));
if (lean_obj_tag(v___x_6319_) == 0)
{
lean_object* v_a_6320_; lean_object* v___x_6322_; uint8_t v_isShared_6323_; uint8_t v_isSharedCheck_6332_; 
v_a_6320_ = lean_ctor_get(v___x_6319_, 0);
v_isSharedCheck_6332_ = !lean_is_exclusive(v___x_6319_);
if (v_isSharedCheck_6332_ == 0)
{
v___x_6322_ = v___x_6319_;
v_isShared_6323_ = v_isSharedCheck_6332_;
goto v_resetjp_6321_;
}
else
{
lean_inc(v_a_6320_);
lean_dec(v___x_6319_);
v___x_6322_ = lean_box(0);
v_isShared_6323_ = v_isSharedCheck_6332_;
goto v_resetjp_6321_;
}
v_resetjp_6321_:
{
if (lean_obj_tag(v_a_6320_) == 0)
{
lean_object* v_a_6324_; lean_object* v___x_6326_; 
lean_dec(v_a_6310_);
lean_dec(v_extraEqualities_6309_);
lean_dec_ref(v_onAlt_6308_);
v_a_6324_ = lean_ctor_get(v_a_6320_, 0);
lean_inc(v_a_6324_);
lean_dec_ref_known(v_a_6320_, 1);
if (v_isShared_6323_ == 0)
{
lean_ctor_set(v___x_6322_, 0, v_a_6324_);
v___x_6326_ = v___x_6322_;
goto v_reusejp_6325_;
}
else
{
lean_object* v_reuseFailAlloc_6327_; 
v_reuseFailAlloc_6327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_a_6324_);
v___x_6326_ = v_reuseFailAlloc_6327_;
goto v_reusejp_6325_;
}
v_reusejp_6325_:
{
return v___x_6326_;
}
}
else
{
lean_object* v_a_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; 
lean_del_object(v___x_6322_);
v_a_6328_ = lean_ctor_get(v_a_6320_, 0);
lean_inc(v_a_6328_);
lean_dec_ref_known(v_a_6320_, 1);
v___x_6329_ = lean_unsigned_to_nat(1u);
v___x_6330_ = lean_nat_add(v_a_6310_, v___x_6329_);
lean_dec(v_a_6310_);
v_a_6310_ = v___x_6330_;
v_b_6311_ = v_a_6328_;
goto _start;
}
}
}
else
{
lean_object* v_a_6333_; lean_object* v___x_6335_; uint8_t v_isShared_6336_; uint8_t v_isSharedCheck_6340_; 
lean_dec(v_a_6310_);
lean_dec(v_extraEqualities_6309_);
lean_dec_ref(v_onAlt_6308_);
v_a_6333_ = lean_ctor_get(v___x_6319_, 0);
v_isSharedCheck_6340_ = !lean_is_exclusive(v___x_6319_);
if (v_isSharedCheck_6340_ == 0)
{
v___x_6335_ = v___x_6319_;
v_isShared_6336_ = v_isSharedCheck_6340_;
goto v_resetjp_6334_;
}
else
{
lean_inc(v_a_6333_);
lean_dec(v___x_6319_);
v___x_6335_ = lean_box(0);
v_isShared_6336_ = v_isSharedCheck_6340_;
goto v_resetjp_6334_;
}
v_resetjp_6334_:
{
lean_object* v___x_6338_; 
if (v_isShared_6336_ == 0)
{
v___x_6338_ = v___x_6335_;
goto v_reusejp_6337_;
}
else
{
lean_object* v_reuseFailAlloc_6339_; 
v_reuseFailAlloc_6339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6333_);
v___x_6338_ = v_reuseFailAlloc_6339_;
goto v_reusejp_6337_;
}
v_reusejp_6337_:
{
return v___x_6338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6455_, lean_object* v_onAlt_6456_, lean_object* v_extraEqualities_6457_, lean_object* v_a_6458_, lean_object* v_b_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_, lean_object* v___y_6463_, lean_object* v___y_6464_){
_start:
{
lean_object* v_res_6465_; 
v_res_6465_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6455_, v_onAlt_6456_, v_extraEqualities_6457_, v_a_6458_, v_b_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_);
lean_dec(v___y_6463_);
lean_dec_ref(v___y_6462_);
lean_dec(v___y_6461_);
lean_dec_ref(v___y_6460_);
lean_dec(v_upperBound_6455_);
return v_res_6465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6466_, size_t v_sz_6467_, size_t v_i_6468_, lean_object* v_bs_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_, lean_object* v___y_6472_, lean_object* v___y_6473_){
_start:
{
uint8_t v___x_6475_; 
v___x_6475_ = lean_usize_dec_lt(v_i_6468_, v_sz_6467_);
if (v___x_6475_ == 0)
{
lean_object* v___x_6476_; 
lean_dec_ref(v_onParams_6466_);
v___x_6476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6476_, 0, v_bs_6469_);
return v___x_6476_;
}
else
{
lean_object* v_v_6477_; lean_object* v___x_6478_; lean_object* v_bs_x27_6479_; lean_object* v___x_6480_; 
v_v_6477_ = lean_array_uget(v_bs_6469_, v_i_6468_);
v___x_6478_ = lean_unsigned_to_nat(0u);
v_bs_x27_6479_ = lean_array_uset(v_bs_6469_, v_i_6468_, v___x_6478_);
lean_inc_ref(v_onParams_6466_);
lean_inc(v___y_6473_);
lean_inc_ref(v___y_6472_);
lean_inc(v___y_6471_);
lean_inc_ref(v___y_6470_);
v___x_6480_ = lean_apply_6(v_onParams_6466_, v_v_6477_, v___y_6470_, v___y_6471_, v___y_6472_, v___y_6473_, lean_box(0));
if (lean_obj_tag(v___x_6480_) == 0)
{
lean_object* v_a_6481_; size_t v___x_6482_; size_t v___x_6483_; lean_object* v___x_6484_; 
v_a_6481_ = lean_ctor_get(v___x_6480_, 0);
lean_inc(v_a_6481_);
lean_dec_ref_known(v___x_6480_, 1);
v___x_6482_ = ((size_t)1ULL);
v___x_6483_ = lean_usize_add(v_i_6468_, v___x_6482_);
v___x_6484_ = lean_array_uset(v_bs_x27_6479_, v_i_6468_, v_a_6481_);
v_i_6468_ = v___x_6483_;
v_bs_6469_ = v___x_6484_;
goto _start;
}
else
{
lean_object* v_a_6486_; lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6493_; 
lean_dec_ref(v_bs_x27_6479_);
lean_dec_ref(v_onParams_6466_);
v_a_6486_ = lean_ctor_get(v___x_6480_, 0);
v_isSharedCheck_6493_ = !lean_is_exclusive(v___x_6480_);
if (v_isSharedCheck_6493_ == 0)
{
v___x_6488_ = v___x_6480_;
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
else
{
lean_inc(v_a_6486_);
lean_dec(v___x_6480_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
lean_object* v___x_6491_; 
if (v_isShared_6489_ == 0)
{
v___x_6491_ = v___x_6488_;
goto v_reusejp_6490_;
}
else
{
lean_object* v_reuseFailAlloc_6492_; 
v_reuseFailAlloc_6492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6492_, 0, v_a_6486_);
v___x_6491_ = v_reuseFailAlloc_6492_;
goto v_reusejp_6490_;
}
v_reusejp_6490_:
{
return v___x_6491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6494_, lean_object* v_sz_6495_, lean_object* v_i_6496_, lean_object* v_bs_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_){
_start:
{
size_t v_sz_boxed_6503_; size_t v_i_boxed_6504_; lean_object* v_res_6505_; 
v_sz_boxed_6503_ = lean_unbox_usize(v_sz_6495_);
lean_dec(v_sz_6495_);
v_i_boxed_6504_ = lean_unbox_usize(v_i_6496_);
lean_dec(v_i_6496_);
v_res_6505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6494_, v_sz_boxed_6503_, v_i_boxed_6504_, v_bs_6497_, v___y_6498_, v___y_6499_, v___y_6500_, v___y_6501_);
lean_dec(v___y_6501_);
lean_dec_ref(v___y_6500_);
lean_dec(v___y_6499_);
lean_dec_ref(v___y_6498_);
return v_res_6505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6506_, lean_object* v___y_6507_){
_start:
{
lean_object* v___x_6509_; lean_object* v_env_6510_; lean_object* v___x_6511_; lean_object* v___x_6512_; 
v___x_6509_ = lean_st_ref_get(v___y_6507_);
v_env_6510_ = lean_ctor_get(v___x_6509_, 0);
lean_inc_ref(v_env_6510_);
lean_dec(v___x_6509_);
v___x_6511_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6510_, v_declName_6506_);
v___x_6512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6512_, 0, v___x_6511_);
return v___x_6512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_){
_start:
{
lean_object* v_res_6516_; 
v_res_6516_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6513_, v___y_6514_);
lean_dec(v___y_6514_);
return v_res_6516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6519_, uint8_t v_useSplitter_6520_, uint8_t v_addEqualities_6521_, lean_object* v_onParams_6522_, lean_object* v_onMotive_6523_, lean_object* v_onAlt_6524_, lean_object* v_onRemaining_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_){
_start:
{
lean_object* v___x_6531_; lean_object* v_env_6532_; lean_object* v_toMatcherInfo_6533_; lean_object* v_matcherName_6534_; lean_object* v_matcherLevels_6535_; lean_object* v_params_6536_; lean_object* v_motive_6537_; lean_object* v_discrs_6538_; lean_object* v_alts_6539_; lean_object* v_remaining_6540_; lean_object* v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; lean_object* v___y_6548_; lean_object* v___y_6549_; lean_object* v___y_6550_; lean_object* v___y_6551_; lean_object* v___y_6552_; lean_object* v___y_6553_; lean_object* v___y_6554_; uint8_t v_isCasesOn_6639_; lean_object* v___y_6641_; lean_object* v___y_6642_; size_t v___y_6643_; lean_object* v___y_6644_; lean_object* v___y_6645_; lean_object* v___y_6646_; lean_object* v___y_6647_; lean_object* v_matcherLevels_6648_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v___y_6651_; lean_object* v___y_6652_; lean_object* v_numDiscrEqs_6846_; lean_object* v___y_6847_; lean_object* v___y_6848_; lean_object* v___y_6849_; lean_object* v___y_6850_; 
v___x_6531_ = lean_st_ref_get(v___y_6529_);
v_env_6532_ = lean_ctor_get(v___x_6531_, 0);
lean_inc_ref(v_env_6532_);
lean_dec(v___x_6531_);
v_toMatcherInfo_6533_ = lean_ctor_get(v_matcherApp_6519_, 0);
lean_inc_ref(v_toMatcherInfo_6533_);
v_matcherName_6534_ = lean_ctor_get(v_matcherApp_6519_, 1);
lean_inc_n(v_matcherName_6534_, 2);
v_matcherLevels_6535_ = lean_ctor_get(v_matcherApp_6519_, 2);
v_params_6536_ = lean_ctor_get(v_matcherApp_6519_, 3);
v_motive_6537_ = lean_ctor_get(v_matcherApp_6519_, 4);
v_discrs_6538_ = lean_ctor_get(v_matcherApp_6519_, 5);
v_alts_6539_ = lean_ctor_get(v_matcherApp_6519_, 6);
lean_inc_ref(v_alts_6539_);
v_remaining_6540_ = lean_ctor_get(v_matcherApp_6519_, 7);
lean_inc_ref(v_remaining_6540_);
v_isCasesOn_6639_ = l_Lean_isCasesOnRecursor(v_env_6532_, v_matcherName_6534_);
if (v_isCasesOn_6639_ == 0)
{
lean_object* v___x_6900_; lean_object* v_a_6901_; 
lean_inc(v_matcherName_6534_);
v___x_6900_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6534_, v___y_6529_);
v_a_6901_ = lean_ctor_get(v___x_6900_, 0);
lean_inc(v_a_6901_);
lean_dec_ref(v___x_6900_);
if (lean_obj_tag(v_a_6901_) == 0)
{
lean_object* v___x_6902_; lean_object* v___x_6903_; lean_object* v___x_6904_; lean_object* v___x_6905_; lean_object* v___x_6906_; lean_object* v___x_6907_; lean_object* v_a_6908_; lean_object* v___x_6910_; uint8_t v_isShared_6911_; uint8_t v_isSharedCheck_6915_; 
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
lean_dec_ref(v_onMotive_6523_);
lean_dec_ref(v_onParams_6522_);
lean_dec_ref(v_matcherApp_6519_);
v___x_6902_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6903_ = l_Lean_MessageData_ofName(v_matcherName_6534_);
v___x_6904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6904_, 0, v___x_6902_);
lean_ctor_set(v___x_6904_, 1, v___x_6903_);
v___x_6905_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6906_, 0, v___x_6904_);
lean_ctor_set(v___x_6906_, 1, v___x_6905_);
v___x_6907_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6906_, v___y_6526_, v___y_6527_, v___y_6528_, v___y_6529_);
v_a_6908_ = lean_ctor_get(v___x_6907_, 0);
v_isSharedCheck_6915_ = !lean_is_exclusive(v___x_6907_);
if (v_isSharedCheck_6915_ == 0)
{
v___x_6910_ = v___x_6907_;
v_isShared_6911_ = v_isSharedCheck_6915_;
goto v_resetjp_6909_;
}
else
{
lean_inc(v_a_6908_);
lean_dec(v___x_6907_);
v___x_6910_ = lean_box(0);
v_isShared_6911_ = v_isSharedCheck_6915_;
goto v_resetjp_6909_;
}
v_resetjp_6909_:
{
lean_object* v___x_6913_; 
if (v_isShared_6911_ == 0)
{
v___x_6913_ = v___x_6910_;
goto v_reusejp_6912_;
}
else
{
lean_object* v_reuseFailAlloc_6914_; 
v_reuseFailAlloc_6914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6914_, 0, v_a_6908_);
v___x_6913_ = v_reuseFailAlloc_6914_;
goto v_reusejp_6912_;
}
v_reusejp_6912_:
{
return v___x_6913_;
}
}
}
else
{
lean_object* v_val_6916_; lean_object* v___x_6917_; 
v_val_6916_ = lean_ctor_get(v_a_6901_, 0);
lean_inc(v_val_6916_);
lean_dec_ref_known(v_a_6901_, 1);
v___x_6917_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6916_);
lean_dec(v_val_6916_);
v_numDiscrEqs_6846_ = v___x_6917_;
v___y_6847_ = v___y_6526_;
v___y_6848_ = v___y_6527_;
v___y_6849_ = v___y_6528_;
v___y_6850_ = v___y_6529_;
goto v___jp_6845_;
}
}
else
{
lean_object* v___x_6918_; 
v___x_6918_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6846_ = v___x_6918_;
v___y_6847_ = v___y_6526_;
v___y_6848_ = v___y_6527_;
v___y_6849_ = v___y_6528_;
v___y_6850_ = v___y_6529_;
goto v___jp_6845_;
}
v___jp_6541_:
{
lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v_aux_6557_; lean_object* v_aux_6558_; lean_object* v_aux_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___f_6563_; uint8_t v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; 
lean_inc_ref(v___y_6550_);
v___x_6555_ = lean_array_to_list(v___y_6550_);
lean_inc(v_matcherName_6534_);
v___x_6556_ = l_Lean_mkConst(v_matcherName_6534_, v___x_6555_);
v_aux_6557_ = l_Lean_mkAppN(v___x_6556_, v___y_6543_);
lean_inc_ref(v___y_6554_);
v_aux_6558_ = l_Lean_Expr_app___override(v_aux_6557_, v___y_6554_);
v_aux_6559_ = l_Lean_mkAppN(v_aux_6558_, v___y_6547_);
v___x_6560_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6559_, 2);
v___x_6561_ = l_Lean_indentExpr(v_aux_6559_);
v___x_6562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6562_, 0, v___x_6560_);
lean_ctor_set(v___x_6562_, 1, v___x_6561_);
v___f_6563_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6563_, 0, v___x_6562_);
v___x_6564_ = 0;
v___x_6565_ = lean_box(v___x_6564_);
v___x_6566_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6566_, 0, v_aux_6559_);
lean_closure_set(v___x_6566_, 1, v___x_6565_);
v___x_6567_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6566_, v___f_6563_, v___y_6553_, v___y_6551_, v___y_6549_, v___y_6545_);
if (lean_obj_tag(v___x_6567_) == 0)
{
lean_object* v___x_6568_; lean_object* v___x_6569_; 
lean_dec_ref_known(v___x_6567_, 1);
v___x_6568_ = lean_array_get_size(v_alts_6539_);
v___x_6569_ = l_Lean_Meta_inferArgumentTypesN(v___x_6568_, v_aux_6559_, v___y_6553_, v___y_6551_, v___y_6549_, v___y_6545_);
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_object* v_a_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; lean_object* v___x_6579_; lean_object* v___x_6580_; 
v_a_6570_ = lean_ctor_get(v___x_6569_, 0);
lean_inc(v_a_6570_);
lean_dec_ref_known(v___x_6569_, 1);
v___x_6571_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6519_);
v___x_6572_ = lean_array_get_size(v___x_6571_);
v___x_6573_ = lean_array_get_size(v_a_6570_);
lean_inc_n(v___y_6552_, 3);
v___x_6574_ = l_Array_toSubarray___redArg(v_alts_6539_, v___y_6552_, v___x_6568_);
v___x_6575_ = l_Array_toSubarray___redArg(v___x_6571_, v___y_6552_, v___x_6572_);
v___x_6576_ = l_Array_toSubarray___redArg(v_a_6570_, v___y_6552_, v___x_6573_);
v___x_6577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6577_, 0, v___x_6575_);
lean_ctor_set(v___x_6577_, 1, v___x_6576_);
v___x_6578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6578_, 0, v___x_6574_);
lean_ctor_set(v___x_6578_, 1, v___x_6577_);
lean_inc_ref(v___y_6546_);
v___x_6579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6579_, 0, v___y_6546_);
lean_ctor_set(v___x_6579_, 1, v___x_6578_);
v___x_6580_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6568_, v_onAlt_6524_, v___y_6542_, v___y_6552_, v___x_6579_, v___y_6553_, v___y_6551_, v___y_6549_, v___y_6545_);
if (lean_obj_tag(v___x_6580_) == 0)
{
lean_object* v_a_6581_; lean_object* v_fst_6582_; lean_object* v___x_6583_; 
v_a_6581_ = lean_ctor_get(v___x_6580_, 0);
lean_inc(v_a_6581_);
lean_dec_ref_known(v___x_6580_, 1);
v_fst_6582_ = lean_ctor_get(v_a_6581_, 0);
lean_inc(v_fst_6582_);
lean_dec(v_a_6581_);
lean_inc(v___y_6545_);
lean_inc_ref(v___y_6549_);
lean_inc(v___y_6551_);
lean_inc_ref(v___y_6553_);
v___x_6583_ = lean_apply_6(v_onRemaining_6525_, v_remaining_6540_, v___y_6553_, v___y_6551_, v___y_6549_, v___y_6545_, lean_box(0));
if (lean_obj_tag(v___x_6583_) == 0)
{
lean_object* v_a_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6606_; 
v_a_6584_ = lean_ctor_get(v___x_6583_, 0);
v_isSharedCheck_6606_ = !lean_is_exclusive(v___x_6583_);
if (v_isSharedCheck_6606_ == 0)
{
v___x_6586_ = v___x_6583_;
v_isShared_6587_ = v_isSharedCheck_6606_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_a_6584_);
lean_dec(v___x_6583_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6606_;
goto v_resetjp_6585_;
}
v_resetjp_6585_:
{
lean_object* v_numParams_6588_; lean_object* v_numDiscrs_6589_; lean_object* v_altInfos_6590_; lean_object* v_uElimPos_x3f_6591_; lean_object* v_overlaps_6592_; lean_object* v___x_6594_; uint8_t v_isShared_6595_; uint8_t v_isSharedCheck_6604_; 
v_numParams_6588_ = lean_ctor_get(v_toMatcherInfo_6533_, 0);
v_numDiscrs_6589_ = lean_ctor_get(v_toMatcherInfo_6533_, 1);
v_altInfos_6590_ = lean_ctor_get(v_toMatcherInfo_6533_, 2);
v_uElimPos_x3f_6591_ = lean_ctor_get(v_toMatcherInfo_6533_, 3);
v_overlaps_6592_ = lean_ctor_get(v_toMatcherInfo_6533_, 5);
v_isSharedCheck_6604_ = !lean_is_exclusive(v_toMatcherInfo_6533_);
if (v_isSharedCheck_6604_ == 0)
{
lean_object* v_unused_6605_; 
v_unused_6605_ = lean_ctor_get(v_toMatcherInfo_6533_, 4);
lean_dec(v_unused_6605_);
v___x_6594_ = v_toMatcherInfo_6533_;
v_isShared_6595_ = v_isSharedCheck_6604_;
goto v_resetjp_6593_;
}
else
{
lean_inc(v_overlaps_6592_);
lean_inc(v_uElimPos_x3f_6591_);
lean_inc(v_altInfos_6590_);
lean_inc(v_numDiscrs_6589_);
lean_inc(v_numParams_6588_);
lean_dec(v_toMatcherInfo_6533_);
v___x_6594_ = lean_box(0);
v_isShared_6595_ = v_isSharedCheck_6604_;
goto v_resetjp_6593_;
}
v_resetjp_6593_:
{
lean_object* v_remaining_x27_6596_; lean_object* v___x_6598_; 
v_remaining_x27_6596_ = l_Array_append___redArg(v___y_6548_, v_a_6584_);
lean_dec(v_a_6584_);
if (v_isShared_6595_ == 0)
{
lean_ctor_set(v___x_6594_, 4, v___y_6544_);
v___x_6598_ = v___x_6594_;
goto v_reusejp_6597_;
}
else
{
lean_object* v_reuseFailAlloc_6603_; 
v_reuseFailAlloc_6603_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6603_, 0, v_numParams_6588_);
lean_ctor_set(v_reuseFailAlloc_6603_, 1, v_numDiscrs_6589_);
lean_ctor_set(v_reuseFailAlloc_6603_, 2, v_altInfos_6590_);
lean_ctor_set(v_reuseFailAlloc_6603_, 3, v_uElimPos_x3f_6591_);
lean_ctor_set(v_reuseFailAlloc_6603_, 4, v___y_6544_);
lean_ctor_set(v_reuseFailAlloc_6603_, 5, v_overlaps_6592_);
v___x_6598_ = v_reuseFailAlloc_6603_;
goto v_reusejp_6597_;
}
v_reusejp_6597_:
{
lean_object* v___x_6599_; lean_object* v___x_6601_; 
v___x_6599_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6599_, 0, v___x_6598_);
lean_ctor_set(v___x_6599_, 1, v_matcherName_6534_);
lean_ctor_set(v___x_6599_, 2, v___y_6550_);
lean_ctor_set(v___x_6599_, 3, v___y_6543_);
lean_ctor_set(v___x_6599_, 4, v___y_6554_);
lean_ctor_set(v___x_6599_, 5, v___y_6547_);
lean_ctor_set(v___x_6599_, 6, v_fst_6582_);
lean_ctor_set(v___x_6599_, 7, v_remaining_x27_6596_);
if (v_isShared_6587_ == 0)
{
lean_ctor_set(v___x_6586_, 0, v___x_6599_);
v___x_6601_ = v___x_6586_;
goto v_reusejp_6600_;
}
else
{
lean_object* v_reuseFailAlloc_6602_; 
v_reuseFailAlloc_6602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6602_, 0, v___x_6599_);
v___x_6601_ = v_reuseFailAlloc_6602_;
goto v_reusejp_6600_;
}
v_reusejp_6600_:
{
return v___x_6601_;
}
}
}
}
}
else
{
lean_object* v_a_6607_; lean_object* v___x_6609_; uint8_t v_isShared_6610_; uint8_t v_isSharedCheck_6614_; 
lean_dec(v_fst_6582_);
lean_dec_ref(v___y_6554_);
lean_dec_ref(v___y_6550_);
lean_dec(v___y_6548_);
lean_dec_ref(v___y_6547_);
lean_dec_ref(v___y_6544_);
lean_dec_ref(v___y_6543_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
v_a_6607_ = lean_ctor_get(v___x_6583_, 0);
v_isSharedCheck_6614_ = !lean_is_exclusive(v___x_6583_);
if (v_isSharedCheck_6614_ == 0)
{
v___x_6609_ = v___x_6583_;
v_isShared_6610_ = v_isSharedCheck_6614_;
goto v_resetjp_6608_;
}
else
{
lean_inc(v_a_6607_);
lean_dec(v___x_6583_);
v___x_6609_ = lean_box(0);
v_isShared_6610_ = v_isSharedCheck_6614_;
goto v_resetjp_6608_;
}
v_resetjp_6608_:
{
lean_object* v___x_6612_; 
if (v_isShared_6610_ == 0)
{
v___x_6612_ = v___x_6609_;
goto v_reusejp_6611_;
}
else
{
lean_object* v_reuseFailAlloc_6613_; 
v_reuseFailAlloc_6613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6613_, 0, v_a_6607_);
v___x_6612_ = v_reuseFailAlloc_6613_;
goto v_reusejp_6611_;
}
v_reusejp_6611_:
{
return v___x_6612_;
}
}
}
}
else
{
lean_object* v_a_6615_; lean_object* v___x_6617_; uint8_t v_isShared_6618_; uint8_t v_isSharedCheck_6622_; 
lean_dec_ref(v___y_6554_);
lean_dec_ref(v___y_6550_);
lean_dec(v___y_6548_);
lean_dec_ref(v___y_6547_);
lean_dec_ref(v___y_6544_);
lean_dec_ref(v___y_6543_);
lean_dec_ref(v_remaining_6540_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
v_a_6615_ = lean_ctor_get(v___x_6580_, 0);
v_isSharedCheck_6622_ = !lean_is_exclusive(v___x_6580_);
if (v_isSharedCheck_6622_ == 0)
{
v___x_6617_ = v___x_6580_;
v_isShared_6618_ = v_isSharedCheck_6622_;
goto v_resetjp_6616_;
}
else
{
lean_inc(v_a_6615_);
lean_dec(v___x_6580_);
v___x_6617_ = lean_box(0);
v_isShared_6618_ = v_isSharedCheck_6622_;
goto v_resetjp_6616_;
}
v_resetjp_6616_:
{
lean_object* v___x_6620_; 
if (v_isShared_6618_ == 0)
{
v___x_6620_ = v___x_6617_;
goto v_reusejp_6619_;
}
else
{
lean_object* v_reuseFailAlloc_6621_; 
v_reuseFailAlloc_6621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6621_, 0, v_a_6615_);
v___x_6620_ = v_reuseFailAlloc_6621_;
goto v_reusejp_6619_;
}
v_reusejp_6619_:
{
return v___x_6620_;
}
}
}
}
else
{
lean_object* v_a_6623_; lean_object* v___x_6625_; uint8_t v_isShared_6626_; uint8_t v_isSharedCheck_6630_; 
lean_dec_ref(v___y_6554_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6550_);
lean_dec(v___y_6548_);
lean_dec_ref(v___y_6547_);
lean_dec_ref(v___y_6544_);
lean_dec_ref(v___y_6543_);
lean_dec(v___y_6542_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
lean_dec_ref(v_matcherApp_6519_);
v_a_6623_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6630_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6630_ == 0)
{
v___x_6625_ = v___x_6569_;
v_isShared_6626_ = v_isSharedCheck_6630_;
goto v_resetjp_6624_;
}
else
{
lean_inc(v_a_6623_);
lean_dec(v___x_6569_);
v___x_6625_ = lean_box(0);
v_isShared_6626_ = v_isSharedCheck_6630_;
goto v_resetjp_6624_;
}
v_resetjp_6624_:
{
lean_object* v___x_6628_; 
if (v_isShared_6626_ == 0)
{
v___x_6628_ = v___x_6625_;
goto v_reusejp_6627_;
}
else
{
lean_object* v_reuseFailAlloc_6629_; 
v_reuseFailAlloc_6629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6629_, 0, v_a_6623_);
v___x_6628_ = v_reuseFailAlloc_6629_;
goto v_reusejp_6627_;
}
v_reusejp_6627_:
{
return v___x_6628_;
}
}
}
}
else
{
lean_object* v_a_6631_; lean_object* v___x_6633_; uint8_t v_isShared_6634_; uint8_t v_isSharedCheck_6638_; 
lean_dec_ref(v_aux_6559_);
lean_dec_ref(v___y_6554_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6550_);
lean_dec(v___y_6548_);
lean_dec_ref(v___y_6547_);
lean_dec_ref(v___y_6544_);
lean_dec_ref(v___y_6543_);
lean_dec(v___y_6542_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
lean_dec_ref(v_matcherApp_6519_);
v_a_6631_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6638_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6638_ == 0)
{
v___x_6633_ = v___x_6567_;
v_isShared_6634_ = v_isSharedCheck_6638_;
goto v_resetjp_6632_;
}
else
{
lean_inc(v_a_6631_);
lean_dec(v___x_6567_);
v___x_6633_ = lean_box(0);
v_isShared_6634_ = v_isSharedCheck_6638_;
goto v_resetjp_6632_;
}
v_resetjp_6632_:
{
lean_object* v___x_6636_; 
if (v_isShared_6634_ == 0)
{
v___x_6636_ = v___x_6633_;
goto v_reusejp_6635_;
}
else
{
lean_object* v_reuseFailAlloc_6637_; 
v_reuseFailAlloc_6637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6637_, 0, v_a_6631_);
v___x_6636_ = v_reuseFailAlloc_6637_;
goto v_reusejp_6635_;
}
v_reusejp_6635_:
{
return v___x_6636_;
}
}
}
}
v___jp_6640_:
{
lean_object* v___x_6653_; lean_object* v_remaining_x27_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; lean_object* v___x_6660_; size_t v_sz_6661_; lean_object* v___x_6662_; 
v___x_6653_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6654_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6655_ = l_Array_reverse___redArg(v___y_6644_);
v___x_6656_ = lean_array_get_size(v___x_6655_);
v___x_6657_ = l_Array_toSubarray___redArg(v___x_6655_, v___x_6653_, v___x_6656_);
lean_inc_ref(v___y_6647_);
v___x_6658_ = l_Array_reverse___redArg(v___y_6647_);
v___x_6659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6659_, 0, v___x_6653_);
lean_ctor_set(v___x_6659_, 1, v___x_6657_);
v___x_6660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6660_, 0, v_remaining_x27_6654_);
lean_ctor_set(v___x_6660_, 1, v___x_6659_);
v_sz_6661_ = lean_array_size(v___x_6658_);
v___x_6662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6658_, v_sz_6661_, v___y_6643_, v___x_6660_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_);
lean_dec_ref(v___x_6658_);
if (lean_obj_tag(v___x_6662_) == 0)
{
lean_object* v_a_6663_; lean_object* v_snd_6664_; 
v_a_6663_ = lean_ctor_get(v___x_6662_, 0);
lean_inc(v_a_6663_);
lean_dec_ref_known(v___x_6662_, 1);
v_snd_6664_ = lean_ctor_get(v_a_6663_, 1);
lean_inc(v_snd_6664_);
if (v_useSplitter_6520_ == 0)
{
lean_object* v_fst_6665_; lean_object* v_fst_6666_; 
lean_dec(v___y_6641_);
v_fst_6665_ = lean_ctor_get(v_a_6663_, 0);
lean_inc(v_fst_6665_);
lean_dec(v_a_6663_);
v_fst_6666_ = lean_ctor_get(v_snd_6664_, 0);
lean_inc(v_fst_6666_);
lean_dec(v_snd_6664_);
v___y_6542_ = v_fst_6666_;
v___y_6543_ = v___y_6642_;
v___y_6544_ = v___y_6645_;
v___y_6545_ = v___y_6652_;
v___y_6546_ = v_remaining_x27_6654_;
v___y_6547_ = v___y_6647_;
v___y_6548_ = v_fst_6665_;
v___y_6549_ = v___y_6651_;
v___y_6550_ = v_matcherLevels_6648_;
v___y_6551_ = v___y_6650_;
v___y_6552_ = v___x_6653_;
v___y_6553_ = v___y_6649_;
v___y_6554_ = v___y_6646_;
goto v___jp_6541_;
}
else
{
if (v_isCasesOn_6639_ == 0)
{
lean_object* v___x_6668_; uint8_t v_isShared_6669_; uint8_t v_isSharedCheck_6826_; 
v_isSharedCheck_6826_ = !lean_is_exclusive(v_matcherApp_6519_);
if (v_isSharedCheck_6826_ == 0)
{
lean_object* v_unused_6827_; lean_object* v_unused_6828_; lean_object* v_unused_6829_; lean_object* v_unused_6830_; lean_object* v_unused_6831_; lean_object* v_unused_6832_; lean_object* v_unused_6833_; lean_object* v_unused_6834_; 
v_unused_6827_ = lean_ctor_get(v_matcherApp_6519_, 7);
lean_dec(v_unused_6827_);
v_unused_6828_ = lean_ctor_get(v_matcherApp_6519_, 6);
lean_dec(v_unused_6828_);
v_unused_6829_ = lean_ctor_get(v_matcherApp_6519_, 5);
lean_dec(v_unused_6829_);
v_unused_6830_ = lean_ctor_get(v_matcherApp_6519_, 4);
lean_dec(v_unused_6830_);
v_unused_6831_ = lean_ctor_get(v_matcherApp_6519_, 3);
lean_dec(v_unused_6831_);
v_unused_6832_ = lean_ctor_get(v_matcherApp_6519_, 2);
lean_dec(v_unused_6832_);
v_unused_6833_ = lean_ctor_get(v_matcherApp_6519_, 1);
lean_dec(v_unused_6833_);
v_unused_6834_ = lean_ctor_get(v_matcherApp_6519_, 0);
lean_dec(v_unused_6834_);
v___x_6668_ = v_matcherApp_6519_;
v_isShared_6669_ = v_isSharedCheck_6826_;
goto v_resetjp_6667_;
}
else
{
lean_dec(v_matcherApp_6519_);
v___x_6668_ = lean_box(0);
v_isShared_6669_ = v_isSharedCheck_6826_;
goto v_resetjp_6667_;
}
v_resetjp_6667_:
{
lean_object* v_fst_6670_; lean_object* v___x_6672_; uint8_t v_isShared_6673_; uint8_t v_isSharedCheck_6824_; 
v_fst_6670_ = lean_ctor_get(v_a_6663_, 0);
v_isSharedCheck_6824_ = !lean_is_exclusive(v_a_6663_);
if (v_isSharedCheck_6824_ == 0)
{
lean_object* v_unused_6825_; 
v_unused_6825_ = lean_ctor_get(v_a_6663_, 1);
lean_dec(v_unused_6825_);
v___x_6672_ = v_a_6663_;
v_isShared_6673_ = v_isSharedCheck_6824_;
goto v_resetjp_6671_;
}
else
{
lean_inc(v_fst_6670_);
lean_dec(v_a_6663_);
v___x_6672_ = lean_box(0);
v_isShared_6673_ = v_isSharedCheck_6824_;
goto v_resetjp_6671_;
}
v_resetjp_6671_:
{
lean_object* v_fst_6674_; lean_object* v___x_6676_; uint8_t v_isShared_6677_; uint8_t v_isSharedCheck_6822_; 
v_fst_6674_ = lean_ctor_get(v_snd_6664_, 0);
v_isSharedCheck_6822_ = !lean_is_exclusive(v_snd_6664_);
if (v_isSharedCheck_6822_ == 0)
{
lean_object* v_unused_6823_; 
v_unused_6823_ = lean_ctor_get(v_snd_6664_, 1);
lean_dec(v_unused_6823_);
v___x_6676_ = v_snd_6664_;
v_isShared_6677_ = v_isSharedCheck_6822_;
goto v_resetjp_6675_;
}
else
{
lean_inc(v_fst_6674_);
lean_dec(v_snd_6664_);
v___x_6676_ = lean_box(0);
v_isShared_6677_ = v_isSharedCheck_6822_;
goto v_resetjp_6675_;
}
v_resetjp_6675_:
{
lean_object* v___x_6678_; lean_object* v___x_6679_; lean_object* v_aux1_6680_; lean_object* v_aux1_6681_; lean_object* v_aux1_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___f_6688_; uint8_t v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; 
lean_inc_ref(v_matcherLevels_6648_);
v___x_6678_ = lean_array_to_list(v_matcherLevels_6648_);
lean_inc(v___x_6678_);
lean_inc(v_matcherName_6534_);
v___x_6679_ = l_Lean_mkConst(v_matcherName_6534_, v___x_6678_);
v_aux1_6680_ = l_Lean_mkAppN(v___x_6679_, v___y_6642_);
lean_inc_ref(v___y_6646_);
v_aux1_6681_ = l_Lean_Expr_app___override(v_aux1_6680_, v___y_6646_);
v_aux1_6682_ = l_Lean_mkAppN(v_aux1_6681_, v___y_6647_);
v___x_6683_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6682_, 2);
v___x_6684_ = l_Lean_indentExpr(v_aux1_6682_);
v___x_6685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6685_, 0, v___x_6683_);
lean_ctor_set(v___x_6685_, 1, v___x_6684_);
v___x_6686_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6687_, 0, v___x_6685_);
lean_ctor_set(v___x_6687_, 1, v___x_6686_);
v___f_6688_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6688_, 0, v___x_6687_);
v___x_6689_ = 0;
v___x_6690_ = lean_box(v___x_6689_);
v___x_6691_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6691_, 0, v_aux1_6682_);
lean_closure_set(v___x_6691_, 1, v___x_6690_);
v___x_6692_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6691_, v___f_6688_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_);
if (lean_obj_tag(v___x_6692_) == 0)
{
lean_object* v___x_6693_; lean_object* v___x_6694_; 
lean_dec_ref_known(v___x_6692_, 1);
v___x_6693_ = lean_array_get_size(v_alts_6539_);
v___x_6694_ = l_Lean_Meta_inferArgumentTypesN(v___x_6693_, v_aux1_6682_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_);
if (lean_obj_tag(v___x_6694_) == 0)
{
lean_object* v_a_6695_; lean_object* v___x_6696_; 
v_a_6695_ = lean_ctor_get(v___x_6694_, 0);
lean_inc(v_a_6695_);
lean_dec_ref_known(v___x_6694_, 1);
lean_inc(v___y_6652_);
lean_inc_ref(v___y_6651_);
lean_inc(v___y_6650_);
lean_inc_ref(v___y_6649_);
v___x_6696_ = lean_get_match_equations_for(v_matcherName_6534_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_);
if (lean_obj_tag(v___x_6696_) == 0)
{
lean_object* v_a_6697_; lean_object* v_splitterName_6698_; lean_object* v_splitterMatchInfo_6699_; lean_object* v___x_6700_; lean_object* v_aux2_6701_; lean_object* v_aux2_6702_; lean_object* v_aux2_6703_; lean_object* v___x_6704_; lean_object* v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6707_; lean_object* v___f_6708_; lean_object* v___x_6709_; lean_object* v___x_6710_; lean_object* v___x_6711_; 
v_a_6697_ = lean_ctor_get(v___x_6696_, 0);
lean_inc(v_a_6697_);
lean_dec_ref_known(v___x_6696_, 1);
v_splitterName_6698_ = lean_ctor_get(v_a_6697_, 1);
lean_inc_n(v_splitterName_6698_, 2);
v_splitterMatchInfo_6699_ = lean_ctor_get(v_a_6697_, 2);
lean_inc_ref(v_splitterMatchInfo_6699_);
lean_dec(v_a_6697_);
v___x_6700_ = l_Lean_mkConst(v_splitterName_6698_, v___x_6678_);
v_aux2_6701_ = l_Lean_mkAppN(v___x_6700_, v___y_6642_);
lean_inc_ref(v___y_6646_);
v_aux2_6702_ = l_Lean_Expr_app___override(v_aux2_6701_, v___y_6646_);
v_aux2_6703_ = l_Lean_mkAppN(v_aux2_6702_, v___y_6647_);
v___x_6704_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6703_, 2);
v___x_6705_ = l_Lean_indentExpr(v_aux2_6703_);
v___x_6706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6706_, 0, v___x_6704_);
lean_ctor_set(v___x_6706_, 1, v___x_6705_);
v___x_6707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6707_, 0, v___x_6706_);
lean_ctor_set(v___x_6707_, 1, v___x_6686_);
v___f_6708_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6708_, 0, v___x_6707_);
v___x_6709_ = lean_box(v___x_6689_);
v___x_6710_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6710_, 0, v_aux2_6703_);
lean_closure_set(v___x_6710_, 1, v___x_6709_);
v___x_6711_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6710_, v___f_6708_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_);
if (lean_obj_tag(v___x_6711_) == 0)
{
lean_object* v___x_6712_; 
lean_dec_ref_known(v___x_6711_, 1);
v___x_6712_ = l_Lean_Meta_inferArgumentTypesN(v___x_6693_, v_aux2_6703_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_);
if (lean_obj_tag(v___x_6712_) == 0)
{
lean_object* v_a_6713_; lean_object* v_numParams_6714_; lean_object* v_numDiscrs_6715_; lean_object* v_altInfos_6716_; lean_object* v_uElimPos_x3f_6717_; lean_object* v_overlaps_6718_; lean_object* v_altInfos_6719_; lean_object* v___x_6721_; uint8_t v_isShared_6722_; uint8_t v_isSharedCheck_6776_; 
v_a_6713_ = lean_ctor_get(v___x_6712_, 0);
lean_inc(v_a_6713_);
lean_dec_ref_known(v___x_6712_, 1);
v_numParams_6714_ = lean_ctor_get(v_toMatcherInfo_6533_, 0);
lean_inc(v_numParams_6714_);
v_numDiscrs_6715_ = lean_ctor_get(v_toMatcherInfo_6533_, 1);
lean_inc(v_numDiscrs_6715_);
v_altInfos_6716_ = lean_ctor_get(v_toMatcherInfo_6533_, 2);
lean_inc_ref(v_altInfos_6716_);
v_uElimPos_x3f_6717_ = lean_ctor_get(v_toMatcherInfo_6533_, 3);
lean_inc(v_uElimPos_x3f_6717_);
v_overlaps_6718_ = lean_ctor_get(v_toMatcherInfo_6533_, 5);
lean_inc_ref(v_overlaps_6718_);
lean_dec_ref(v_toMatcherInfo_6533_);
v_altInfos_6719_ = lean_ctor_get(v_splitterMatchInfo_6699_, 2);
v_isSharedCheck_6776_ = !lean_is_exclusive(v_splitterMatchInfo_6699_);
if (v_isSharedCheck_6776_ == 0)
{
lean_object* v_unused_6777_; lean_object* v_unused_6778_; lean_object* v_unused_6779_; lean_object* v_unused_6780_; lean_object* v_unused_6781_; 
v_unused_6777_ = lean_ctor_get(v_splitterMatchInfo_6699_, 5);
lean_dec(v_unused_6777_);
v_unused_6778_ = lean_ctor_get(v_splitterMatchInfo_6699_, 4);
lean_dec(v_unused_6778_);
v_unused_6779_ = lean_ctor_get(v_splitterMatchInfo_6699_, 3);
lean_dec(v_unused_6779_);
v_unused_6780_ = lean_ctor_get(v_splitterMatchInfo_6699_, 1);
lean_dec(v_unused_6780_);
v_unused_6781_ = lean_ctor_get(v_splitterMatchInfo_6699_, 0);
lean_dec(v_unused_6781_);
v___x_6721_ = v_splitterMatchInfo_6699_;
v_isShared_6722_ = v_isSharedCheck_6776_;
goto v_resetjp_6720_;
}
else
{
lean_inc(v_altInfos_6719_);
lean_dec(v_splitterMatchInfo_6699_);
v___x_6721_ = lean_box(0);
v_isShared_6722_ = v_isSharedCheck_6776_;
goto v_resetjp_6720_;
}
v_resetjp_6720_:
{
lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6733_; 
v___x_6723_ = lean_array_get_size(v_altInfos_6716_);
v___x_6724_ = lean_array_get_size(v_altInfos_6719_);
v___x_6725_ = lean_array_get_size(v_a_6695_);
v___x_6726_ = lean_array_get_size(v_a_6713_);
v___x_6727_ = l_Array_toSubarray___redArg(v_alts_6539_, v___x_6653_, v___x_6693_);
lean_inc_ref(v_altInfos_6716_);
v___x_6728_ = l_Array_toSubarray___redArg(v_altInfos_6716_, v___x_6653_, v___x_6723_);
v___x_6729_ = l_Array_toSubarray___redArg(v_altInfos_6719_, v___x_6653_, v___x_6724_);
v___x_6730_ = l_Array_toSubarray___redArg(v_a_6695_, v___x_6653_, v___x_6725_);
v___x_6731_ = l_Array_toSubarray___redArg(v_a_6713_, v___x_6653_, v___x_6726_);
if (v_isShared_6677_ == 0)
{
lean_ctor_set(v___x_6676_, 1, v___x_6731_);
lean_ctor_set(v___x_6676_, 0, v___x_6730_);
v___x_6733_ = v___x_6676_;
goto v_reusejp_6732_;
}
else
{
lean_object* v_reuseFailAlloc_6775_; 
v_reuseFailAlloc_6775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6775_, 0, v___x_6730_);
lean_ctor_set(v_reuseFailAlloc_6775_, 1, v___x_6731_);
v___x_6733_ = v_reuseFailAlloc_6775_;
goto v_reusejp_6732_;
}
v_reusejp_6732_:
{
lean_object* v___x_6735_; 
if (v_isShared_6673_ == 0)
{
lean_ctor_set(v___x_6672_, 1, v___x_6733_);
lean_ctor_set(v___x_6672_, 0, v___x_6729_);
v___x_6735_ = v___x_6672_;
goto v_reusejp_6734_;
}
else
{
lean_object* v_reuseFailAlloc_6774_; 
v_reuseFailAlloc_6774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6774_, 0, v___x_6729_);
lean_ctor_set(v_reuseFailAlloc_6774_, 1, v___x_6733_);
v___x_6735_ = v_reuseFailAlloc_6774_;
goto v_reusejp_6734_;
}
v_reusejp_6734_:
{
lean_object* v___x_6736_; lean_object* v___x_6737_; lean_object* v___x_6738_; lean_object* v___x_6739_; 
v___x_6736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6736_, 0, v___x_6728_);
lean_ctor_set(v___x_6736_, 1, v___x_6735_);
v___x_6737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6737_, 0, v___x_6727_);
lean_ctor_set(v___x_6737_, 1, v___x_6736_);
v___x_6738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6738_, 0, v_remaining_x27_6654_);
lean_ctor_set(v___x_6738_, 1, v___x_6737_);
v___x_6739_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6693_, v_onAlt_6524_, v_useSplitter_6520_, v_fst_6674_, v___y_6641_, v___x_6653_, v___x_6738_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_);
if (lean_obj_tag(v___x_6739_) == 0)
{
lean_object* v_a_6740_; lean_object* v_fst_6741_; lean_object* v___x_6742_; 
v_a_6740_ = lean_ctor_get(v___x_6739_, 0);
lean_inc(v_a_6740_);
lean_dec_ref_known(v___x_6739_, 1);
v_fst_6741_ = lean_ctor_get(v_a_6740_, 0);
lean_inc(v_fst_6741_);
lean_dec(v_a_6740_);
lean_inc(v___y_6652_);
lean_inc_ref(v___y_6651_);
lean_inc(v___y_6650_);
lean_inc_ref(v___y_6649_);
v___x_6742_ = lean_apply_6(v_onRemaining_6525_, v_remaining_6540_, v___y_6649_, v___y_6650_, v___y_6651_, v___y_6652_, lean_box(0));
if (lean_obj_tag(v___x_6742_) == 0)
{
lean_object* v_a_6743_; lean_object* v___x_6745_; uint8_t v_isShared_6746_; uint8_t v_isSharedCheck_6757_; 
v_a_6743_ = lean_ctor_get(v___x_6742_, 0);
v_isSharedCheck_6757_ = !lean_is_exclusive(v___x_6742_);
if (v_isSharedCheck_6757_ == 0)
{
v___x_6745_ = v___x_6742_;
v_isShared_6746_ = v_isSharedCheck_6757_;
goto v_resetjp_6744_;
}
else
{
lean_inc(v_a_6743_);
lean_dec(v___x_6742_);
v___x_6745_ = lean_box(0);
v_isShared_6746_ = v_isSharedCheck_6757_;
goto v_resetjp_6744_;
}
v_resetjp_6744_:
{
lean_object* v_remaining_x27_6747_; lean_object* v___x_6749_; 
v_remaining_x27_6747_ = l_Array_append___redArg(v_fst_6670_, v_a_6743_);
lean_dec(v_a_6743_);
if (v_isShared_6722_ == 0)
{
lean_ctor_set(v___x_6721_, 5, v_overlaps_6718_);
lean_ctor_set(v___x_6721_, 4, v___y_6645_);
lean_ctor_set(v___x_6721_, 3, v_uElimPos_x3f_6717_);
lean_ctor_set(v___x_6721_, 2, v_altInfos_6716_);
lean_ctor_set(v___x_6721_, 1, v_numDiscrs_6715_);
lean_ctor_set(v___x_6721_, 0, v_numParams_6714_);
v___x_6749_ = v___x_6721_;
goto v_reusejp_6748_;
}
else
{
lean_object* v_reuseFailAlloc_6756_; 
v_reuseFailAlloc_6756_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6756_, 0, v_numParams_6714_);
lean_ctor_set(v_reuseFailAlloc_6756_, 1, v_numDiscrs_6715_);
lean_ctor_set(v_reuseFailAlloc_6756_, 2, v_altInfos_6716_);
lean_ctor_set(v_reuseFailAlloc_6756_, 3, v_uElimPos_x3f_6717_);
lean_ctor_set(v_reuseFailAlloc_6756_, 4, v___y_6645_);
lean_ctor_set(v_reuseFailAlloc_6756_, 5, v_overlaps_6718_);
v___x_6749_ = v_reuseFailAlloc_6756_;
goto v_reusejp_6748_;
}
v_reusejp_6748_:
{
lean_object* v___x_6751_; 
if (v_isShared_6669_ == 0)
{
lean_ctor_set(v___x_6668_, 7, v_remaining_x27_6747_);
lean_ctor_set(v___x_6668_, 6, v_fst_6741_);
lean_ctor_set(v___x_6668_, 5, v___y_6647_);
lean_ctor_set(v___x_6668_, 4, v___y_6646_);
lean_ctor_set(v___x_6668_, 3, v___y_6642_);
lean_ctor_set(v___x_6668_, 2, v_matcherLevels_6648_);
lean_ctor_set(v___x_6668_, 1, v_splitterName_6698_);
lean_ctor_set(v___x_6668_, 0, v___x_6749_);
v___x_6751_ = v___x_6668_;
goto v_reusejp_6750_;
}
else
{
lean_object* v_reuseFailAlloc_6755_; 
v_reuseFailAlloc_6755_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6755_, 0, v___x_6749_);
lean_ctor_set(v_reuseFailAlloc_6755_, 1, v_splitterName_6698_);
lean_ctor_set(v_reuseFailAlloc_6755_, 2, v_matcherLevels_6648_);
lean_ctor_set(v_reuseFailAlloc_6755_, 3, v___y_6642_);
lean_ctor_set(v_reuseFailAlloc_6755_, 4, v___y_6646_);
lean_ctor_set(v_reuseFailAlloc_6755_, 5, v___y_6647_);
lean_ctor_set(v_reuseFailAlloc_6755_, 6, v_fst_6741_);
lean_ctor_set(v_reuseFailAlloc_6755_, 7, v_remaining_x27_6747_);
v___x_6751_ = v_reuseFailAlloc_6755_;
goto v_reusejp_6750_;
}
v_reusejp_6750_:
{
lean_object* v___x_6753_; 
if (v_isShared_6746_ == 0)
{
lean_ctor_set(v___x_6745_, 0, v___x_6751_);
v___x_6753_ = v___x_6745_;
goto v_reusejp_6752_;
}
else
{
lean_object* v_reuseFailAlloc_6754_; 
v_reuseFailAlloc_6754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6754_, 0, v___x_6751_);
v___x_6753_ = v_reuseFailAlloc_6754_;
goto v_reusejp_6752_;
}
v_reusejp_6752_:
{
return v___x_6753_;
}
}
}
}
}
else
{
lean_object* v_a_6758_; lean_object* v___x_6760_; uint8_t v_isShared_6761_; uint8_t v_isSharedCheck_6765_; 
lean_dec(v_fst_6741_);
lean_del_object(v___x_6721_);
lean_dec_ref(v_overlaps_6718_);
lean_dec(v_uElimPos_x3f_6717_);
lean_dec_ref(v_altInfos_6716_);
lean_dec(v_numDiscrs_6715_);
lean_dec(v_numParams_6714_);
lean_dec(v_splitterName_6698_);
lean_dec(v_fst_6670_);
lean_del_object(v___x_6668_);
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
v_a_6758_ = lean_ctor_get(v___x_6742_, 0);
v_isSharedCheck_6765_ = !lean_is_exclusive(v___x_6742_);
if (v_isSharedCheck_6765_ == 0)
{
v___x_6760_ = v___x_6742_;
v_isShared_6761_ = v_isSharedCheck_6765_;
goto v_resetjp_6759_;
}
else
{
lean_inc(v_a_6758_);
lean_dec(v___x_6742_);
v___x_6760_ = lean_box(0);
v_isShared_6761_ = v_isSharedCheck_6765_;
goto v_resetjp_6759_;
}
v_resetjp_6759_:
{
lean_object* v___x_6763_; 
if (v_isShared_6761_ == 0)
{
v___x_6763_ = v___x_6760_;
goto v_reusejp_6762_;
}
else
{
lean_object* v_reuseFailAlloc_6764_; 
v_reuseFailAlloc_6764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6764_, 0, v_a_6758_);
v___x_6763_ = v_reuseFailAlloc_6764_;
goto v_reusejp_6762_;
}
v_reusejp_6762_:
{
return v___x_6763_;
}
}
}
}
else
{
lean_object* v_a_6766_; lean_object* v___x_6768_; uint8_t v_isShared_6769_; uint8_t v_isSharedCheck_6773_; 
lean_del_object(v___x_6721_);
lean_dec_ref(v_overlaps_6718_);
lean_dec(v_uElimPos_x3f_6717_);
lean_dec_ref(v_altInfos_6716_);
lean_dec(v_numDiscrs_6715_);
lean_dec(v_numParams_6714_);
lean_dec(v_splitterName_6698_);
lean_dec(v_fst_6670_);
lean_del_object(v___x_6668_);
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_onRemaining_6525_);
v_a_6766_ = lean_ctor_get(v___x_6739_, 0);
v_isSharedCheck_6773_ = !lean_is_exclusive(v___x_6739_);
if (v_isSharedCheck_6773_ == 0)
{
v___x_6768_ = v___x_6739_;
v_isShared_6769_ = v_isSharedCheck_6773_;
goto v_resetjp_6767_;
}
else
{
lean_inc(v_a_6766_);
lean_dec(v___x_6739_);
v___x_6768_ = lean_box(0);
v_isShared_6769_ = v_isSharedCheck_6773_;
goto v_resetjp_6767_;
}
v_resetjp_6767_:
{
lean_object* v___x_6771_; 
if (v_isShared_6769_ == 0)
{
v___x_6771_ = v___x_6768_;
goto v_reusejp_6770_;
}
else
{
lean_object* v_reuseFailAlloc_6772_; 
v_reuseFailAlloc_6772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6772_, 0, v_a_6766_);
v___x_6771_ = v_reuseFailAlloc_6772_;
goto v_reusejp_6770_;
}
v_reusejp_6770_:
{
return v___x_6771_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6782_; lean_object* v___x_6784_; uint8_t v_isShared_6785_; uint8_t v_isSharedCheck_6789_; 
lean_dec_ref(v_splitterMatchInfo_6699_);
lean_dec(v_splitterName_6698_);
lean_dec(v_a_6695_);
lean_del_object(v___x_6676_);
lean_dec(v_fst_6674_);
lean_del_object(v___x_6672_);
lean_dec(v_fst_6670_);
lean_del_object(v___x_6668_);
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
v_a_6782_ = lean_ctor_get(v___x_6712_, 0);
v_isSharedCheck_6789_ = !lean_is_exclusive(v___x_6712_);
if (v_isSharedCheck_6789_ == 0)
{
v___x_6784_ = v___x_6712_;
v_isShared_6785_ = v_isSharedCheck_6789_;
goto v_resetjp_6783_;
}
else
{
lean_inc(v_a_6782_);
lean_dec(v___x_6712_);
v___x_6784_ = lean_box(0);
v_isShared_6785_ = v_isSharedCheck_6789_;
goto v_resetjp_6783_;
}
v_resetjp_6783_:
{
lean_object* v___x_6787_; 
if (v_isShared_6785_ == 0)
{
v___x_6787_ = v___x_6784_;
goto v_reusejp_6786_;
}
else
{
lean_object* v_reuseFailAlloc_6788_; 
v_reuseFailAlloc_6788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6788_, 0, v_a_6782_);
v___x_6787_ = v_reuseFailAlloc_6788_;
goto v_reusejp_6786_;
}
v_reusejp_6786_:
{
return v___x_6787_;
}
}
}
}
else
{
lean_object* v_a_6790_; lean_object* v___x_6792_; uint8_t v_isShared_6793_; uint8_t v_isSharedCheck_6797_; 
lean_dec_ref(v_aux2_6703_);
lean_dec_ref(v_splitterMatchInfo_6699_);
lean_dec(v_splitterName_6698_);
lean_dec(v_a_6695_);
lean_del_object(v___x_6676_);
lean_dec(v_fst_6674_);
lean_del_object(v___x_6672_);
lean_dec(v_fst_6670_);
lean_del_object(v___x_6668_);
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
v_a_6790_ = lean_ctor_get(v___x_6711_, 0);
v_isSharedCheck_6797_ = !lean_is_exclusive(v___x_6711_);
if (v_isSharedCheck_6797_ == 0)
{
v___x_6792_ = v___x_6711_;
v_isShared_6793_ = v_isSharedCheck_6797_;
goto v_resetjp_6791_;
}
else
{
lean_inc(v_a_6790_);
lean_dec(v___x_6711_);
v___x_6792_ = lean_box(0);
v_isShared_6793_ = v_isSharedCheck_6797_;
goto v_resetjp_6791_;
}
v_resetjp_6791_:
{
lean_object* v___x_6795_; 
if (v_isShared_6793_ == 0)
{
v___x_6795_ = v___x_6792_;
goto v_reusejp_6794_;
}
else
{
lean_object* v_reuseFailAlloc_6796_; 
v_reuseFailAlloc_6796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6796_, 0, v_a_6790_);
v___x_6795_ = v_reuseFailAlloc_6796_;
goto v_reusejp_6794_;
}
v_reusejp_6794_:
{
return v___x_6795_;
}
}
}
}
else
{
lean_object* v_a_6798_; lean_object* v___x_6800_; uint8_t v_isShared_6801_; uint8_t v_isSharedCheck_6805_; 
lean_dec(v_a_6695_);
lean_dec(v___x_6678_);
lean_del_object(v___x_6676_);
lean_dec(v_fst_6674_);
lean_del_object(v___x_6672_);
lean_dec(v_fst_6670_);
lean_del_object(v___x_6668_);
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
v_a_6798_ = lean_ctor_get(v___x_6696_, 0);
v_isSharedCheck_6805_ = !lean_is_exclusive(v___x_6696_);
if (v_isSharedCheck_6805_ == 0)
{
v___x_6800_ = v___x_6696_;
v_isShared_6801_ = v_isSharedCheck_6805_;
goto v_resetjp_6799_;
}
else
{
lean_inc(v_a_6798_);
lean_dec(v___x_6696_);
v___x_6800_ = lean_box(0);
v_isShared_6801_ = v_isSharedCheck_6805_;
goto v_resetjp_6799_;
}
v_resetjp_6799_:
{
lean_object* v___x_6803_; 
if (v_isShared_6801_ == 0)
{
v___x_6803_ = v___x_6800_;
goto v_reusejp_6802_;
}
else
{
lean_object* v_reuseFailAlloc_6804_; 
v_reuseFailAlloc_6804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6804_, 0, v_a_6798_);
v___x_6803_ = v_reuseFailAlloc_6804_;
goto v_reusejp_6802_;
}
v_reusejp_6802_:
{
return v___x_6803_;
}
}
}
}
else
{
lean_object* v_a_6806_; lean_object* v___x_6808_; uint8_t v_isShared_6809_; uint8_t v_isSharedCheck_6813_; 
lean_dec(v___x_6678_);
lean_del_object(v___x_6676_);
lean_dec(v_fst_6674_);
lean_del_object(v___x_6672_);
lean_dec(v_fst_6670_);
lean_del_object(v___x_6668_);
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
v_a_6806_ = lean_ctor_get(v___x_6694_, 0);
v_isSharedCheck_6813_ = !lean_is_exclusive(v___x_6694_);
if (v_isSharedCheck_6813_ == 0)
{
v___x_6808_ = v___x_6694_;
v_isShared_6809_ = v_isSharedCheck_6813_;
goto v_resetjp_6807_;
}
else
{
lean_inc(v_a_6806_);
lean_dec(v___x_6694_);
v___x_6808_ = lean_box(0);
v_isShared_6809_ = v_isSharedCheck_6813_;
goto v_resetjp_6807_;
}
v_resetjp_6807_:
{
lean_object* v___x_6811_; 
if (v_isShared_6809_ == 0)
{
v___x_6811_ = v___x_6808_;
goto v_reusejp_6810_;
}
else
{
lean_object* v_reuseFailAlloc_6812_; 
v_reuseFailAlloc_6812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6812_, 0, v_a_6806_);
v___x_6811_ = v_reuseFailAlloc_6812_;
goto v_reusejp_6810_;
}
v_reusejp_6810_:
{
return v___x_6811_;
}
}
}
}
else
{
lean_object* v_a_6814_; lean_object* v___x_6816_; uint8_t v_isShared_6817_; uint8_t v_isSharedCheck_6821_; 
lean_dec_ref(v_aux1_6682_);
lean_dec(v___x_6678_);
lean_del_object(v___x_6676_);
lean_dec(v_fst_6674_);
lean_del_object(v___x_6672_);
lean_dec(v_fst_6670_);
lean_del_object(v___x_6668_);
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
v_a_6814_ = lean_ctor_get(v___x_6692_, 0);
v_isSharedCheck_6821_ = !lean_is_exclusive(v___x_6692_);
if (v_isSharedCheck_6821_ == 0)
{
v___x_6816_ = v___x_6692_;
v_isShared_6817_ = v_isSharedCheck_6821_;
goto v_resetjp_6815_;
}
else
{
lean_inc(v_a_6814_);
lean_dec(v___x_6692_);
v___x_6816_ = lean_box(0);
v_isShared_6817_ = v_isSharedCheck_6821_;
goto v_resetjp_6815_;
}
v_resetjp_6815_:
{
lean_object* v___x_6819_; 
if (v_isShared_6817_ == 0)
{
v___x_6819_ = v___x_6816_;
goto v_reusejp_6818_;
}
else
{
lean_object* v_reuseFailAlloc_6820_; 
v_reuseFailAlloc_6820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6820_, 0, v_a_6814_);
v___x_6819_ = v_reuseFailAlloc_6820_;
goto v_reusejp_6818_;
}
v_reusejp_6818_:
{
return v___x_6819_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6835_; lean_object* v_fst_6836_; 
lean_dec(v___y_6641_);
v_fst_6835_ = lean_ctor_get(v_a_6663_, 0);
lean_inc(v_fst_6835_);
lean_dec(v_a_6663_);
v_fst_6836_ = lean_ctor_get(v_snd_6664_, 0);
lean_inc(v_fst_6836_);
lean_dec(v_snd_6664_);
v___y_6542_ = v_fst_6836_;
v___y_6543_ = v___y_6642_;
v___y_6544_ = v___y_6645_;
v___y_6545_ = v___y_6652_;
v___y_6546_ = v_remaining_x27_6654_;
v___y_6547_ = v___y_6647_;
v___y_6548_ = v_fst_6835_;
v___y_6549_ = v___y_6651_;
v___y_6550_ = v_matcherLevels_6648_;
v___y_6551_ = v___y_6650_;
v___y_6552_ = v___x_6653_;
v___y_6553_ = v___y_6649_;
v___y_6554_ = v___y_6646_;
goto v___jp_6541_;
}
}
}
else
{
lean_object* v_a_6837_; lean_object* v___x_6839_; uint8_t v_isShared_6840_; uint8_t v_isSharedCheck_6844_; 
lean_dec_ref(v_matcherLevels_6648_);
lean_dec_ref(v___y_6647_);
lean_dec_ref(v___y_6646_);
lean_dec_ref(v___y_6645_);
lean_dec_ref(v___y_6642_);
lean_dec(v___y_6641_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
lean_dec_ref(v_matcherApp_6519_);
v_a_6837_ = lean_ctor_get(v___x_6662_, 0);
v_isSharedCheck_6844_ = !lean_is_exclusive(v___x_6662_);
if (v_isSharedCheck_6844_ == 0)
{
v___x_6839_ = v___x_6662_;
v_isShared_6840_ = v_isSharedCheck_6844_;
goto v_resetjp_6838_;
}
else
{
lean_inc(v_a_6837_);
lean_dec(v___x_6662_);
v___x_6839_ = lean_box(0);
v_isShared_6840_ = v_isSharedCheck_6844_;
goto v_resetjp_6838_;
}
v_resetjp_6838_:
{
lean_object* v___x_6842_; 
if (v_isShared_6840_ == 0)
{
v___x_6842_ = v___x_6839_;
goto v_reusejp_6841_;
}
else
{
lean_object* v_reuseFailAlloc_6843_; 
v_reuseFailAlloc_6843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6843_, 0, v_a_6837_);
v___x_6842_ = v_reuseFailAlloc_6843_;
goto v_reusejp_6841_;
}
v_reusejp_6841_:
{
return v___x_6842_;
}
}
}
}
v___jp_6845_:
{
size_t v_sz_6851_; size_t v___x_6852_; lean_object* v___x_6853_; 
v_sz_6851_ = lean_array_size(v_params_6536_);
v___x_6852_ = ((size_t)0ULL);
lean_inc_ref(v_params_6536_);
lean_inc_ref(v_onParams_6522_);
v___x_6853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6522_, v_sz_6851_, v___x_6852_, v_params_6536_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_);
if (lean_obj_tag(v___x_6853_) == 0)
{
lean_object* v_a_6854_; size_t v_sz_6855_; lean_object* v___x_6856_; 
v_a_6854_ = lean_ctor_get(v___x_6853_, 0);
lean_inc(v_a_6854_);
lean_dec_ref_known(v___x_6853_, 1);
v_sz_6855_ = lean_array_size(v_discrs_6538_);
lean_inc_ref(v_discrs_6538_);
v___x_6856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6522_, v_sz_6855_, v___x_6852_, v_discrs_6538_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_);
if (lean_obj_tag(v___x_6856_) == 0)
{
lean_object* v_a_6857_; lean_object* v___x_6858_; lean_object* v___x_6859_; lean_object* v___f_6860_; uint8_t v___x_6861_; lean_object* v___x_6862_; 
v_a_6857_ = lean_ctor_get(v___x_6856_, 0);
lean_inc_n(v_a_6857_, 2);
lean_dec_ref_known(v___x_6856_, 1);
v___x_6858_ = lean_box(v_addEqualities_6521_);
v___x_6859_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6538_);
lean_inc_ref(v_toMatcherInfo_6533_);
v___f_6860_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6860_, 0, v_onMotive_6523_);
lean_closure_set(v___f_6860_, 1, v_toMatcherInfo_6533_);
lean_closure_set(v___f_6860_, 2, v_a_6857_);
lean_closure_set(v___f_6860_, 3, v___x_6858_);
lean_closure_set(v___f_6860_, 4, v___x_6859_);
lean_closure_set(v___f_6860_, 5, v_discrs_6538_);
v___x_6861_ = 0;
lean_inc_ref(v_motive_6537_);
v___x_6862_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6537_, v___f_6860_, v___x_6861_, v___y_6847_, v___y_6848_, v___y_6849_, v___y_6850_);
if (lean_obj_tag(v___x_6862_) == 0)
{
lean_object* v_a_6863_; lean_object* v_snd_6864_; lean_object* v_snd_6865_; lean_object* v_uElimPos_x3f_6866_; 
v_a_6863_ = lean_ctor_get(v___x_6862_, 0);
lean_inc(v_a_6863_);
lean_dec_ref_known(v___x_6862_, 1);
v_snd_6864_ = lean_ctor_get(v_a_6863_, 1);
v_snd_6865_ = lean_ctor_get(v_snd_6864_, 1);
lean_inc(v_snd_6865_);
v_uElimPos_x3f_6866_ = lean_ctor_get(v_toMatcherInfo_6533_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6866_) == 0)
{
lean_object* v_fst_6867_; lean_object* v_fst_6868_; lean_object* v_snd_6869_; 
v_fst_6867_ = lean_ctor_get(v_a_6863_, 0);
lean_inc(v_fst_6867_);
lean_dec(v_a_6863_);
v_fst_6868_ = lean_ctor_get(v_snd_6865_, 0);
lean_inc(v_fst_6868_);
v_snd_6869_ = lean_ctor_get(v_snd_6865_, 1);
lean_inc(v_snd_6869_);
lean_dec(v_snd_6865_);
lean_inc_ref(v_matcherLevels_6535_);
v___y_6641_ = v_numDiscrEqs_6846_;
v___y_6642_ = v_a_6854_;
v___y_6643_ = v___x_6852_;
v___y_6644_ = v_fst_6868_;
v___y_6645_ = v_snd_6869_;
v___y_6646_ = v_fst_6867_;
v___y_6647_ = v_a_6857_;
v_matcherLevels_6648_ = v_matcherLevels_6535_;
v___y_6649_ = v___y_6847_;
v___y_6650_ = v___y_6848_;
v___y_6651_ = v___y_6849_;
v___y_6652_ = v___y_6850_;
goto v___jp_6640_;
}
else
{
lean_object* v_fst_6870_; lean_object* v_fst_6871_; lean_object* v_fst_6872_; lean_object* v_snd_6873_; lean_object* v_val_6874_; lean_object* v___x_6875_; 
lean_inc(v_snd_6864_);
v_fst_6870_ = lean_ctor_get(v_a_6863_, 0);
lean_inc(v_fst_6870_);
lean_dec(v_a_6863_);
v_fst_6871_ = lean_ctor_get(v_snd_6864_, 0);
lean_inc(v_fst_6871_);
lean_dec(v_snd_6864_);
v_fst_6872_ = lean_ctor_get(v_snd_6865_, 0);
lean_inc(v_fst_6872_);
v_snd_6873_ = lean_ctor_get(v_snd_6865_, 1);
lean_inc(v_snd_6873_);
lean_dec(v_snd_6865_);
v_val_6874_ = lean_ctor_get(v_uElimPos_x3f_6866_, 0);
lean_inc_ref(v_matcherLevels_6535_);
v___x_6875_ = lean_array_set(v_matcherLevels_6535_, v_val_6874_, v_fst_6871_);
v___y_6641_ = v_numDiscrEqs_6846_;
v___y_6642_ = v_a_6854_;
v___y_6643_ = v___x_6852_;
v___y_6644_ = v_fst_6872_;
v___y_6645_ = v_snd_6873_;
v___y_6646_ = v_fst_6870_;
v___y_6647_ = v_a_6857_;
v_matcherLevels_6648_ = v___x_6875_;
v___y_6649_ = v___y_6847_;
v___y_6650_ = v___y_6848_;
v___y_6651_ = v___y_6849_;
v___y_6652_ = v___y_6850_;
goto v___jp_6640_;
}
}
else
{
lean_object* v_a_6876_; lean_object* v___x_6878_; uint8_t v_isShared_6879_; uint8_t v_isSharedCheck_6883_; 
lean_dec(v_a_6857_);
lean_dec(v_a_6854_);
lean_dec(v_numDiscrEqs_6846_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
lean_dec_ref(v_matcherApp_6519_);
v_a_6876_ = lean_ctor_get(v___x_6862_, 0);
v_isSharedCheck_6883_ = !lean_is_exclusive(v___x_6862_);
if (v_isSharedCheck_6883_ == 0)
{
v___x_6878_ = v___x_6862_;
v_isShared_6879_ = v_isSharedCheck_6883_;
goto v_resetjp_6877_;
}
else
{
lean_inc(v_a_6876_);
lean_dec(v___x_6862_);
v___x_6878_ = lean_box(0);
v_isShared_6879_ = v_isSharedCheck_6883_;
goto v_resetjp_6877_;
}
v_resetjp_6877_:
{
lean_object* v___x_6881_; 
if (v_isShared_6879_ == 0)
{
v___x_6881_ = v___x_6878_;
goto v_reusejp_6880_;
}
else
{
lean_object* v_reuseFailAlloc_6882_; 
v_reuseFailAlloc_6882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6882_, 0, v_a_6876_);
v___x_6881_ = v_reuseFailAlloc_6882_;
goto v_reusejp_6880_;
}
v_reusejp_6880_:
{
return v___x_6881_;
}
}
}
}
else
{
lean_object* v_a_6884_; lean_object* v___x_6886_; uint8_t v_isShared_6887_; uint8_t v_isSharedCheck_6891_; 
lean_dec(v_a_6854_);
lean_dec(v_numDiscrEqs_6846_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
lean_dec_ref(v_onMotive_6523_);
lean_dec_ref(v_matcherApp_6519_);
v_a_6884_ = lean_ctor_get(v___x_6856_, 0);
v_isSharedCheck_6891_ = !lean_is_exclusive(v___x_6856_);
if (v_isSharedCheck_6891_ == 0)
{
v___x_6886_ = v___x_6856_;
v_isShared_6887_ = v_isSharedCheck_6891_;
goto v_resetjp_6885_;
}
else
{
lean_inc(v_a_6884_);
lean_dec(v___x_6856_);
v___x_6886_ = lean_box(0);
v_isShared_6887_ = v_isSharedCheck_6891_;
goto v_resetjp_6885_;
}
v_resetjp_6885_:
{
lean_object* v___x_6889_; 
if (v_isShared_6887_ == 0)
{
v___x_6889_ = v___x_6886_;
goto v_reusejp_6888_;
}
else
{
lean_object* v_reuseFailAlloc_6890_; 
v_reuseFailAlloc_6890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6890_, 0, v_a_6884_);
v___x_6889_ = v_reuseFailAlloc_6890_;
goto v_reusejp_6888_;
}
v_reusejp_6888_:
{
return v___x_6889_;
}
}
}
}
else
{
lean_object* v_a_6892_; lean_object* v___x_6894_; uint8_t v_isShared_6895_; uint8_t v_isSharedCheck_6899_; 
lean_dec(v_numDiscrEqs_6846_);
lean_dec_ref(v_remaining_6540_);
lean_dec_ref(v_alts_6539_);
lean_dec(v_matcherName_6534_);
lean_dec_ref(v_toMatcherInfo_6533_);
lean_dec_ref(v_onRemaining_6525_);
lean_dec_ref(v_onAlt_6524_);
lean_dec_ref(v_onMotive_6523_);
lean_dec_ref(v_onParams_6522_);
lean_dec_ref(v_matcherApp_6519_);
v_a_6892_ = lean_ctor_get(v___x_6853_, 0);
v_isSharedCheck_6899_ = !lean_is_exclusive(v___x_6853_);
if (v_isSharedCheck_6899_ == 0)
{
v___x_6894_ = v___x_6853_;
v_isShared_6895_ = v_isSharedCheck_6899_;
goto v_resetjp_6893_;
}
else
{
lean_inc(v_a_6892_);
lean_dec(v___x_6853_);
v___x_6894_ = lean_box(0);
v_isShared_6895_ = v_isSharedCheck_6899_;
goto v_resetjp_6893_;
}
v_resetjp_6893_:
{
lean_object* v___x_6897_; 
if (v_isShared_6895_ == 0)
{
v___x_6897_ = v___x_6894_;
goto v_reusejp_6896_;
}
else
{
lean_object* v_reuseFailAlloc_6898_; 
v_reuseFailAlloc_6898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6898_, 0, v_a_6892_);
v___x_6897_ = v_reuseFailAlloc_6898_;
goto v_reusejp_6896_;
}
v_reusejp_6896_:
{
return v___x_6897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6919_, lean_object* v_useSplitter_6920_, lean_object* v_addEqualities_6921_, lean_object* v_onParams_6922_, lean_object* v_onMotive_6923_, lean_object* v_onAlt_6924_, lean_object* v_onRemaining_6925_, lean_object* v___y_6926_, lean_object* v___y_6927_, lean_object* v___y_6928_, lean_object* v___y_6929_, lean_object* v___y_6930_){
_start:
{
uint8_t v_useSplitter_boxed_6931_; uint8_t v_addEqualities_boxed_6932_; lean_object* v_res_6933_; 
v_useSplitter_boxed_6931_ = lean_unbox(v_useSplitter_6920_);
v_addEqualities_boxed_6932_ = lean_unbox(v_addEqualities_6921_);
v_res_6933_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6919_, v_useSplitter_boxed_6931_, v_addEqualities_boxed_6932_, v_onParams_6922_, v_onMotive_6923_, v_onAlt_6924_, v_onRemaining_6925_, v___y_6926_, v___y_6927_, v___y_6928_, v___y_6929_);
lean_dec(v___y_6929_);
lean_dec_ref(v___y_6928_);
lean_dec(v___y_6927_);
lean_dec_ref(v___y_6926_);
return v_res_6933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6939_, lean_object* v_a_6940_, lean_object* v_a_6941_, lean_object* v_a_6942_, lean_object* v_a_6943_){
_start:
{
lean_object* v_toMatcherInfo_6945_; lean_object* v_matcherName_6946_; lean_object* v_matcherLevels_6947_; lean_object* v_params_6948_; lean_object* v_alts_6949_; lean_object* v_remaining_6950_; lean_object* v___f_6951_; lean_object* v___f_6952_; lean_object* v_nExtra_6953_; uint8_t v___x_6954_; lean_object* v___f_6955_; uint8_t v___x_6956_; lean_object* v___x_6957_; lean_object* v___x_6958_; lean_object* v___f_6959_; lean_object* v___x_6960_; 
v_toMatcherInfo_6945_ = lean_ctor_get(v_matcherApp_6939_, 0);
v_matcherName_6946_ = lean_ctor_get(v_matcherApp_6939_, 1);
v_matcherLevels_6947_ = lean_ctor_get(v_matcherApp_6939_, 2);
v_params_6948_ = lean_ctor_get(v_matcherApp_6939_, 3);
v_alts_6949_ = lean_ctor_get(v_matcherApp_6939_, 6);
v_remaining_6950_ = lean_ctor_get(v_matcherApp_6939_, 7);
v___f_6951_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6952_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6953_ = lean_array_get_size(v_remaining_6950_);
v___x_6954_ = 1;
v___f_6955_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6956_ = 0;
v___x_6957_ = lean_box(v___x_6956_);
v___x_6958_ = lean_box(v___x_6954_);
lean_inc_ref(v_matcherLevels_6947_);
lean_inc_ref(v_params_6948_);
lean_inc(v_matcherName_6946_);
lean_inc_ref(v_toMatcherInfo_6945_);
lean_inc_ref(v_alts_6949_);
v___f_6959_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6959_, 0, v_nExtra_6953_);
lean_closure_set(v___f_6959_, 1, v___x_6957_);
lean_closure_set(v___f_6959_, 2, v___x_6958_);
lean_closure_set(v___f_6959_, 3, v_alts_6949_);
lean_closure_set(v___f_6959_, 4, v_toMatcherInfo_6945_);
lean_closure_set(v___f_6959_, 5, v_matcherName_6946_);
lean_closure_set(v___f_6959_, 6, v_params_6948_);
lean_closure_set(v___f_6959_, 7, v_matcherLevels_6947_);
v___x_6960_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6939_, v___x_6954_, v___x_6956_, v___f_6951_, v___f_6959_, v___f_6955_, v___f_6952_, v_a_6940_, v_a_6941_, v_a_6942_, v_a_6943_);
return v___x_6960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6961_, lean_object* v_a_6962_, lean_object* v_a_6963_, lean_object* v_a_6964_, lean_object* v_a_6965_, lean_object* v_a_6966_){
_start:
{
lean_object* v_res_6967_; 
v_res_6967_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6961_, v_a_6962_, v_a_6963_, v_a_6964_, v_a_6965_);
lean_dec(v_a_6965_);
lean_dec_ref(v_a_6964_);
lean_dec(v_a_6963_);
lean_dec_ref(v_a_6962_);
return v_res_6967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6968_, lean_object* v_termAlt_6969_, lean_object* v_inst_6970_, lean_object* v_R_6971_, lean_object* v_a_6972_, lean_object* v_b_6973_, lean_object* v_c_6974_, lean_object* v___y_6975_, lean_object* v___y_6976_, lean_object* v___y_6977_, lean_object* v___y_6978_){
_start:
{
lean_object* v___x_6980_; 
v___x_6980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6968_, v_termAlt_6969_, v_a_6972_, v_b_6973_, v___y_6975_, v___y_6976_, v___y_6977_, v___y_6978_);
return v___x_6980_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6981_, lean_object* v_termAlt_6982_, lean_object* v_inst_6983_, lean_object* v_R_6984_, lean_object* v_a_6985_, lean_object* v_b_6986_, lean_object* v_c_6987_, lean_object* v___y_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_, lean_object* v___y_6991_, lean_object* v___y_6992_){
_start:
{
lean_object* v_res_6993_; 
v_res_6993_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6981_, v_termAlt_6982_, v_inst_6983_, v_R_6984_, v_a_6985_, v_b_6986_, v_c_6987_, v___y_6988_, v___y_6989_, v___y_6990_, v___y_6991_);
lean_dec(v___y_6991_);
lean_dec_ref(v___y_6990_);
lean_dec(v___y_6989_);
lean_dec_ref(v___y_6988_);
return v_res_6993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6994_, lean_object* v_fvars_6995_, lean_object* v_names_6996_, lean_object* v_k_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_, lean_object* v___y_7000_, lean_object* v___y_7001_){
_start:
{
lean_object* v___x_7003_; 
v___x_7003_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6995_, v_names_6996_, v_k_6997_, v___y_6998_, v___y_6999_, v___y_7000_, v___y_7001_);
return v___x_7003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_7004_, lean_object* v_fvars_7005_, lean_object* v_names_7006_, lean_object* v_k_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_, lean_object* v___y_7011_, lean_object* v___y_7012_){
_start:
{
lean_object* v_res_7013_; 
v_res_7013_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_7004_, v_fvars_7005_, v_names_7006_, v_k_7007_, v___y_7008_, v___y_7009_, v___y_7010_, v___y_7011_);
lean_dec(v___y_7011_);
lean_dec_ref(v___y_7010_);
lean_dec(v___y_7009_);
lean_dec_ref(v___y_7008_);
lean_dec_ref(v_names_7006_);
lean_dec_ref(v_fvars_7005_);
return v_res_7013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7014_, lean_object* v_origAltType_7015_, lean_object* v_altInfo_7016_, lean_object* v_k_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_, lean_object* v___y_7020_, lean_object* v___y_7021_){
_start:
{
lean_object* v___x_7023_; 
v___x_7023_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7015_, v_altInfo_7016_, v_k_7017_, v___y_7018_, v___y_7019_, v___y_7020_, v___y_7021_);
return v___x_7023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7024_, lean_object* v_origAltType_7025_, lean_object* v_altInfo_7026_, lean_object* v_k_7027_, lean_object* v___y_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_, lean_object* v___y_7032_){
_start:
{
lean_object* v_res_7033_; 
v_res_7033_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7024_, v_origAltType_7025_, v_altInfo_7026_, v_k_7027_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_);
lean_dec(v___y_7031_);
lean_dec_ref(v___y_7030_);
lean_dec(v___y_7029_);
lean_dec_ref(v___y_7028_);
return v_res_7033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_, lean_object* v___y_7037_, lean_object* v___y_7038_){
_start:
{
lean_object* v___x_7040_; 
v___x_7040_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7034_, v___y_7038_);
return v___x_7040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7041_, lean_object* v___y_7042_, lean_object* v___y_7043_, lean_object* v___y_7044_, lean_object* v___y_7045_, lean_object* v___y_7046_){
_start:
{
lean_object* v_res_7047_; 
v_res_7047_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
lean_dec(v___y_7045_);
lean_dec_ref(v___y_7044_);
lean_dec(v___y_7043_);
lean_dec_ref(v___y_7042_);
return v_res_7047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7048_, size_t v_i_7049_, lean_object* v_bs_7050_, lean_object* v___y_7051_, lean_object* v___y_7052_, lean_object* v___y_7053_, lean_object* v___y_7054_){
_start:
{
lean_object* v___x_7056_; 
v___x_7056_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7048_, v_i_7049_, v_bs_7050_, v___y_7051_, v___y_7053_, v___y_7054_);
return v___x_7056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7057_, lean_object* v_i_7058_, lean_object* v_bs_7059_, lean_object* v___y_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_){
_start:
{
size_t v_sz_boxed_7065_; size_t v_i_boxed_7066_; lean_object* v_res_7067_; 
v_sz_boxed_7065_ = lean_unbox_usize(v_sz_7057_);
lean_dec(v_sz_7057_);
v_i_boxed_7066_ = lean_unbox_usize(v_i_7058_);
lean_dec(v_i_7058_);
v_res_7067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7065_, v_i_boxed_7066_, v_bs_7059_, v___y_7060_, v___y_7061_, v___y_7062_, v___y_7063_);
lean_dec(v___y_7063_);
lean_dec_ref(v___y_7062_);
lean_dec(v___y_7061_);
lean_dec_ref(v___y_7060_);
return v_res_7067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7068_, lean_object* v_onAlt_7069_, lean_object* v_extraEqualities_7070_, lean_object* v_inst_7071_, lean_object* v_R_7072_, lean_object* v_a_7073_, lean_object* v_b_7074_, lean_object* v_c_7075_, lean_object* v___y_7076_, lean_object* v___y_7077_, lean_object* v___y_7078_, lean_object* v___y_7079_){
_start:
{
lean_object* v___x_7081_; 
v___x_7081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7068_, v_onAlt_7069_, v_extraEqualities_7070_, v_a_7073_, v_b_7074_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_);
return v___x_7081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7082_, lean_object* v_onAlt_7083_, lean_object* v_extraEqualities_7084_, lean_object* v_inst_7085_, lean_object* v_R_7086_, lean_object* v_a_7087_, lean_object* v_b_7088_, lean_object* v_c_7089_, lean_object* v___y_7090_, lean_object* v___y_7091_, lean_object* v___y_7092_, lean_object* v___y_7093_, lean_object* v___y_7094_){
_start:
{
lean_object* v_res_7095_; 
v_res_7095_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7082_, v_onAlt_7083_, v_extraEqualities_7084_, v_inst_7085_, v_R_7086_, v_a_7087_, v_b_7088_, v_c_7089_, v___y_7090_, v___y_7091_, v___y_7092_, v___y_7093_);
lean_dec(v___y_7093_);
lean_dec_ref(v___y_7092_);
lean_dec(v___y_7091_);
lean_dec_ref(v___y_7090_);
lean_dec(v_upperBound_7082_);
return v_res_7095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7096_, lean_object* v_onAlt_7097_, uint8_t v_useSplitter_7098_, lean_object* v_extraEqualities_7099_, lean_object* v_numDiscrEqs_7100_, lean_object* v_inst_7101_, lean_object* v_R_7102_, lean_object* v_a_7103_, lean_object* v_b_7104_, lean_object* v_c_7105_, lean_object* v___y_7106_, lean_object* v___y_7107_, lean_object* v___y_7108_, lean_object* v___y_7109_){
_start:
{
lean_object* v___x_7111_; 
v___x_7111_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7096_, v_onAlt_7097_, v_useSplitter_7098_, v_extraEqualities_7099_, v_numDiscrEqs_7100_, v_a_7103_, v_b_7104_, v___y_7106_, v___y_7107_, v___y_7108_, v___y_7109_);
return v___x_7111_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7112_, lean_object* v_onAlt_7113_, lean_object* v_useSplitter_7114_, lean_object* v_extraEqualities_7115_, lean_object* v_numDiscrEqs_7116_, lean_object* v_inst_7117_, lean_object* v_R_7118_, lean_object* v_a_7119_, lean_object* v_b_7120_, lean_object* v_c_7121_, lean_object* v___y_7122_, lean_object* v___y_7123_, lean_object* v___y_7124_, lean_object* v___y_7125_, lean_object* v___y_7126_){
_start:
{
uint8_t v_useSplitter_boxed_7127_; lean_object* v_res_7128_; 
v_useSplitter_boxed_7127_ = lean_unbox(v_useSplitter_7114_);
v_res_7128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7112_, v_onAlt_7113_, v_useSplitter_boxed_7127_, v_extraEqualities_7115_, v_numDiscrEqs_7116_, v_inst_7117_, v_R_7118_, v_a_7119_, v_b_7120_, v_c_7121_, v___y_7122_, v___y_7123_, v___y_7124_, v___y_7125_);
lean_dec(v___y_7125_);
lean_dec_ref(v___y_7124_);
lean_dec(v___y_7123_);
lean_dec_ref(v___y_7122_);
lean_dec(v_upperBound_7112_);
return v_res_7128_;
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
