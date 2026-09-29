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
uint8_t v___x_3870__boxed_142_; uint8_t v_refined_boxed_143_; lean_object* v_res_144_; 
v___x_3870__boxed_142_ = lean_unbox(v___x_132_);
v_refined_boxed_143_ = lean_unbox(v_refined_133_);
v_res_144_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_xs_130_, v_alt_131_, v___x_3870__boxed_142_, v_refined_boxed_143_, v_unrefinedArgType_134_, v_binderType_135_, v_x_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
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
lean_object* v___x_151_; lean_object* v_env_152_; lean_object* v___x_153_; lean_object* v_toCold_154_; lean_object* v_mctx_155_; lean_object* v_lctx_156_; lean_object* v_options_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_151_ = lean_st_ref_get(v___y_149_);
v_env_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc_ref(v_env_152_);
lean_dec(v___x_151_);
v___x_153_ = lean_st_ref_get(v___y_147_);
v_toCold_154_ = lean_ctor_get(v___y_148_, 0);
v_mctx_155_ = lean_ctor_get(v___x_153_, 0);
lean_inc_ref(v_mctx_155_);
lean_dec(v___x_153_);
v_lctx_156_ = lean_ctor_get(v___y_146_, 2);
v_options_157_ = lean_ctor_get(v_toCold_154_, 2);
lean_inc_ref(v_options_157_);
lean_inc_ref(v_lctx_156_);
v___x_158_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_158_, 0, v_env_152_);
lean_ctor_set(v___x_158_, 1, v_mctx_155_);
lean_ctor_set(v___x_158_, 2, v_lctx_156_);
lean_ctor_set(v___x_158_, 3, v_options_157_);
v___x_159_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v_msgData_145_);
v___x_160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object* v_msgData_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msgData_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object* v_msg_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_ref_174_; lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_ref_174_ = lean_ctor_get(v___y_171_, 2);
v___x_175_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msg_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_184_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
lean_inc(v_ref_174_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_ref_174_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set_tag(v___x_178_, 1);
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object* v_msg_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t v___x_204_, uint8_t v_refined_205_, lean_object* v_unrefinedArgType_206_, lean_object* v_binderType_207_, lean_object* v_numParams_208_, lean_object* v_xs_209_, lean_object* v_alt_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; uint8_t v___y_256_; lean_object* v___x_264_; uint8_t v___x_265_; 
v___x_264_ = lean_array_get_size(v_xs_209_);
v___x_265_ = lean_nat_dec_eq(v___x_264_, v_numParams_208_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_266_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5);
v___x_267_ = l_Nat_reprFast(v_numParams_208_);
v___x_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
v___x_269_ = l_Lean_MessageData_ofFormat(v___x_268_);
v___x_270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_266_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__7);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_272_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_dec_ref_known(v___x_273_, 1);
goto v___jp_259_;
}
else
{
lean_object* v_a_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_281_; 
lean_dec_ref(v_alt_210_);
lean_dec_ref(v_xs_209_);
lean_dec_ref(v_binderType_207_);
lean_dec_ref(v_unrefinedArgType_206_);
v_a_274_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_281_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_281_ == 0)
{
v___x_276_ = v___x_273_;
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_a_274_);
lean_dec(v___x_273_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_281_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v___x_279_; 
if (v_isShared_277_ == 0)
{
v___x_279_ = v___x_276_;
goto v_reusejp_278_;
}
else
{
lean_object* v_reuseFailAlloc_280_; 
v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
v___x_279_ = v_reuseFailAlloc_280_;
goto v_reusejp_278_;
}
v_reusejp_278_:
{
return v___x_279_;
}
}
}
}
else
{
lean_dec(v_numParams_208_);
goto v___jp_259_;
}
v___jp_216_:
{
if (lean_obj_tag(v___y_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_223_; 
v_a_222_ = lean_ctor_get(v___y_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref_known(v___y_221_, 1);
v___x_223_ = l_Lean_Meta_whnfForall(v_a_222_, v___y_219_, v___y_220_, v___y_217_, v___y_218_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
if (lean_obj_tag(v_a_224_) == 7)
{
lean_object* v_binderName_225_; lean_object* v_binderType_226_; uint8_t v_binderInfo_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___f_230_; lean_object* v___x_231_; 
v_binderName_225_ = lean_ctor_get(v_a_224_, 0);
lean_inc(v_binderName_225_);
v_binderType_226_ = lean_ctor_get(v_a_224_, 1);
lean_inc_ref_n(v_binderType_226_, 2);
v_binderInfo_227_ = lean_ctor_get_uint8(v_a_224_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_224_, 3);
v___x_228_ = lean_box(v___x_204_);
v___x_229_ = lean_box(v_refined_205_);
v___f_230_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 6);
lean_closure_set(v___f_230_, 0, v_xs_209_);
lean_closure_set(v___f_230_, 1, v_alt_210_);
lean_closure_set(v___f_230_, 2, v___x_228_);
lean_closure_set(v___f_230_, 3, v___x_229_);
lean_closure_set(v___f_230_, 4, v_unrefinedArgType_206_);
lean_closure_set(v___f_230_, 5, v_binderType_226_);
v___x_231_ = l_Lean_Meta_withLocalDeclNoLocalInstanceUpdate___redArg(v_binderName_225_, v_binderInfo_227_, v_binderType_226_, v___f_230_, v___y_219_, v___y_220_, v___y_217_, v___y_218_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_a_224_);
lean_dec_ref(v_alt_210_);
lean_dec_ref(v_xs_209_);
lean_dec_ref(v_unrefinedArgType_206_);
v___x_232_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_233_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_232_, v___y_219_, v___y_220_, v___y_217_, v___y_218_);
return v___x_233_;
}
}
else
{
lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_241_; 
lean_dec_ref(v_alt_210_);
lean_dec_ref(v_xs_209_);
lean_dec_ref(v_unrefinedArgType_206_);
v_a_234_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_241_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_241_ == 0)
{
v___x_236_ = v___x_223_;
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_223_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_241_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_239_; 
if (v_isShared_237_ == 0)
{
v___x_239_ = v___x_236_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v_a_234_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec_ref(v_alt_210_);
lean_dec_ref(v_xs_209_);
lean_dec_ref(v_unrefinedArgType_206_);
v_a_242_ = lean_ctor_get(v___y_221_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___y_221_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___y_221_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___y_221_);
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
v___jp_250_:
{
if (v___y_256_ == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec_ref(v___y_254_);
v___x_257_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_258_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_257_, v___y_253_, v___y_255_, v___y_251_, v___y_252_);
v___y_217_ = v___y_251_;
v___y_218_ = v___y_252_;
v___y_219_ = v___y_253_;
v___y_220_ = v___y_255_;
v___y_221_ = v___x_258_;
goto v___jp_216_;
}
else
{
v___y_217_ = v___y_251_;
v___y_218_ = v___y_252_;
v___y_219_ = v___y_253_;
v___y_220_ = v___y_255_;
v___y_221_ = v___y_254_;
goto v___jp_216_;
}
}
v___jp_259_:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Meta_instantiateForall(v_binderType_207_, v_xs_209_, v___y_211_, v___y_212_, v___y_213_, v___y_214_);
if (lean_obj_tag(v___x_260_) == 0)
{
v___y_217_ = v___y_213_;
v___y_218_ = v___y_214_;
v___y_219_ = v___y_211_;
v___y_220_ = v___y_212_;
v___y_221_ = v___x_260_;
goto v___jp_216_;
}
else
{
lean_object* v_a_261_; uint8_t v___x_262_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
v___x_262_ = l_Lean_Exception_isInterrupt(v_a_261_);
if (v___x_262_ == 0)
{
uint8_t v___x_263_; 
v___x_263_ = l_Lean_Exception_isRuntime(v_a_261_);
v___y_251_ = v___y_213_;
v___y_252_ = v___y_214_;
v___y_253_ = v___y_211_;
v___y_254_ = v___x_260_;
v___y_255_ = v___y_212_;
v___y_256_ = v___x_263_;
goto v___jp_250_;
}
else
{
lean_dec(v_a_261_);
v___y_251_ = v___y_213_;
v___y_252_ = v___y_214_;
v___y_253_ = v___y_211_;
v___y_254_ = v___x_260_;
v___y_255_ = v___y_212_;
v___y_256_ = v___x_262_;
goto v___jp_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* v___x_282_, lean_object* v_refined_283_, lean_object* v_unrefinedArgType_284_, lean_object* v_binderType_285_, lean_object* v_numParams_286_, lean_object* v_xs_287_, lean_object* v_alt_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
uint8_t v___x_4044__boxed_294_; uint8_t v_refined_boxed_295_; lean_object* v_res_296_; 
v___x_4044__boxed_294_ = lean_unbox(v___x_282_);
v_refined_boxed_295_ = lean_unbox(v_refined_283_);
v_res_296_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4044__boxed_294_, v_refined_boxed_295_, v_unrefinedArgType_284_, v_binderType_285_, v_numParams_286_, v_xs_287_, v_alt_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* v_unrefinedArgType_300_, lean_object* v_typeNew_301_, lean_object* v_altNumParams_302_, lean_object* v_alts_303_, uint8_t v_refined_304_, lean_object* v_i_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_array_get_size(v_alts_303_);
v___x_312_ = lean_nat_dec_lt(v_i_305_, v___x_311_);
if (v___x_312_ == 0)
{
lean_dec(v_i_305_);
lean_dec_ref(v_typeNew_301_);
lean_dec_ref(v_unrefinedArgType_300_);
if (v_refined_304_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec_ref(v_alts_303_);
v___x_313_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
v___x_314_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_313_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; 
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v_alts_303_);
return v___x_315_;
}
}
else
{
lean_object* v___x_316_; lean_object* v_alt_317_; lean_object* v_numParams_318_; lean_object* v___x_319_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v_alt_317_ = lean_array_fget_borrowed(v_alts_303_, v_i_305_);
v_numParams_318_ = lean_array_get_borrowed(v___x_316_, v_altNumParams_302_, v_i_305_);
v___x_319_ = l_Lean_Meta_whnfD(v_typeNew_301_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_319_) == 0)
{
lean_object* v_a_320_; 
v_a_320_ = lean_ctor_get(v___x_319_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v___x_319_, 1);
if (lean_obj_tag(v_a_320_) == 7)
{
lean_object* v_binderType_321_; lean_object* v_body_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___f_325_; uint8_t v___x_326_; lean_object* v___x_327_; 
v_binderType_321_ = lean_ctor_get(v_a_320_, 1);
lean_inc_ref(v_binderType_321_);
v_body_322_ = lean_ctor_get(v_a_320_, 2);
lean_inc_ref(v_body_322_);
lean_dec_ref_known(v_a_320_, 3);
v___x_323_ = lean_box(v___x_312_);
v___x_324_ = lean_box(v_refined_304_);
lean_inc_n(v_numParams_318_, 2);
lean_inc_ref(v_unrefinedArgType_300_);
v___f_325_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(v___f_325_, 0, v___x_323_);
lean_closure_set(v___f_325_, 1, v___x_324_);
lean_closure_set(v___f_325_, 2, v_unrefinedArgType_300_);
lean_closure_set(v___f_325_, 3, v_binderType_321_);
lean_closure_set(v___f_325_, 4, v_numParams_318_);
v___x_326_ = 0;
lean_inc(v_alt_317_);
v___x_327_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_alt_317_, v_numParams_318_, v___f_325_, v___x_326_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v_fst_329_ = lean_ctor_get(v_a_328_, 0);
lean_inc(v_fst_329_);
v_snd_330_ = lean_ctor_get(v_a_328_, 1);
lean_inc(v_snd_330_);
lean_dec(v_a_328_);
v___x_331_ = lean_expr_instantiate1(v_body_322_, v_fst_329_);
lean_dec_ref(v_body_322_);
v___x_332_ = lean_array_fset(v_alts_303_, v_i_305_, v_fst_329_);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_i_305_, v___x_333_);
lean_dec(v_i_305_);
v___x_335_ = lean_unbox(v_snd_330_);
lean_dec(v_snd_330_);
v_typeNew_301_ = v___x_331_;
v_alts_303_ = v___x_332_;
v_refined_304_ = v___x_335_;
v_i_305_ = v___x_334_;
goto _start;
}
else
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_344_; 
lean_dec_ref(v_body_322_);
lean_dec(v_i_305_);
lean_dec_ref(v_alts_303_);
lean_dec_ref(v_unrefinedArgType_300_);
v_a_337_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_344_ == 0)
{
v___x_339_ = v___x_327_;
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_327_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_344_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_340_ == 0)
{
v___x_342_ = v___x_339_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_a_337_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
else
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_a_320_);
lean_dec(v_i_305_);
lean_dec_ref(v_alts_303_);
lean_dec_ref(v_unrefinedArgType_300_);
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1);
v___x_346_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_345_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
return v___x_346_;
}
}
else
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_i_305_);
lean_dec_ref(v_alts_303_);
lean_dec_ref(v_unrefinedArgType_300_);
v_a_347_ = lean_ctor_get(v___x_319_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_319_);
if (v_isSharedCheck_354_ == 0)
{
v___x_349_ = v___x_319_;
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_319_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_354_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_352_; 
if (v_isShared_350_ == 0)
{
v___x_352_ = v___x_349_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* v_unrefinedArgType_355_, lean_object* v_typeNew_356_, lean_object* v_altNumParams_357_, lean_object* v_alts_358_, lean_object* v_refined_359_, lean_object* v_i_360_, lean_object* v_a_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
uint8_t v_refined_boxed_366_; lean_object* v_res_367_; 
v_refined_boxed_366_ = lean_unbox(v_refined_359_);
v_res_367_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_355_, v_typeNew_356_, v_altNumParams_357_, v_alts_358_, v_refined_boxed_366_, v_i_360_, v_a_361_, v_a_362_, v_a_363_, v_a_364_);
lean_dec(v_a_364_);
lean_dec_ref(v_a_363_);
lean_dec(v_a_362_);
lean_dec_ref(v_a_361_);
lean_dec_ref(v_altNumParams_357_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* v_00_u03b1_368_, lean_object* v_msg_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* v_00_u03b1_376_, lean_object* v_msg_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(v_00_u03b1_376_, v_msg_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec(v___y_379_);
lean_dec_ref(v___y_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* v_e_384_, lean_object* v_k_385_, uint8_t v_cleanupAnnotations_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v___f_392_; uint8_t v___x_393_; uint8_t v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v___f_392_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_392_, 0, v_k_385_);
v___x_393_ = 1;
v___x_394_ = 0;
v___x_395_ = lean_box(0);
v___x_396_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_384_, v___x_393_, v___x_394_, v___x_393_, v___x_394_, v___x_395_, v___f_392_, v_cleanupAnnotations_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_397_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_396_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_396_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_396_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_396_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_396_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* v_e_413_, lean_object* v_k_414_, lean_object* v_cleanupAnnotations_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_421_; lean_object* v_res_422_; 
v_cleanupAnnotations_boxed_421_ = lean_unbox(v_cleanupAnnotations_415_);
v_res_422_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_413_, v_k_414_, v_cleanupAnnotations_boxed_421_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* v_00_u03b1_423_, lean_object* v_e_424_, lean_object* v_k_425_, uint8_t v_cleanupAnnotations_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_424_, v_k_425_, v_cleanupAnnotations_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* v_00_u03b1_433_, lean_object* v_e_434_, lean_object* v_k_435_, lean_object* v_cleanupAnnotations_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_442_; lean_object* v_res_443_; 
v_cleanupAnnotations_boxed_442_ = lean_unbox(v_cleanupAnnotations_436_);
v_res_443_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(v_00_u03b1_433_, v_e_434_, v_k_435_, v_cleanupAnnotations_boxed_442_, v___y_437_, v___y_438_, v___y_439_, v___y_440_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* v___x_444_, lean_object* v_motiveArgs_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
lean_object* v_zero_448_; uint8_t v_isZero_449_; 
v_zero_448_ = lean_unsigned_to_nat(0u);
v_isZero_449_ = lean_nat_dec_eq(v_x_446_, v_zero_448_);
if (v_isZero_449_ == 1)
{
lean_dec(v_x_446_);
return v_x_447_;
}
else
{
lean_object* v_one_450_; lean_object* v_n_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_one_450_ = lean_unsigned_to_nat(1u);
v_n_451_ = lean_nat_sub(v_x_446_, v_one_450_);
lean_dec(v_x_446_);
v___x_452_ = lean_array_fget_borrowed(v___x_444_, v_n_451_);
v___x_453_ = l_Lean_Expr_isFVar(v___x_452_);
if (v___x_453_ == 0)
{
v_x_446_ = v_n_451_;
goto _start;
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = l_Lean_instInhabitedExpr;
v___x_456_ = lean_array_get_borrowed(v___x_455_, v_motiveArgs_445_, v_n_451_);
lean_inc(v___x_452_);
v___x_457_ = l_Lean_Expr_replaceFVar(v_x_447_, v___x_452_, v___x_456_);
lean_dec_ref(v_x_447_);
v_x_446_ = v_n_451_;
v_x_447_ = v___x_457_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* v___x_459_, lean_object* v_motiveArgs_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_459_, v_motiveArgs_460_, v_x_461_, v_x_462_);
lean_dec_ref(v_motiveArgs_460_);
lean_dec_ref(v___x_459_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* v___x_464_, lean_object* v_motiveArgs_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_zero_468_; uint8_t v_isZero_469_; 
v_zero_468_ = lean_unsigned_to_nat(0u);
v_isZero_469_ = lean_nat_dec_eq(v_x_466_, v_zero_468_);
if (v_isZero_469_ == 1)
{
return v_x_467_;
}
else
{
lean_object* v_one_470_; lean_object* v_n_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_one_470_ = lean_unsigned_to_nat(1u);
v_n_471_ = lean_nat_sub(v_x_466_, v_one_470_);
v___x_472_ = lean_array_fget_borrowed(v___x_464_, v_n_471_);
v___x_473_ = l_Lean_Expr_isFVar(v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; 
v___x_474_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_464_, v_motiveArgs_465_, v_n_471_, v_x_467_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_475_ = l_Lean_instInhabitedExpr;
v___x_476_ = lean_array_get_borrowed(v___x_475_, v_motiveArgs_465_, v_n_471_);
lean_inc(v___x_472_);
v___x_477_ = l_Lean_Expr_replaceFVar(v_x_467_, v___x_472_, v___x_476_);
lean_dec_ref(v_x_467_);
v___x_478_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_464_, v_motiveArgs_465_, v_n_471_, v___x_477_);
return v___x_478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* v___x_479_, lean_object* v_motiveArgs_480_, lean_object* v_x_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v___x_479_, v_motiveArgs_480_, v_x_481_, v_x_482_);
lean_dec(v_x_481_);
lean_dec_ref(v_motiveArgs_480_);
lean_dec_ref(v___x_479_);
return v_res_483_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0));
v___x_486_ = l_Lean_stringToMessageData(v___x_485_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2));
v___x_489_ = l_Lean_stringToMessageData(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4));
v___x_492_ = l_Lean_stringToMessageData(v___x_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_493_, lean_object* v_e_494_, lean_object* v_discrs_495_, lean_object* v_toMatcherInfo_496_, lean_object* v_matcherName_497_, lean_object* v_alts_498_, lean_object* v_remaining_499_, lean_object* v_params_500_, lean_object* v_matcherLevels_501_, lean_object* v_motiveArgs_502_, lean_object* v_motiveBody_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___y_510_; lean_object* v___y_511_; uint8_t v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_566_; lean_object* v___y_567_; lean_object* v_matcherLevels_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_653_ = lean_array_get_size(v_motiveArgs_502_);
v___x_654_ = lean_array_get_size(v_discrs_495_);
v___x_655_ = lean_nat_dec_eq(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec_ref(v_motiveBody_503_);
lean_dec_ref(v_matcherLevels_501_);
lean_dec_ref(v_params_500_);
lean_dec_ref(v_alts_498_);
lean_dec(v_matcherName_497_);
lean_dec_ref(v_toMatcherInfo_496_);
lean_dec_ref(v_discrs_495_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v___x_656_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_657_ = l_Nat_reprFast(v___x_654_);
v___x_658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
v___x_659_ = l_Lean_MessageData_ofFormat(v___x_658_);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_656_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_662_, v___y_504_, v___y_505_, v___y_506_, v___y_507_);
v_a_664_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_663_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
v___y_613_ = v___y_504_;
v___y_614_ = v___y_505_;
v___y_615_ = v___y_506_;
v___y_616_ = v___y_507_;
goto v___jp_612_;
}
v___jp_509_:
{
lean_object* v___x_525_; 
lean_inc(v___y_524_);
lean_inc_ref(v___y_523_);
lean_inc(v___y_522_);
lean_inc_ref(v___y_521_);
v___x_525_ = lean_infer_type(v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v___x_527_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_493_);
v___x_528_ = lean_unsigned_to_nat(0u);
v___x_529_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_519_, v_a_526_, v___x_527_, v___y_513_, v___y_512_, v___x_528_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec_ref(v___x_527_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_542_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_542_ == 0)
{
v___x_532_ = v___x_529_;
v_isShared_533_ = v_isSharedCheck_542_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_529_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_542_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_540_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_mk_empty_array_with_capacity(v___x_534_);
v___x_536_ = lean_array_push(v___x_535_, v_e_494_);
v___x_537_ = l_Array_append___redArg(v___x_536_, v___y_516_);
v___x_538_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_538_, 0, v___y_514_);
lean_ctor_set(v___x_538_, 1, v___y_510_);
lean_ctor_set(v___x_538_, 2, v___y_511_);
lean_ctor_set(v___x_538_, 3, v___y_515_);
lean_ctor_set(v___x_538_, 4, v___y_517_);
lean_ctor_set(v___x_538_, 5, v___y_518_);
lean_ctor_set(v___x_538_, 6, v_a_530_);
lean_ctor_set(v___x_538_, 7, v___x_537_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v___x_538_);
v___x_540_ = v___x_532_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v___x_538_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v_e_494_);
v_a_543_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_529_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_529_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_510_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v_a_551_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_525_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_525_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
v___jp_559_:
{
uint8_t v___x_573_; uint8_t v___x_574_; uint8_t v___x_575_; lean_object* v___x_576_; 
v___x_573_ = 0;
v___x_574_ = 1;
v___x_575_ = 1;
v___x_576_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_502_, v___y_565_, v___x_573_, v___x_574_, v___x_573_, v___x_574_, v___x_575_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc_n(v_a_577_, 2);
lean_dec_ref_known(v___x_576_, 1);
lean_inc_ref(v_matcherLevels_568_);
v___x_578_ = lean_array_to_list(v_matcherLevels_568_);
lean_inc(v___y_560_);
v___x_579_ = l_Lean_mkConst(v___y_560_, v___x_578_);
v___x_580_ = l_Lean_mkAppN(v___x_579_, v___y_564_);
v___x_581_ = l_Lean_Expr_app___override(v___x_580_, v_a_577_);
v___x_582_ = l_Lean_mkAppN(v___x_581_, v___y_567_);
lean_inc_ref(v___x_582_);
v___x_583_ = l_Lean_Meta_isTypeCorrect(v___x_582_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; uint8_t v___x_585_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref_known(v___x_583_, 1);
v___x_585_ = lean_unbox(v_a_584_);
lean_dec(v_a_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v___x_582_);
lean_dec(v_a_577_);
lean_dec_ref(v_matcherLevels_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v___x_586_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_587_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_586_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_587_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_587_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
else
{
v___y_510_ = v___y_560_;
v___y_511_ = v_matcherLevels_568_;
v___y_512_ = v___x_573_;
v___y_513_ = v___y_561_;
v___y_514_ = v___y_562_;
v___y_515_ = v___y_564_;
v___y_516_ = v___y_563_;
v___y_517_ = v_a_577_;
v___y_518_ = v___y_567_;
v___y_519_ = v___y_566_;
v___y_520_ = v___x_582_;
v___y_521_ = v___y_569_;
v___y_522_ = v___y_570_;
v___y_523_ = v___y_571_;
v___y_524_ = v___y_572_;
goto v___jp_509_;
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v___x_582_);
lean_dec(v_a_577_);
lean_dec_ref(v_matcherLevels_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v_a_596_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_583_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_583_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec_ref(v_matcherLevels_568_);
lean_dec_ref(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec_ref(v___y_564_);
lean_dec_ref(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v_a_604_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_576_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_576_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
v___jp_612_:
{
lean_object* v___x_617_; 
lean_inc(v___y_616_);
lean_inc_ref(v___y_615_);
lean_inc(v___y_614_);
lean_inc_ref(v___y_613_);
lean_inc_ref(v_e_494_);
v___x_617_ = lean_infer_type(v_e_494_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc_n(v_a_618_, 2);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = lean_array_get_size(v_discrs_495_);
v___x_620_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_495_, v_motiveArgs_502_, v___x_619_, v_a_618_);
v___x_621_ = l_Lean_mkArrow(v___x_620_, v_motiveBody_503_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_uElimPos_x3f_622_; 
v_uElimPos_x3f_622_ = lean_ctor_get(v_toMatcherInfo_496_, 3);
if (lean_obj_tag(v_uElimPos_x3f_622_) == 0)
{
lean_object* v_a_623_; 
v_a_623_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_621_, 1);
v___y_560_ = v_matcherName_497_;
v___y_561_ = v_alts_498_;
v___y_562_ = v_toMatcherInfo_496_;
v___y_563_ = v_remaining_499_;
v___y_564_ = v_params_500_;
v___y_565_ = v_a_623_;
v___y_566_ = v_a_618_;
v___y_567_ = v_discrs_495_;
v_matcherLevels_568_ = v_matcherLevels_501_;
v___y_569_ = v___y_613_;
v___y_570_ = v___y_614_;
v___y_571_ = v___y_615_;
v___y_572_ = v___y_616_;
goto v___jp_559_;
}
else
{
lean_object* v_a_624_; lean_object* v_val_625_; lean_object* v___x_626_; 
v_a_624_ = lean_ctor_get(v___x_621_, 0);
lean_inc_n(v_a_624_, 2);
lean_dec_ref_known(v___x_621_, 1);
v_val_625_ = lean_ctor_get(v_uElimPos_x3f_622_, 0);
v___x_626_ = l_Lean_Meta_getLevel(v_a_624_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_628_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_a_627_);
lean_dec_ref_known(v___x_626_, 1);
v___x_628_ = lean_array_set(v_matcherLevels_501_, v_val_625_, v_a_627_);
v___y_560_ = v_matcherName_497_;
v___y_561_ = v_alts_498_;
v___y_562_ = v_toMatcherInfo_496_;
v___y_563_ = v_remaining_499_;
v___y_564_ = v_params_500_;
v___y_565_ = v_a_624_;
v___y_566_ = v_a_618_;
v___y_567_ = v_discrs_495_;
v_matcherLevels_568_ = v___x_628_;
v___y_569_ = v___y_613_;
v___y_570_ = v___y_614_;
v___y_571_ = v___y_615_;
v___y_572_ = v___y_616_;
goto v___jp_559_;
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v_a_624_);
lean_dec(v_a_618_);
lean_dec_ref(v_matcherLevels_501_);
lean_dec_ref(v_params_500_);
lean_dec_ref(v_alts_498_);
lean_dec(v_matcherName_497_);
lean_dec_ref(v_toMatcherInfo_496_);
lean_dec_ref(v_discrs_495_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v_a_629_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_626_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_626_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec(v_a_618_);
lean_dec_ref(v_matcherLevels_501_);
lean_dec_ref(v_params_500_);
lean_dec_ref(v_alts_498_);
lean_dec(v_matcherName_497_);
lean_dec_ref(v_toMatcherInfo_496_);
lean_dec_ref(v_discrs_495_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v_a_637_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_621_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_621_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_a_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
lean_dec_ref(v_motiveBody_503_);
lean_dec_ref(v_matcherLevels_501_);
lean_dec_ref(v_params_500_);
lean_dec_ref(v_alts_498_);
lean_dec(v_matcherName_497_);
lean_dec_ref(v_toMatcherInfo_496_);
lean_dec_ref(v_discrs_495_);
lean_dec_ref(v_e_494_);
lean_dec_ref(v_matcherApp_493_);
v_a_645_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_652_ == 0)
{
v___x_647_ = v___x_617_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_a_645_);
lean_dec(v___x_617_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_645_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_672_, lean_object* v_e_673_, lean_object* v_discrs_674_, lean_object* v_toMatcherInfo_675_, lean_object* v_matcherName_676_, lean_object* v_alts_677_, lean_object* v_remaining_678_, lean_object* v_params_679_, lean_object* v_matcherLevels_680_, lean_object* v_motiveArgs_681_, lean_object* v_motiveBody_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_672_, v_e_673_, v_discrs_674_, v_toMatcherInfo_675_, v_matcherName_676_, v_alts_677_, v_remaining_678_, v_params_679_, v_matcherLevels_680_, v_motiveArgs_681_, v_motiveBody_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v_motiveArgs_681_);
lean_dec_ref(v_remaining_678_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* v_matcherApp_689_, lean_object* v_e_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_toMatcherInfo_696_; lean_object* v_matcherName_697_; lean_object* v_matcherLevels_698_; lean_object* v_params_699_; lean_object* v_motive_700_; lean_object* v_discrs_701_; lean_object* v_alts_702_; lean_object* v_remaining_703_; lean_object* v___f_704_; uint8_t v___x_705_; lean_object* v___x_706_; 
v_toMatcherInfo_696_ = lean_ctor_get(v_matcherApp_689_, 0);
lean_inc_ref(v_toMatcherInfo_696_);
v_matcherName_697_ = lean_ctor_get(v_matcherApp_689_, 1);
lean_inc(v_matcherName_697_);
v_matcherLevels_698_ = lean_ctor_get(v_matcherApp_689_, 2);
lean_inc_ref(v_matcherLevels_698_);
v_params_699_ = lean_ctor_get(v_matcherApp_689_, 3);
lean_inc_ref(v_params_699_);
v_motive_700_ = lean_ctor_get(v_matcherApp_689_, 4);
lean_inc_ref(v_motive_700_);
v_discrs_701_ = lean_ctor_get(v_matcherApp_689_, 5);
lean_inc_ref(v_discrs_701_);
v_alts_702_ = lean_ctor_get(v_matcherApp_689_, 6);
lean_inc_ref(v_alts_702_);
v_remaining_703_ = lean_ctor_get(v_matcherApp_689_, 7);
lean_inc_ref(v_remaining_703_);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_704_, 0, v_matcherApp_689_);
lean_closure_set(v___f_704_, 1, v_e_690_);
lean_closure_set(v___f_704_, 2, v_discrs_701_);
lean_closure_set(v___f_704_, 3, v_toMatcherInfo_696_);
lean_closure_set(v___f_704_, 4, v_matcherName_697_);
lean_closure_set(v___f_704_, 5, v_alts_702_);
lean_closure_set(v___f_704_, 6, v_remaining_703_);
lean_closure_set(v___f_704_, 7, v_params_699_);
lean_closure_set(v___f_704_, 8, v_matcherLevels_698_);
v___x_705_ = 0;
v___x_706_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_700_, v___f_704_, v___x_705_, v_a_691_, v_a_692_, v_a_693_, v_a_694_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* v_matcherApp_707_, lean_object* v_e_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_707_, v_e_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* v_matcherApp_715_, lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_715_, v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_731_; 
v_a_723_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_731_ == 0)
{
v___x_725_ = v___x_722_;
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_727_, 0, v_a_723_);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_747_; 
v_a_732_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_747_ == 0)
{
v___x_734_ = v___x_722_;
v_isShared_735_ = v_isSharedCheck_747_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_722_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_747_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
uint8_t v___y_737_; uint8_t v___x_745_; 
v___x_745_ = l_Lean_Exception_isInterrupt(v_a_732_);
if (v___x_745_ == 0)
{
uint8_t v___x_746_; 
lean_inc(v_a_732_);
v___x_746_ = l_Lean_Exception_isRuntime(v_a_732_);
v___y_737_ = v___x_746_;
goto v___jp_736_;
}
else
{
v___y_737_ = v___x_745_;
goto v___jp_736_;
}
v___jp_736_:
{
if (v___y_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_740_; 
lean_dec(v_a_732_);
v___x_738_ = lean_box(0);
if (v_isShared_735_ == 0)
{
lean_ctor_set_tag(v___x_734_, 0);
lean_ctor_set(v___x_734_, 0, v___x_738_);
v___x_740_ = v___x_734_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_738_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
else
{
lean_object* v___x_743_; 
if (v_isShared_735_ == 0)
{
v___x_743_ = v___x_734_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_732_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* v_matcherApp_748_, lean_object* v_e_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_748_, v_e_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(lean_object* v_type_756_, lean_object* v_maxFVars_x3f_757_, lean_object* v_k_758_, uint8_t v_cleanupAnnotations_759_, uint8_t v_whnfType_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v___f_766_; lean_object* v___x_767_; 
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_766_, 0, v_k_758_);
v___x_767_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_756_, v_maxFVars_x3f_757_, v___f_766_, v_cleanupAnnotations_759_, v_whnfType_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
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
v_reuseFailAlloc_774_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
v_a_776_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_767_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_767_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg___boxed(lean_object* v_type_784_, lean_object* v_maxFVars_x3f_785_, lean_object* v_k_786_, lean_object* v_cleanupAnnotations_787_, lean_object* v_whnfType_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_794_; uint8_t v_whnfType_boxed_795_; lean_object* v_res_796_; 
v_cleanupAnnotations_boxed_794_ = lean_unbox(v_cleanupAnnotations_787_);
v_whnfType_boxed_795_ = lean_unbox(v_whnfType_788_);
v_res_796_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_784_, v_maxFVars_x3f_785_, v_k_786_, v_cleanupAnnotations_boxed_794_, v_whnfType_boxed_795_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(lean_object* v_00_u03b1_797_, lean_object* v_type_798_, lean_object* v_maxFVars_x3f_799_, lean_object* v_k_800_, uint8_t v_cleanupAnnotations_801_, uint8_t v_whnfType_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_type_798_, v_maxFVars_x3f_799_, v_k_800_, v_cleanupAnnotations_801_, v_whnfType_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* v_00_u03b1_809_, lean_object* v_type_810_, lean_object* v_maxFVars_x3f_811_, lean_object* v_k_812_, lean_object* v_cleanupAnnotations_813_, lean_object* v_whnfType_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_820_; uint8_t v_whnfType_boxed_821_; lean_object* v_res_822_; 
v_cleanupAnnotations_boxed_820_ = lean_unbox(v_cleanupAnnotations_813_);
v_whnfType_boxed_821_ = lean_unbox(v_whnfType_814_);
v_res_822_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_00_u03b1_809_, v_type_810_, v_maxFVars_x3f_811_, v_k_812_, v_cleanupAnnotations_boxed_820_, v_whnfType_boxed_821_, v___y_815_, v___y_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(lean_object* v_type_823_, lean_object* v_k_824_, uint8_t v_cleanupAnnotations_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___f_831_; uint8_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___f_831_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_831_, 0, v_k_824_);
v___x_832_ = 0;
v___x_833_ = lean_box(0);
v___x_834_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_832_, v___x_833_, v_type_823_, v___f_831_, v_cleanupAnnotations_825_, v___x_832_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
v_a_843_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_834_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_834_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg___boxed(lean_object* v_type_851_, lean_object* v_k_852_, lean_object* v_cleanupAnnotations_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_859_; lean_object* v_res_860_; 
v_cleanupAnnotations_boxed_859_ = lean_unbox(v_cleanupAnnotations_853_);
v_res_860_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_851_, v_k_852_, v_cleanupAnnotations_boxed_859_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(lean_object* v_00_u03b1_861_, lean_object* v_type_862_, lean_object* v_k_863_, uint8_t v_cleanupAnnotations_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_){
_start:
{
lean_object* v___x_870_; 
v___x_870_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_type_862_, v_k_863_, v_cleanupAnnotations_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___boxed(lean_object* v_00_u03b1_871_, lean_object* v_type_872_, lean_object* v_k_873_, lean_object* v_cleanupAnnotations_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_880_; lean_object* v_res_881_; 
v_cleanupAnnotations_boxed_880_ = lean_unbox(v_cleanupAnnotations_874_);
v_res_881_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4(v_00_u03b1_871_, v_type_872_, v_k_873_, v_cleanupAnnotations_boxed_880_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(size_t v_sz_882_, size_t v_i_883_, lean_object* v_bs_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
uint8_t v___x_890_; 
v___x_890_ = lean_usize_dec_lt(v_i_883_, v_sz_882_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
v___x_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_891_, 0, v_bs_884_);
return v___x_891_;
}
else
{
lean_object* v_v_892_; lean_object* v___x_893_; lean_object* v_bs_x27_894_; lean_object* v___x_895_; 
v_v_892_ = lean_array_uget(v_bs_884_, v_i_883_);
v___x_893_ = lean_unsigned_to_nat(0u);
v_bs_x27_894_ = lean_array_uset(v_bs_884_, v_i_883_, v___x_893_);
lean_inc(v___y_888_);
lean_inc_ref(v___y_887_);
lean_inc(v___y_886_);
lean_inc_ref(v___y_885_);
v___x_895_ = lean_infer_type(v_v_892_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; size_t v___x_897_; size_t v___x_898_; lean_object* v___x_899_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = ((size_t)1ULL);
v___x_898_ = lean_usize_add(v_i_883_, v___x_897_);
v___x_899_ = lean_array_uset(v_bs_x27_894_, v_i_883_, v_a_896_);
v_i_883_ = v___x_898_;
v_bs_884_ = v___x_899_;
goto _start;
}
else
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec_ref(v_bs_x27_894_);
v_a_901_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_895_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_895_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_a_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* v_sz_909_, lean_object* v_i_910_, lean_object* v_bs_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_909_);
lean_dec(v_sz_909_);
v_i_boxed_918_ = lean_unbox_usize(v_i_910_);
lean_dec(v_i_910_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_boxed_917_, v_i_boxed_918_, v_bs_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
return v_res_919_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__0));
v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(uint8_t v___x_923_, uint8_t v___x_924_, uint8_t v___x_925_, lean_object* v_a_926_, lean_object* v_fvs_927_, lean_object* v_body_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = lean_array_get_size(v_fvs_927_);
v___x_943_ = lean_nat_dec_eq(v___x_942_, v_a_926_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
v___x_944_ = lean_obj_once(&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1, &l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___closed__1);
v___x_945_ = l_Nat_reprFast(v_a_926_);
v___x_946_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
v___x_947_ = l_Lean_MessageData_ofFormat(v___x_946_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_944_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_950_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
else
{
lean_dec(v_a_926_);
goto v___jp_934_;
}
v___jp_934_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_935_ = lean_unsigned_to_nat(2u);
v___x_936_ = l_Lean_Expr_getAppNumArgs(v_body_928_);
v___x_937_ = lean_nat_sub(v___x_936_, v___x_935_);
lean_dec(v___x_936_);
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_sub(v___x_937_, v___x_938_);
lean_dec(v___x_937_);
v___x_940_ = l_Lean_Expr_getRevArg_x21(v_body_928_, v___x_939_);
v___x_941_ = l_Lean_Meta_mkLambdaFVars(v_fvs_927_, v___x_940_, v___x_923_, v___x_924_, v___x_923_, v___x_924_, v___x_925_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
return v___x_941_;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed(lean_object* v___x_960_, lean_object* v___x_961_, lean_object* v___x_962_, lean_object* v_a_963_, lean_object* v_fvs_964_, lean_object* v_body_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_4175__boxed_971_; uint8_t v___x_4176__boxed_972_; uint8_t v___x_4177__boxed_973_; lean_object* v_res_974_; 
v___x_4175__boxed_971_ = lean_unbox(v___x_960_);
v___x_4176__boxed_972_ = lean_unbox(v___x_961_);
v___x_4177__boxed_973_ = lean_unbox(v___x_962_);
v_res_974_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0(v___x_4175__boxed_971_, v___x_4176__boxed_972_, v___x_4177__boxed_973_, v_a_963_, v_fvs_964_, v_body_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_body_965_);
lean_dec_ref(v_fvs_964_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* v_as_975_, lean_object* v_bs_976_, lean_object* v_i_977_, lean_object* v_cs_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = lean_array_get_size(v_as_975_);
v___x_985_ = lean_nat_dec_lt(v_i_977_, v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; 
lean_dec(v_i_977_);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v_cs_978_);
return v___x_986_;
}
else
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = lean_array_get_size(v_bs_976_);
v___x_988_ = lean_nat_dec_lt(v_i_977_, v___x_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; 
lean_dec(v_i_977_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v_cs_978_);
return v___x_989_;
}
else
{
uint8_t v___x_990_; uint8_t v___x_991_; lean_object* v_a_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___f_996_; lean_object* v_b_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_990_ = 0;
v___x_991_ = 1;
v_a_992_ = lean_array_fget_borrowed(v_as_975_, v_i_977_);
v___x_993_ = lean_box(v___x_990_);
v___x_994_ = lean_box(v___x_988_);
v___x_995_ = lean_box(v___x_991_);
lean_inc_n(v_a_992_, 2);
v___f_996_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___lam__0___boxed), 11, 4);
lean_closure_set(v___f_996_, 0, v___x_993_);
lean_closure_set(v___f_996_, 1, v___x_994_);
lean_closure_set(v___f_996_, 2, v___x_995_);
lean_closure_set(v___f_996_, 3, v_a_992_);
v_b_997_ = lean_array_fget_borrowed(v_bs_976_, v_i_977_);
v___x_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_998_, 0, v_a_992_);
lean_inc(v_b_997_);
v___x_999_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_b_997_, v___x_998_, v___f_996_, v___x_990_, v___x_990_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
lean_inc(v_a_1000_);
lean_dec_ref_known(v___x_999_, 1);
v___x_1001_ = lean_unsigned_to_nat(1u);
v___x_1002_ = lean_nat_add(v_i_977_, v___x_1001_);
lean_dec(v_i_977_);
v___x_1003_ = lean_array_push(v_cs_978_, v_a_1000_);
v_i_977_ = v___x_1002_;
v_cs_978_ = v___x_1003_;
goto _start;
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_dec_ref(v_cs_978_);
lean_dec(v_i_977_);
v_a_1005_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_999_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* v_as_1013_, lean_object* v_bs_1014_, lean_object* v_i_1015_, lean_object* v_cs_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_as_1013_, v_bs_1014_, v_i_1015_, v_cs_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec_ref(v___y_1017_);
lean_dec_ref(v_bs_1014_);
lean_dec_ref(v_as_1013_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* v_matcherApp_1025_, lean_object* v_altAuxs_1026_, lean_object* v_x_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
size_t v_sz_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
v_sz_1033_ = lean_array_size(v_altAuxs_1026_);
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_sz_1033_, v___x_1034_, v_altAuxs_1026_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref_known(v___x_1035_, 1);
v___x_1037_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_1025_);
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_1040_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v___x_1037_, v_a_1036_, v___x_1038_, v___x_1039_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v_a_1036_);
lean_dec_ref(v___x_1037_);
return v___x_1040_;
}
else
{
lean_dec_ref(v_matcherApp_1025_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* v_matcherApp_1041_, lean_object* v_altAuxs_1042_, lean_object* v_x_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1041_, v_altAuxs_1042_, v_x_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec_ref(v_x_1043_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* v_motiveArgs_1050_, lean_object* v___x_1051_, lean_object* v_i_1052_, lean_object* v_a_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_zero_1059_; uint8_t v_isZero_1060_; 
v_zero_1059_ = lean_unsigned_to_nat(0u);
v_isZero_1060_ = lean_nat_dec_eq(v_i_1052_, v_zero_1059_);
if (v_isZero_1060_ == 1)
{
lean_object* v___x_1061_; 
lean_dec(v_i_1052_);
v___x_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1061_, 0, v_a_1053_);
return v___x_1061_;
}
else
{
lean_object* v___x_1062_; lean_object* v_one_1063_; lean_object* v_n_1064_; lean_object* v_motiveArg_1065_; lean_object* v_discr_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1062_ = l_Lean_instInhabitedExpr;
v_one_1063_ = lean_unsigned_to_nat(1u);
v_n_1064_ = lean_nat_sub(v_i_1052_, v_one_1063_);
lean_dec(v_i_1052_);
v_motiveArg_1065_ = lean_array_get_borrowed(v___x_1062_, v_motiveArgs_1050_, v_n_1064_);
v_discr_1066_ = lean_array_fget_borrowed(v___x_1051_, v_n_1064_);
v___x_1067_ = lean_box(0);
lean_inc(v_discr_1066_);
v___x_1068_ = l_Lean_Meta_kabstract(v_a_1053_, v_discr_1066_, v___x_1067_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = lean_expr_instantiate1(v_a_1069_, v_motiveArg_1065_);
lean_dec(v_a_1069_);
v_i_1052_ = v_n_1064_;
v_a_1053_ = v___x_1070_;
goto _start;
}
else
{
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1072_; 
v_a_1072_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1068_, 1);
v_i_1052_ = v_n_1064_;
v_a_1053_ = v_a_1072_;
goto _start;
}
else
{
lean_dec(v_n_1064_);
return v___x_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* v_motiveArgs_1074_, lean_object* v___x_1075_, lean_object* v_i_1076_, lean_object* v_a_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1074_, v___x_1075_, v_i_1076_, v_a_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec_ref(v___x_1075_);
lean_dec_ref(v_motiveArgs_1074_);
return v_res_1083_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
v___x_1089_ = l_Lean_stringToMessageData(v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1090_, lean_object* v_discrs_1091_, lean_object* v_e_1092_, lean_object* v_toMatcherInfo_1093_, lean_object* v_params_1094_, lean_object* v_matcherName_1095_, lean_object* v_matcherLevels_1096_, lean_object* v_motiveArgs_1097_, lean_object* v___motiveBody_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v___y_1105_; lean_object* v___y_1106_; lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v_matcherLevels_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1203_ = lean_array_get_size(v_motiveArgs_1097_);
v___x_1204_ = lean_array_get_size(v_discrs_1091_);
v___x_1205_ = lean_nat_dec_eq(v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v_matcherLevels_1096_);
lean_dec(v_matcherName_1095_);
lean_dec_ref(v_e_1092_);
lean_dec_ref(v___f_1090_);
v___x_1206_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
v___x_1207_ = l_Nat_reprFast(v___x_1204_);
v___x_1208_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
v___x_1209_ = l_Lean_MessageData_ofFormat(v___x_1208_);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1206_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1212_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
v___y_1173_ = v___y_1099_;
v___y_1174_ = v___y_1100_;
v___y_1175_ = v___y_1101_;
v___y_1176_ = v___y_1102_;
goto v___jp_1172_;
}
v___jp_1104_:
{
lean_object* v___x_1112_; 
lean_inc(v___y_1111_);
lean_inc_ref(v___y_1110_);
lean_inc(v___y_1109_);
lean_inc_ref(v___y_1108_);
v___x_1112_ = lean_infer_type(v___y_1106_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__4___redArg(v_a_1113_, v___y_1107_, v___y_1105_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
return v___x_1114_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
lean_dec_ref(v___y_1107_);
v_a_1115_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1117_ = v___x_1112_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1112_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
v___jp_1123_:
{
uint8_t v___x_1133_; uint8_t v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; 
v___x_1133_ = 0;
v___x_1134_ = 1;
v___x_1135_ = 1;
v___x_1136_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1097_, v___y_1125_, v___x_1133_, v___x_1134_, v___x_1133_, v___x_1134_, v___x_1135_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
v___x_1138_ = lean_array_to_list(v_matcherLevels_1128_);
v___x_1139_ = l_Lean_mkConst(v___y_1127_, v___x_1138_);
v___x_1140_ = l_Lean_mkAppN(v___x_1139_, v___y_1126_);
v___x_1141_ = l_Lean_Expr_app___override(v___x_1140_, v_a_1137_);
v___x_1142_ = l_Lean_mkAppN(v___x_1141_, v___y_1124_);
lean_inc_ref(v___x_1142_);
v___x_1143_ = l_Lean_Meta_isTypeCorrect(v___x_1142_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; uint8_t v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = lean_unbox(v_a_1144_);
lean_dec(v_a_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1155_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v___f_1090_);
v___x_1146_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
v___x_1147_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1146_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1150_ = v___x_1147_;
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1147_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1155_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1153_; 
if (v_isShared_1151_ == 0)
{
v___x_1153_ = v___x_1150_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
v___y_1105_ = v___x_1133_;
v___y_1106_ = v___x_1142_;
v___y_1107_ = v___f_1090_;
v___y_1108_ = v___y_1129_;
v___y_1109_ = v___y_1130_;
v___y_1110_ = v___y_1131_;
v___y_1111_ = v___y_1132_;
goto v___jp_1104_;
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v___x_1142_);
lean_dec_ref(v___f_1090_);
v_a_1156_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1143_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1143_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec_ref(v_matcherLevels_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___f_1090_);
v_a_1164_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1136_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1136_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
v___jp_1172_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_array_get_size(v_discrs_1091_);
v___x_1178_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1097_, v_discrs_1091_, v___x_1177_, v_e_1092_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v___x_1180_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc_n(v_a_1179_, 2);
lean_dec_ref_known(v___x_1178_, 1);
v___x_1180_ = l_Lean_Meta_mkEq(v_a_1179_, v_a_1179_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_uElimPos_x3f_1181_; 
v_uElimPos_x3f_1181_ = lean_ctor_get(v_toMatcherInfo_1093_, 3);
if (lean_obj_tag(v_uElimPos_x3f_1181_) == 0)
{
lean_object* v_a_1182_; 
v_a_1182_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1180_, 1);
v___y_1124_ = v_discrs_1091_;
v___y_1125_ = v_a_1182_;
v___y_1126_ = v_params_1094_;
v___y_1127_ = v_matcherName_1095_;
v_matcherLevels_1128_ = v_matcherLevels_1096_;
v___y_1129_ = v___y_1173_;
v___y_1130_ = v___y_1174_;
v___y_1131_ = v___y_1175_;
v___y_1132_ = v___y_1176_;
goto v___jp_1123_;
}
else
{
lean_object* v_a_1183_; lean_object* v_val_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v_a_1183_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1180_, 1);
v_val_1184_ = lean_ctor_get(v_uElimPos_x3f_1181_, 0);
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_array_set(v_matcherLevels_1096_, v_val_1184_, v___x_1185_);
v___y_1124_ = v_discrs_1091_;
v___y_1125_ = v_a_1183_;
v___y_1126_ = v_params_1094_;
v___y_1127_ = v_matcherName_1095_;
v_matcherLevels_1128_ = v___x_1186_;
v___y_1129_ = v___y_1173_;
v___y_1130_ = v___y_1174_;
v___y_1131_ = v___y_1175_;
v___y_1132_ = v___y_1176_;
goto v___jp_1123_;
}
}
else
{
lean_object* v_a_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1194_; 
lean_dec_ref(v_matcherLevels_1096_);
lean_dec(v_matcherName_1095_);
lean_dec_ref(v___f_1090_);
v_a_1187_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1194_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1189_ = v___x_1180_;
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_a_1187_);
lean_dec(v___x_1180_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1194_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1192_; 
if (v_isShared_1190_ == 0)
{
v___x_1192_ = v___x_1189_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_a_1187_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
else
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1202_; 
lean_dec_ref(v_matcherLevels_1096_);
lean_dec(v_matcherName_1095_);
lean_dec_ref(v___f_1090_);
v_a_1195_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1197_ = v___x_1178_;
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1178_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1202_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1200_; 
if (v_isShared_1198_ == 0)
{
v___x_1200_ = v___x_1197_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1201_; 
v_reuseFailAlloc_1201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1201_, 0, v_a_1195_);
v___x_1200_ = v_reuseFailAlloc_1201_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
return v___x_1200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1222_, lean_object* v_discrs_1223_, lean_object* v_e_1224_, lean_object* v_toMatcherInfo_1225_, lean_object* v_params_1226_, lean_object* v_matcherName_1227_, lean_object* v_matcherLevels_1228_, lean_object* v_motiveArgs_1229_, lean_object* v___motiveBody_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1222_, v_discrs_1223_, v_e_1224_, v_toMatcherInfo_1225_, v_params_1226_, v_matcherName_1227_, v_matcherLevels_1228_, v_motiveArgs_1229_, v___motiveBody_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec_ref(v___motiveBody_1230_);
lean_dec_ref(v_motiveArgs_1229_);
lean_dec_ref(v_params_1226_);
lean_dec_ref(v_toMatcherInfo_1225_);
lean_dec_ref(v_discrs_1223_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* v_matcherApp_1237_, lean_object* v_e_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_){
_start:
{
lean_object* v_toMatcherInfo_1244_; lean_object* v_matcherName_1245_; lean_object* v_matcherLevels_1246_; lean_object* v_params_1247_; lean_object* v_motive_1248_; lean_object* v_discrs_1249_; lean_object* v___f_1250_; lean_object* v___f_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
v_toMatcherInfo_1244_ = lean_ctor_get(v_matcherApp_1237_, 0);
lean_inc_ref(v_toMatcherInfo_1244_);
v_matcherName_1245_ = lean_ctor_get(v_matcherApp_1237_, 1);
lean_inc(v_matcherName_1245_);
v_matcherLevels_1246_ = lean_ctor_get(v_matcherApp_1237_, 2);
lean_inc_ref(v_matcherLevels_1246_);
v_params_1247_ = lean_ctor_get(v_matcherApp_1237_, 3);
lean_inc_ref(v_params_1247_);
v_motive_1248_ = lean_ctor_get(v_matcherApp_1237_, 4);
lean_inc_ref(v_motive_1248_);
v_discrs_1249_ = lean_ctor_get(v_matcherApp_1237_, 5);
lean_inc_ref(v_discrs_1249_);
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1250_, 0, v_matcherApp_1237_);
v___f_1251_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1251_, 0, v___f_1250_);
lean_closure_set(v___f_1251_, 1, v_discrs_1249_);
lean_closure_set(v___f_1251_, 2, v_e_1238_);
lean_closure_set(v___f_1251_, 3, v_toMatcherInfo_1244_);
lean_closure_set(v___f_1251_, 4, v_params_1247_);
lean_closure_set(v___f_1251_, 5, v_matcherName_1245_);
lean_closure_set(v___f_1251_, 6, v_matcherLevels_1246_);
v___x_1252_ = 0;
v___x_1253_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_1248_, v___f_1251_, v___x_1252_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* v_matcherApp_1254_, lean_object* v_e_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1254_, v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* v_motiveArgs_1262_, lean_object* v___x_1263_, lean_object* v_n_1264_, lean_object* v_i_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v___x_1273_; 
v___x_1273_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_motiveArgs_1262_, v___x_1263_, v_i_1265_, v_a_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* v_motiveArgs_1274_, lean_object* v___x_1275_, lean_object* v_n_1276_, lean_object* v_i_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v_motiveArgs_1274_, v___x_1275_, v_n_1276_, v_i_1277_, v_a_1278_, v_a_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v_n_1276_);
lean_dec_ref(v___x_1275_);
lean_dec_ref(v_motiveArgs_1274_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* v_matcherApp_1286_, lean_object* v_e_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1286_, v_e_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1302_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_a_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1318_; 
v_a_1303_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1305_ = v___x_1293_;
v_isShared_1306_ = v_isSharedCheck_1318_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1293_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1318_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
uint8_t v___y_1308_; uint8_t v___x_1316_; 
v___x_1316_ = l_Lean_Exception_isInterrupt(v_a_1303_);
if (v___x_1316_ == 0)
{
uint8_t v___x_1317_; 
lean_inc(v_a_1303_);
v___x_1317_ = l_Lean_Exception_isRuntime(v_a_1303_);
v___y_1308_ = v___x_1317_;
goto v___jp_1307_;
}
else
{
v___y_1308_ = v___x_1316_;
goto v___jp_1307_;
}
v___jp_1307_:
{
if (v___y_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_dec(v_a_1303_);
v___x_1309_ = lean_box(0);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1309_);
v___x_1311_ = v___x_1305_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
lean_object* v___x_1314_; 
if (v_isShared_1306_ == 0)
{
v___x_1314_ = v___x_1305_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1303_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* v_matcherApp_1319_, lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1319_, v_e_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1327_, lean_object* v_x_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v_keyedConfig_1334_; uint8_t v_trackZetaDelta_1335_; lean_object* v_zetaDeltaSet_1336_; lean_object* v_localInstances_1337_; lean_object* v_defEqCtx_x3f_1338_; lean_object* v_synthPendingDepth_1339_; lean_object* v_customCanUnfoldPredicate_x3f_1340_; uint8_t v_univApprox_1341_; uint8_t v_inTypeClassResolution_1342_; uint8_t v_cacheInferType_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_keyedConfig_1334_ = lean_ctor_get(v___y_1329_, 0);
v_trackZetaDelta_1335_ = lean_ctor_get_uint8(v___y_1329_, sizeof(void*)*7);
v_zetaDeltaSet_1336_ = lean_ctor_get(v___y_1329_, 1);
v_localInstances_1337_ = lean_ctor_get(v___y_1329_, 3);
v_defEqCtx_x3f_1338_ = lean_ctor_get(v___y_1329_, 4);
v_synthPendingDepth_1339_ = lean_ctor_get(v___y_1329_, 5);
v_customCanUnfoldPredicate_x3f_1340_ = lean_ctor_get(v___y_1329_, 6);
v_univApprox_1341_ = lean_ctor_get_uint8(v___y_1329_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1342_ = lean_ctor_get_uint8(v___y_1329_, sizeof(void*)*7 + 2);
v_cacheInferType_1343_ = lean_ctor_get_uint8(v___y_1329_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_1340_);
lean_inc(v_synthPendingDepth_1339_);
lean_inc(v_defEqCtx_x3f_1338_);
lean_inc_ref(v_localInstances_1337_);
lean_inc(v_zetaDeltaSet_1336_);
lean_inc_ref(v_keyedConfig_1334_);
v___x_1344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1344_, 0, v_keyedConfig_1334_);
lean_ctor_set(v___x_1344_, 1, v_zetaDeltaSet_1336_);
lean_ctor_set(v___x_1344_, 2, v_lctx_1327_);
lean_ctor_set(v___x_1344_, 3, v_localInstances_1337_);
lean_ctor_set(v___x_1344_, 4, v_defEqCtx_x3f_1338_);
lean_ctor_set(v___x_1344_, 5, v_synthPendingDepth_1339_);
lean_ctor_set(v___x_1344_, 6, v_customCanUnfoldPredicate_x3f_1340_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7, v_trackZetaDelta_1335_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7 + 1, v_univApprox_1341_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1342_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*7 + 3, v_cacheInferType_1343_);
lean_inc(v___y_1332_);
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1330_);
v___x_1345_ = lean_apply_5(v_x_1328_, v___x_1344_, v___y_1330_, v___y_1331_, v___y_1332_, lean_box(0));
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1346_, lean_object* v_x_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1346_, v_x_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1354_, lean_object* v_lctx_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; 
v___x_1362_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1355_, v_x_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1363_, lean_object* v_lctx_1364_, lean_object* v_x_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1363_, v_lctx_1364_, v_x_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1372_, size_t v_i_1373_, size_t v_stop_1374_, lean_object* v_b_1375_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_eq(v_i_1373_, v_stop_1374_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; size_t v___x_1382_; size_t v___x_1383_; 
v___x_1377_ = lean_array_uget_borrowed(v_as_1372_, v_i_1373_);
v_fst_1378_ = lean_ctor_get(v___x_1377_, 0);
v_snd_1379_ = lean_ctor_get(v___x_1377_, 1);
v___x_1380_ = l_Lean_Expr_fvarId_x21(v_fst_1378_);
lean_inc(v_snd_1379_);
v___x_1381_ = l_Lean_LocalContext_setUserName(v_b_1375_, v___x_1380_, v_snd_1379_);
v___x_1382_ = ((size_t)1ULL);
v___x_1383_ = lean_usize_add(v_i_1373_, v___x_1382_);
v_i_1373_ = v___x_1383_;
v_b_1375_ = v___x_1381_;
goto _start;
}
else
{
return v_b_1375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1385_, lean_object* v_i_1386_, lean_object* v_stop_1387_, lean_object* v_b_1388_){
_start:
{
size_t v_i_boxed_1389_; size_t v_stop_boxed_1390_; lean_object* v_res_1391_; 
v_i_boxed_1389_ = lean_unbox_usize(v_i_1386_);
lean_dec(v_i_1386_);
v_stop_boxed_1390_ = lean_unbox_usize(v_stop_1387_);
lean_dec(v_stop_1387_);
v_res_1391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1385_, v_i_boxed_1389_, v_stop_boxed_1390_, v_b_1388_);
lean_dec_ref(v_as_1385_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1392_, lean_object* v_names_1393_, lean_object* v_k_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_){
_start:
{
lean_object* v_lctx_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v_lctx_1400_ = lean_ctor_get(v_a_1395_, 2);
v___x_1401_ = l_Array_zip___redArg(v_fvars_1392_, v_names_1393_);
v___x_1402_ = lean_unsigned_to_nat(0u);
v___x_1403_ = lean_array_get_size(v___x_1401_);
v___x_1404_ = lean_nat_dec_lt(v___x_1402_, v___x_1403_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; 
lean_dec_ref(v___x_1401_);
lean_inc_ref(v_lctx_1400_);
v___x_1405_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1400_, v_k_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
return v___x_1405_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_le(v___x_1403_, v___x_1403_);
if (v___x_1406_ == 0)
{
if (v___x_1404_ == 0)
{
lean_object* v___x_1407_; 
lean_dec_ref(v___x_1401_);
lean_inc_ref(v_lctx_1400_);
v___x_1407_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1400_, v_k_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
return v___x_1407_;
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1403_);
lean_inc_ref(v_lctx_1400_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1401_, v___x_1408_, v___x_1409_, v_lctx_1400_);
lean_dec_ref(v___x_1401_);
v___x_1411_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1410_, v_k_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
return v___x_1411_;
}
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = lean_usize_of_nat(v___x_1403_);
lean_inc_ref(v_lctx_1400_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1401_, v___x_1412_, v___x_1413_, v_lctx_1400_);
lean_dec_ref(v___x_1401_);
v___x_1415_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1414_, v_k_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_);
return v___x_1415_;
}
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
uint8_t v_val_12196__boxed_1628_; lean_object* v_res_1629_; 
v_val_12196__boxed_1628_ = lean_unbox(v_val_1621_);
v_res_1629_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__4(v_val_12196__boxed_1628_, v_a_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
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
uint8_t v_____do__lift_12390__boxed_1784_; lean_object* v_res_1785_; 
v_____do__lift_12390__boxed_1784_ = lean_unbox(v_____do__lift_1783_);
v_res_1785_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v___x_1771_, v_a_1772_, v_inst_1773_, v_toBind_1774_, v___f_1775_, v_fst_1776_, v_fst_1777_, v___x_1778_, v___x_1779_, v___x_1780_, v_fst_1781_, v_toPure_1782_, v_____do__lift_12390__boxed_1784_);
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
uint8_t v___x_12843__boxed_2151_; uint8_t v___x_12844__boxed_2152_; lean_object* v_res_2153_; 
v___x_12843__boxed_2151_ = lean_unbox(v___x_2147_);
v___x_12844__boxed_2152_ = lean_unbox(v___x_2148_);
v_res_2153_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2145_, v_ys4_2146_, v___x_12843__boxed_2151_, v___x_12844__boxed_2152_, v_inst_2149_, v_alt_x27_2150_);
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
uint8_t v___x_12896__boxed_2213_; uint8_t v___x_12897__boxed_2214_; lean_object* v_res_2215_; 
v___x_12896__boxed_2213_ = lean_unbox(v___x_2200_);
v___x_12897__boxed_2214_ = lean_unbox(v___x_2201_);
v_res_2215_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2199_, v___x_12896__boxed_2213_, v___x_12897__boxed_2214_, v_inst_2202_, v_remaining_x27_2203_, v_onAlt_2204_, v_next_2205_, v_toBind_2206_, v___x_2207_, v_inst_2208_, v_inst_2209_, v___f_2210_, v_ys4_2211_, v_altType_2212_);
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
uint8_t v___x_12931__boxed_2249_; uint8_t v___x_12932__boxed_2250_; lean_object* v_res_2251_; 
v___x_12931__boxed_2249_ = lean_unbox(v___x_2235_);
v___x_12932__boxed_2250_ = lean_unbox(v___x_2236_);
v_res_2251_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_12931__boxed_2249_, v___x_12932__boxed_2250_, v_inst_2237_, v_remaining_x27_2238_, v_onAlt_2239_, v_next_2240_, v_toBind_2241_, v___x_2242_, v_inst_2243_, v_inst_2244_, v___f_2245_, v_fst_2246_, v_xs_2247_, v_altType_2248_);
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
uint8_t v___x_12982__boxed_2415_; uint8_t v___x_12983__boxed_2416_; lean_object* v_res_2417_; 
v___x_12982__boxed_2415_ = lean_unbox(v___x_2402_);
v___x_12983__boxed_2416_ = lean_unbox(v___x_2403_);
v_res_2417_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2398_, v_toPure_2399_, v_toBind_2400_, v___f_2401_, v___x_12982__boxed_2415_, v___x_12983__boxed_2416_, v_inst_2404_, v_remaining_x27_2405_, v_onAlt_2406_, v_inst_2407_, v_inst_2408_, v___f_2409_, v_fst_2410_, v_next_2411_, v_acc_2412_, v_h_2413_, v_G_2414_);
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
uint8_t v___x_13239__boxed_2482_; uint8_t v___x_13240__boxed_2483_; lean_object* v_res_2484_; 
v___x_13239__boxed_2482_ = lean_unbox(v___x_2468_);
v___x_13240__boxed_2483_ = lean_unbox(v___x_2469_);
v_res_2484_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2464_, v_toPure_2465_, v_toBind_2466_, v___f_2467_, v___x_13239__boxed_2482_, v___x_13240__boxed_2483_, v_inst_2470_, v_remaining_x27_2471_, v_onAlt_2472_, v_inst_2473_, v_inst_2474_, v___f_2475_, v_fst_2476_, v_matcherApp_2477_, v___x_2478_, v___f_2479_, v_aux_2480_, v_____r_2481_);
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
uint8_t v___x_13393__boxed_2581_; uint8_t v_useSplitter_boxed_2582_; lean_object* v_res_2583_; 
v___x_13393__boxed_2581_ = lean_unbox(v___x_2577_);
v_useSplitter_boxed_2582_ = lean_unbox(v_useSplitter_2578_);
v_res_2583_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2573_, v_ys2_2574_, v_ys3_2575_, v_ys4_2576_, v___x_13393__boxed_2581_, v_useSplitter_boxed_2582_, v_inst_2579_, v_alt_x27_2580_);
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
uint8_t v___x_13429__boxed_2638_; uint8_t v_useSplitter_boxed_2639_; lean_object* v_res_2640_; 
v___x_13429__boxed_2638_ = lean_unbox(v___x_2627_);
v_useSplitter_boxed_2639_ = lean_unbox(v_useSplitter_2628_);
v_res_2640_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_toMonadExceptOf_2623_, v_ys_2624_, v_ys2_2625_, v_ys3_2626_, v___x_13429__boxed_2638_, v_useSplitter_boxed_2639_, v_inst_2629_, v_args_2630_, v_onAlt_2631_, v_next_2632_, v_toBind_2633_, v___x_2634_, v___f_2635_, v_ys4_2636_, v_altType_2637_);
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
uint8_t v___x_13459__boxed_2680_; uint8_t v_useSplitter_boxed_2681_; lean_object* v_res_2682_; 
v___x_13459__boxed_2680_ = lean_unbox(v___x_2666_);
v_useSplitter_boxed_2681_ = lean_unbox(v_useSplitter_2667_);
v_res_2682_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_toMonadExceptOf_2663_, v_ys_2664_, v_ys2_2665_, v___x_13459__boxed_2680_, v_useSplitter_boxed_2681_, v_inst_2668_, v_args_2669_, v_onAlt_2670_, v_next_2671_, v_toBind_2672_, v___x_2673_, v___f_2674_, v_fst_2675_, v_inst_2676_, v_inst_2677_, v_ys3_2678_, v_altType_2679_);
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
uint8_t v___x_13487__boxed_2722_; uint8_t v_useSplitter_boxed_2723_; lean_object* v_res_2724_; 
v___x_13487__boxed_2722_ = lean_unbox(v___x_2707_);
v_useSplitter_boxed_2723_ = lean_unbox(v_useSplitter_2708_);
v_res_2724_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_toMonadExceptOf_2705_, v_ys_2706_, v___x_13487__boxed_2722_, v_useSplitter_boxed_2723_, v_inst_2709_, v_args_2710_, v_onAlt_2711_, v_next_2712_, v_toBind_2713_, v___x_2714_, v___f_2715_, v_fst_2716_, v_inst_2717_, v_inst_2718_, v_numDiscrEqs_2719_, v_ys2_2720_, v_altType_2721_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v___f_2728_, uint8_t v___x_2729_, lean_object* v_toBind_2730_, lean_object* v___f_2731_, lean_object* v_altType_2732_){
_start:
{
lean_object* v_numOverlaps_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; 
v_numOverlaps_2733_ = lean_ctor_get(v___x_2725_, 1);
lean_inc(v_numOverlaps_2733_);
v___x_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2734_, 0, v_numOverlaps_2733_);
v___x_2735_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2726_, v_inst_2727_, v_altType_2732_, v___x_2734_, v___f_2728_, v___x_2729_, v___x_2729_);
v___x_2736_ = lean_apply_4(v_toBind_2730_, lean_box(0), lean_box(0), v___x_2735_, v___f_2731_);
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v___f_2740_, lean_object* v___x_2741_, lean_object* v_toBind_2742_, lean_object* v___f_2743_, lean_object* v_altType_2744_){
_start:
{
uint8_t v___x_13519__boxed_2745_; lean_object* v_res_2746_; 
v___x_13519__boxed_2745_ = lean_unbox(v___x_2741_);
v_res_2746_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2737_, v_inst_2738_, v_inst_2739_, v___f_2740_, v___x_13519__boxed_2745_, v_toBind_2742_, v___f_2743_, v_altType_2744_);
lean_dec_ref(v___x_2737_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2747_, lean_object* v_altType_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_apply_1(v___f_2747_, v_altType_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2756_ = l_Lean_mkConst(v___x_2755_, v___x_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(lean_object* v___x_2757_, lean_object* v_toPure_2758_, lean_object* v_toBind_2759_, lean_object* v___f_2760_, lean_object* v___x_2761_, lean_object* v_inst_2762_, lean_object* v___f_2763_, lean_object* v_altType_2764_){
_start:
{
uint8_t v_hasUnitThunk_2765_; 
v_hasUnitThunk_2765_ = lean_ctor_get_uint8(v___x_2757_, sizeof(void*)*2);
if (v_hasUnitThunk_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
lean_dec(v___f_2763_);
lean_dec(v_inst_2762_);
v___x_2766_ = lean_apply_2(v_toPure_2758_, lean_box(0), v_altType_2764_);
v___x_2767_ = lean_apply_4(v_toBind_2759_, lean_box(0), lean_box(0), v___x_2766_, v___f_2760_);
return v___x_2767_;
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_dec(v___f_2760_);
lean_dec(v_toPure_2758_);
v___x_2768_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2761_);
v___x_2770_ = lean_array_push(v___x_2769_, v___x_2768_);
v___x_2771_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2771_, 0, v_altType_2764_);
lean_closure_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = lean_apply_2(v_inst_2762_, lean_box(0), v___x_2771_);
v___x_2773_ = lean_apply_4(v_toBind_2759_, lean_box(0), lean_box(0), v___x_2772_, v___f_2763_);
return v___x_2773_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v___x_2774_, lean_object* v_toPure_2775_, lean_object* v_toBind_2776_, lean_object* v___f_2777_, lean_object* v___x_2778_, lean_object* v_inst_2779_, lean_object* v___f_2780_, lean_object* v_altType_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v___x_2774_, v_toPure_2775_, v_toBind_2776_, v___f_2777_, v___x_2778_, v_inst_2779_, v___f_2780_, v_altType_2781_);
lean_dec(v___x_2778_);
lean_dec_ref(v___x_2774_);
return v_res_2782_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2786_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2787_ = lean_unsigned_to_nat(8u);
v___x_2788_ = lean_unsigned_to_nat(363u);
v___x_2789_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2790_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2791_ = l_mkPanicMessageWithDecl(v___x_2790_, v___x_2789_, v___x_2788_, v___x_2787_, v___x_2786_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2792_, lean_object* v___x_2793_, lean_object* v_toMonadExceptOf_2794_, uint8_t v___x_2795_, uint8_t v_useSplitter_2796_, lean_object* v_inst_2797_, lean_object* v_onAlt_2798_, lean_object* v_next_2799_, lean_object* v_toBind_2800_, lean_object* v___x_2801_, lean_object* v___f_2802_, lean_object* v_fst_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_numDiscrEqs_2806_, lean_object* v___f_2807_, lean_object* v___x_2808_, lean_object* v_toPure_2809_, lean_object* v___x_2810_, lean_object* v___x_2811_, lean_object* v_ys_2812_, lean_object* v_args_2813_){
_start:
{
lean_object* v_numFields_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_numFields_2814_ = lean_ctor_get(v___x_2792_, 0);
v___x_2815_ = lean_array_get_size(v_ys_2812_);
v___x_2816_ = lean_nat_dec_eq(v___x_2815_, v_numFields_2814_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref(v_args_2813_);
lean_dec_ref(v_ys_2812_);
lean_dec_ref(v___x_2811_);
lean_dec(v___x_2810_);
lean_dec(v_toPure_2809_);
lean_dec_ref(v___x_2808_);
lean_dec(v___f_2807_);
lean_dec(v_numDiscrEqs_2806_);
lean_dec_ref(v_inst_2805_);
lean_dec_ref(v_inst_2804_);
lean_dec(v_fst_2803_);
lean_dec(v___f_2802_);
lean_dec_ref(v___x_2801_);
lean_dec(v_toBind_2800_);
lean_dec(v_next_2799_);
lean_dec(v_onAlt_2798_);
lean_dec(v_inst_2797_);
lean_dec_ref(v_toMonadExceptOf_2794_);
lean_dec_ref(v___x_2792_);
v___x_2817_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2818_ = l_panic___redArg(v___x_2793_, v___x_2817_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___f_2821_; lean_object* v___x_2822_; lean_object* v___f_2823_; lean_object* v___f_2824_; lean_object* v___f_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2819_ = lean_box(v___x_2795_);
v___x_2820_ = lean_box(v_useSplitter_2796_);
lean_inc_ref(v_inst_2805_);
lean_inc_ref(v_inst_2804_);
lean_inc_n(v_toBind_2800_, 3);
lean_inc_n(v_inst_2797_, 2);
lean_inc_ref(v_ys_2812_);
v___f_2821_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2821_, 0, v_toMonadExceptOf_2794_);
lean_closure_set(v___f_2821_, 1, v_ys_2812_);
lean_closure_set(v___f_2821_, 2, v___x_2819_);
lean_closure_set(v___f_2821_, 3, v___x_2820_);
lean_closure_set(v___f_2821_, 4, v_inst_2797_);
lean_closure_set(v___f_2821_, 5, v_args_2813_);
lean_closure_set(v___f_2821_, 6, v_onAlt_2798_);
lean_closure_set(v___f_2821_, 7, v_next_2799_);
lean_closure_set(v___f_2821_, 8, v_toBind_2800_);
lean_closure_set(v___f_2821_, 9, v___x_2801_);
lean_closure_set(v___f_2821_, 10, v___f_2802_);
lean_closure_set(v___f_2821_, 11, v_fst_2803_);
lean_closure_set(v___f_2821_, 12, v_inst_2804_);
lean_closure_set(v___f_2821_, 13, v_inst_2805_);
lean_closure_set(v___f_2821_, 14, v_numDiscrEqs_2806_);
v___x_2822_ = lean_box(v___x_2795_);
v___f_2823_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2823_, 0, v___x_2792_);
lean_closure_set(v___f_2823_, 1, v_inst_2804_);
lean_closure_set(v___f_2823_, 2, v_inst_2805_);
lean_closure_set(v___f_2823_, 3, v___f_2821_);
lean_closure_set(v___f_2823_, 4, v___x_2822_);
lean_closure_set(v___f_2823_, 5, v_toBind_2800_);
lean_closure_set(v___f_2823_, 6, v___f_2807_);
v___f_2824_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2824_, 0, v___f_2823_);
lean_inc_ref(v___f_2824_);
v___f_2825_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2825_, 0, v___x_2808_);
lean_closure_set(v___f_2825_, 1, v_toPure_2809_);
lean_closure_set(v___f_2825_, 2, v_toBind_2800_);
lean_closure_set(v___f_2825_, 3, v___f_2824_);
lean_closure_set(v___f_2825_, 4, v___x_2810_);
lean_closure_set(v___f_2825_, 5, v_inst_2797_);
lean_closure_set(v___f_2825_, 6, v___f_2824_);
v___x_2826_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2826_, 0, v___x_2811_);
lean_closure_set(v___x_2826_, 1, v_ys_2812_);
v___x_2827_ = lean_apply_2(v_inst_2797_, lean_box(0), v___x_2826_);
v___x_2828_ = lean_apply_4(v_toBind_2800_, lean_box(0), lean_box(0), v___x_2827_, v___f_2825_);
return v___x_2828_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2829_ = _args[0];
lean_object* v___x_2830_ = _args[1];
lean_object* v_toMonadExceptOf_2831_ = _args[2];
lean_object* v___x_2832_ = _args[3];
lean_object* v_useSplitter_2833_ = _args[4];
lean_object* v_inst_2834_ = _args[5];
lean_object* v_onAlt_2835_ = _args[6];
lean_object* v_next_2836_ = _args[7];
lean_object* v_toBind_2837_ = _args[8];
lean_object* v___x_2838_ = _args[9];
lean_object* v___f_2839_ = _args[10];
lean_object* v_fst_2840_ = _args[11];
lean_object* v_inst_2841_ = _args[12];
lean_object* v_inst_2842_ = _args[13];
lean_object* v_numDiscrEqs_2843_ = _args[14];
lean_object* v___f_2844_ = _args[15];
lean_object* v___x_2845_ = _args[16];
lean_object* v_toPure_2846_ = _args[17];
lean_object* v___x_2847_ = _args[18];
lean_object* v___x_2848_ = _args[19];
lean_object* v_ys_2849_ = _args[20];
lean_object* v_args_2850_ = _args[21];
_start:
{
uint8_t v___x_13616__boxed_2851_; uint8_t v_useSplitter_boxed_2852_; lean_object* v_res_2853_; 
v___x_13616__boxed_2851_ = lean_unbox(v___x_2832_);
v_useSplitter_boxed_2852_ = lean_unbox(v_useSplitter_2833_);
v_res_2853_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2829_, v___x_2830_, v_toMonadExceptOf_2831_, v___x_13616__boxed_2851_, v_useSplitter_boxed_2852_, v_inst_2834_, v_onAlt_2835_, v_next_2836_, v_toBind_2837_, v___x_2838_, v___f_2839_, v_fst_2840_, v_inst_2841_, v_inst_2842_, v_numDiscrEqs_2843_, v___f_2844_, v___x_2845_, v_toPure_2846_, v___x_2847_, v___x_2848_, v_ys_2849_, v_args_2850_);
lean_dec(v___x_2830_);
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
lean_inc(v___x_3042_);
lean_inc_ref(v_inst_2892_);
lean_inc_ref(v_inst_2891_);
lean_inc(v___x_3072_);
lean_inc(v_toBind_2879_);
v___f_3075_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 22, 20);
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
lean_closure_set(v___f_3075_, 16, v___x_3042_);
lean_closure_set(v___f_3075_, 17, v_toPure_2878_);
lean_closure_set(v___f_3075_, 18, v___x_2958_);
lean_closure_set(v___f_3075_, 19, v___x_2957_);
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
uint8_t v___x_13735__boxed_3138_; uint8_t v_useSplitter_boxed_3139_; lean_object* v_res_3140_; 
v___x_13735__boxed_3138_ = lean_unbox(v___x_3126_);
v_useSplitter_boxed_3139_ = lean_unbox(v_useSplitter_3127_);
v_res_3140_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3117_, v_toPure_3118_, v_toBind_3119_, v___f_3120_, v___x_3121_, v___x_3122_, v_inst_3123_, v___x_3124_, v_toMonadExceptOf_3125_, v___x_13735__boxed_3138_, v_useSplitter_boxed_3139_, v_onAlt_3128_, v___f_3129_, v_fst_3130_, v_inst_3131_, v_inst_3132_, v_numDiscrEqs_3133_, v_next_3134_, v_acc_3135_, v_h_3136_, v_G_3137_);
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
uint8_t v___x_14259__boxed_3371_; lean_object* v_res_3372_; 
v___x_14259__boxed_3371_ = lean_unbox(v___x_3367_);
v_res_3372_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3343_, v_params_x27_3344_, v_fst_3345_, v_discrs_x27_3346_, v_fst_3347_, v_numParams_3348_, v_numDiscrs_3349_, v_altInfos_3350_, v_uElimPos_x3f_3351_, v_snd_3352_, v_overlaps_3353_, v_matcherLevels_3354_, v_toPure_3355_, v_onRemaining_3356_, v_remaining_3357_, v_toBind_3358_, v_origAltTypes_3359_, v_alts_3360_, v___x_3361_, v___x_3362_, v_remaining_x27_3363_, v___f_3364_, v_inst_3365_, v___x_3366_, v___x_14259__boxed_3371_, v_liftWith_3368_, v_restoreM_3369_, v_matchEqns_3370_);
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
uint8_t v___x_14321__boxed_3434_; lean_object* v_res_3435_; 
v___x_14321__boxed_3434_ = lean_unbox(v___x_3429_);
v_res_3435_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3406_, v_params_x27_3407_, v_fst_3408_, v_discrs_x27_3409_, v_fst_3410_, v_numParams_3411_, v_numDiscrs_3412_, v_altInfos_3413_, v_uElimPos_x3f_3414_, v_snd_3415_, v_overlaps_3416_, v_matcherLevels_3417_, v_toPure_3418_, v_onRemaining_3419_, v_remaining_3420_, v_toBind_3421_, v_alts_3422_, v___x_3423_, v___x_3424_, v_remaining_x27_3425_, v___f_3426_, v_inst_3427_, v___x_3428_, v___x_14321__boxed_3434_, v_liftWith_3430_, v_restoreM_3431_, v_matcherName_3432_, v_origAltTypes_3433_);
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
uint8_t v___x_14355__boxed_3523_; uint8_t v_useSplitter_boxed_3524_; uint8_t v___x_14363__boxed_3525_; lean_object* v_res_3526_; 
v___x_14355__boxed_3523_ = lean_unbox(v___x_3493_);
v_useSplitter_boxed_3524_ = lean_unbox(v_useSplitter_3494_);
v___x_14363__boxed_3525_ = lean_unbox(v___x_3517_);
v_res_3526_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3484_, v_toPure_3485_, v_toBind_3486_, v___f_3487_, v___x_3488_, v___x_3489_, v_inst_3490_, v___x_3491_, v_toMonadExceptOf_3492_, v___x_14355__boxed_3523_, v_useSplitter_boxed_3524_, v_onAlt_3495_, v___f_3496_, v_fst_3497_, v_inst_3498_, v_inst_3499_, v_numDiscrEqs_3500_, v___x_3501_, v_params_x27_3502_, v_fst_3503_, v_discrs_x27_3504_, v_fst_3505_, v_numParams_3506_, v_numDiscrs_3507_, v_altInfos_3508_, v_uElimPos_x3f_3509_, v_snd_3510_, v_overlaps_3511_, v_matcherLevels_3512_, v_onRemaining_3513_, v_remaining_3514_, v_remaining_x27_3515_, v___x_3516_, v___x_14363__boxed_3525_, v_liftWith_3518_, v_restoreM_3519_, v_matcherName_3520_, v_aux1_3521_, v_____r_3522_);
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
uint8_t v___x_14435__boxed_3674_; uint8_t v_useSplitter_boxed_3675_; uint8_t v_isCasesOn_boxed_3676_; lean_object* v_res_3677_; 
v___x_14435__boxed_3674_ = lean_unbox(v___x_3657_);
v_useSplitter_boxed_3675_ = lean_unbox(v_useSplitter_3665_);
v_isCasesOn_boxed_3676_ = lean_unbox(v_isCasesOn_3666_);
v_res_3677_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3639_, v_numDiscrs_3640_, v_altInfos_3641_, v_uElimPos_x3f_3642_, v_snd_3643_, v_overlaps_3644_, v_matcherName_3645_, v_matcherLevels_3646_, v_params_x27_3647_, v_fst_3648_, v_discrs_x27_3649_, v_toPure_3650_, v_onRemaining_3651_, v_remaining_3652_, v_toBind_3653_, v_inst_3654_, v_alts_3655_, v___f_3656_, v___x_14435__boxed_3674_, v_inst_3658_, v_remaining_x27_3659_, v_onAlt_3660_, v_inst_3661_, v___f_3662_, v_matcherApp_3663_, v___x_3664_, v_useSplitter_boxed_3675_, v_isCasesOn_boxed_3676_, v___f_3667_, v___x_3668_, v___x_3669_, v_toMonadExceptOf_3670_, v___f_3671_, v_numDiscrEqs_3672_, v_____s_3673_);
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
uint8_t v___x_14597__boxed_3762_; uint8_t v_useSplitter_boxed_3763_; uint8_t v_isCasesOn_boxed_3764_; lean_object* v_res_3765_; 
v___x_14597__boxed_3762_ = lean_unbox(v___x_3745_);
v_useSplitter_boxed_3763_ = lean_unbox(v_useSplitter_3751_);
v_isCasesOn_boxed_3764_ = lean_unbox(v_isCasesOn_3752_);
v_res_3765_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3728_, v_numDiscrs_3729_, v_altInfos_3730_, v_uElimPos_x3f_3731_, v_snd_3732_, v_overlaps_3733_, v_matcherName_3734_, v_params_x27_3735_, v_fst_3736_, v_discrs_x27_3737_, v_toPure_3738_, v_onRemaining_3739_, v_remaining_3740_, v_toBind_3741_, v_inst_3742_, v_alts_3743_, v___f_3744_, v___x_14597__boxed_3762_, v_inst_3746_, v_onAlt_3747_, v_inst_3748_, v___f_3749_, v_matcherApp_3750_, v_useSplitter_boxed_3763_, v_isCasesOn_boxed_3764_, v___f_3753_, v___x_3754_, v___x_3755_, v_toMonadExceptOf_3756_, v___f_3757_, v_numDiscrEqs_3758_, v_fst_3759_, v___f_3760_, v_matcherLevels_3761_);
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
uint8_t v___x_14669__boxed_3848_; uint8_t v_useSplitter_boxed_3849_; uint8_t v_isCasesOn_boxed_3850_; lean_object* v_res_3851_; 
v___x_14669__boxed_3848_ = lean_unbox(v___x_3831_);
v_useSplitter_boxed_3849_ = lean_unbox(v_useSplitter_3837_);
v_isCasesOn_boxed_3850_ = lean_unbox(v_isCasesOn_3838_);
v_res_3851_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3820_, v_matcherName_3821_, v_params_x27_3822_, v_discrs_x27_3823_, v_toPure_3824_, v_onRemaining_3825_, v_remaining_3826_, v_toBind_3827_, v_inst_3828_, v_alts_3829_, v___f_3830_, v___x_14669__boxed_3848_, v_inst_3832_, v_onAlt_3833_, v_inst_3834_, v___f_3835_, v_matcherApp_3836_, v_useSplitter_boxed_3849_, v_isCasesOn_boxed_3850_, v___f_3839_, v___x_3840_, v___x_3841_, v_toMonadExceptOf_3842_, v___f_3843_, v_numDiscrEqs_3844_, v___f_3845_, v_matcherLevels_3846_, v_____x_3847_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v_suppressElabErrors_4325_, uint8_t v___y_4326_, lean_object* v_x_4327_){
_start:
{
if (lean_obj_tag(v_x_4327_) == 1)
{
lean_object* v_pre_4328_; 
v_pre_4328_ = lean_ctor_get(v_x_4327_, 0);
switch(lean_obj_tag(v_pre_4328_))
{
case 1:
{
lean_object* v_pre_4329_; 
v_pre_4329_ = lean_ctor_get(v_pre_4328_, 0);
switch(lean_obj_tag(v_pre_4329_))
{
case 0:
{
lean_object* v_str_4330_; lean_object* v_str_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; 
v_str_4330_ = lean_ctor_get(v_x_4327_, 1);
v_str_4331_ = lean_ctor_get(v_pre_4328_, 1);
v___x_4332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4333_ = lean_string_dec_eq(v_str_4331_, v___x_4332_);
if (v___x_4333_ == 0)
{
lean_object* v___x_4334_; uint8_t v___x_4335_; 
v___x_4334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4335_ = lean_string_dec_eq(v_str_4331_, v___x_4334_);
if (v___x_4335_ == 0)
{
return v___x_4335_;
}
else
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4337_ = lean_string_dec_eq(v_str_4330_, v___x_4336_);
if (v___x_4337_ == 0)
{
return v___x_4337_;
}
else
{
return v_suppressElabErrors_4325_;
}
}
}
else
{
lean_object* v___x_4338_; uint8_t v___x_4339_; 
v___x_4338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4339_ = lean_string_dec_eq(v_str_4330_, v___x_4338_);
if (v___x_4339_ == 0)
{
return v___x_4339_;
}
else
{
return v_suppressElabErrors_4325_;
}
}
}
case 1:
{
lean_object* v_pre_4340_; 
v_pre_4340_ = lean_ctor_get(v_pre_4329_, 0);
if (lean_obj_tag(v_pre_4340_) == 0)
{
lean_object* v_str_4341_; lean_object* v_str_4342_; lean_object* v_str_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; 
v_str_4341_ = lean_ctor_get(v_x_4327_, 1);
v_str_4342_ = lean_ctor_get(v_pre_4328_, 1);
v_str_4343_ = lean_ctor_get(v_pre_4329_, 1);
v___x_4344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4345_ = lean_string_dec_eq(v_str_4343_, v___x_4344_);
if (v___x_4345_ == 0)
{
return v___x_4345_;
}
else
{
lean_object* v___x_4346_; uint8_t v___x_4347_; 
v___x_4346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4347_ = lean_string_dec_eq(v_str_4342_, v___x_4346_);
if (v___x_4347_ == 0)
{
return v___x_4347_;
}
else
{
lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4348_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4349_ = lean_string_dec_eq(v_str_4341_, v___x_4348_);
if (v___x_4349_ == 0)
{
return v___x_4349_;
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
return v___y_4326_;
}
}
default: 
{
return v___y_4326_;
}
}
}
case 0:
{
lean_object* v_str_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
v_str_4350_ = lean_ctor_get(v_x_4327_, 1);
v___x_4351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4352_ = lean_string_dec_eq(v_str_4350_, v___x_4351_);
if (v___x_4352_ == 0)
{
return v___x_4352_;
}
else
{
return v_suppressElabErrors_4325_;
}
}
default: 
{
return v___y_4326_;
}
}
}
else
{
return v___y_4326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_4353_, lean_object* v___y_4354_, lean_object* v_x_4355_){
_start:
{
uint8_t v_suppressElabErrors_boxed_4356_; uint8_t v___y_32220__boxed_4357_; uint8_t v_res_4358_; lean_object* v_r_4359_; 
v_suppressElabErrors_boxed_4356_ = lean_unbox(v_suppressElabErrors_4353_);
v___y_32220__boxed_4357_ = lean_unbox(v___y_4354_);
v_res_4358_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v_suppressElabErrors_boxed_4356_, v___y_32220__boxed_4357_, v_x_4355_);
lean_dec(v_x_4355_);
v_r_4359_ = lean_box(v_res_4358_);
return v_r_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4361_, lean_object* v_msgData_4362_, uint8_t v_severity_4363_, uint8_t v_isSilent_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___y_4371_; lean_object* v___y_4372_; uint8_t v___y_4373_; lean_object* v___y_4374_; uint8_t v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v_toCold_4378_; lean_object* v___y_4379_; lean_object* v___y_4408_; lean_object* v___y_4409_; lean_object* v___y_4410_; uint8_t v___y_4411_; uint8_t v___y_4412_; lean_object* v___y_4413_; uint8_t v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4435_; lean_object* v___y_4436_; uint8_t v___y_4437_; uint8_t v___y_4438_; lean_object* v___y_4439_; uint8_t v___y_4440_; lean_object* v___y_4441_; uint8_t v___y_4445_; uint8_t v___y_4446_; uint8_t v___y_4447_; uint8_t v___x_4458_; uint8_t v___y_4460_; uint8_t v___y_4461_; uint8_t v___y_4462_; uint8_t v___y_4464_; uint8_t v___x_4472_; 
v___x_4458_ = 2;
v___x_4472_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4363_, v___x_4458_);
if (v___x_4472_ == 0)
{
v___y_4464_ = v___x_4472_;
goto v___jp_4463_;
}
else
{
uint8_t v___x_4473_; 
lean_inc_ref(v_msgData_4362_);
v___x_4473_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4362_);
v___y_4464_ = v___x_4473_;
goto v___jp_4463_;
}
v___jp_4370_:
{
lean_object* v_currNamespace_4380_; lean_object* v_openDecls_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v_env_4386_; lean_object* v_nextMacroScope_4387_; lean_object* v_ngen_4388_; lean_object* v_auxDeclNGen_4389_; lean_object* v_traceState_4390_; lean_object* v_cache_4391_; lean_object* v_recordedDeps_4392_; lean_object* v_messages_4393_; lean_object* v_infoState_4394_; lean_object* v_snapshotTasks_4395_; lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4406_; 
v_currNamespace_4380_ = lean_ctor_get(v_toCold_4378_, 4);
v_openDecls_4381_ = lean_ctor_get(v_toCold_4378_, 5);
lean_inc(v_openDecls_4381_);
lean_inc(v_currNamespace_4380_);
v___x_4382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4382_, 0, v_currNamespace_4380_);
lean_ctor_set(v___x_4382_, 1, v_openDecls_4381_);
v___x_4383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4382_);
lean_ctor_set(v___x_4383_, 1, v___y_4377_);
lean_inc_ref(v___y_4372_);
lean_inc_ref(v___y_4376_);
v___x_4384_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4384_, 0, v___y_4376_);
lean_ctor_set(v___x_4384_, 1, v___y_4374_);
lean_ctor_set(v___x_4384_, 2, v___y_4371_);
lean_ctor_set(v___x_4384_, 3, v___y_4372_);
lean_ctor_set(v___x_4384_, 4, v___x_4383_);
lean_ctor_set_uint8(v___x_4384_, sizeof(void*)*5, v___y_4373_);
lean_ctor_set_uint8(v___x_4384_, sizeof(void*)*5 + 1, v___y_4375_);
lean_ctor_set_uint8(v___x_4384_, sizeof(void*)*5 + 2, v_isSilent_4364_);
v___x_4385_ = lean_st_ref_take(v___y_4379_);
v_env_4386_ = lean_ctor_get(v___x_4385_, 0);
v_nextMacroScope_4387_ = lean_ctor_get(v___x_4385_, 1);
v_ngen_4388_ = lean_ctor_get(v___x_4385_, 2);
v_auxDeclNGen_4389_ = lean_ctor_get(v___x_4385_, 3);
v_traceState_4390_ = lean_ctor_get(v___x_4385_, 4);
v_cache_4391_ = lean_ctor_get(v___x_4385_, 5);
v_recordedDeps_4392_ = lean_ctor_get(v___x_4385_, 6);
v_messages_4393_ = lean_ctor_get(v___x_4385_, 7);
v_infoState_4394_ = lean_ctor_get(v___x_4385_, 8);
v_snapshotTasks_4395_ = lean_ctor_get(v___x_4385_, 9);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4385_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4397_ = v___x_4385_;
v_isShared_4398_ = v_isSharedCheck_4406_;
goto v_resetjp_4396_;
}
else
{
lean_inc(v_snapshotTasks_4395_);
lean_inc(v_infoState_4394_);
lean_inc(v_messages_4393_);
lean_inc(v_recordedDeps_4392_);
lean_inc(v_cache_4391_);
lean_inc(v_traceState_4390_);
lean_inc(v_auxDeclNGen_4389_);
lean_inc(v_ngen_4388_);
lean_inc(v_nextMacroScope_4387_);
lean_inc(v_env_4386_);
lean_dec(v___x_4385_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4406_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4402_; 
v___x_4399_ = lean_box(0);
v___x_4400_ = l_Lean_MessageLog_add(v___x_4384_, v_messages_4393_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 7, v___x_4400_);
v___x_4402_ = v___x_4397_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_env_4386_);
lean_ctor_set(v_reuseFailAlloc_4405_, 1, v_nextMacroScope_4387_);
lean_ctor_set(v_reuseFailAlloc_4405_, 2, v_ngen_4388_);
lean_ctor_set(v_reuseFailAlloc_4405_, 3, v_auxDeclNGen_4389_);
lean_ctor_set(v_reuseFailAlloc_4405_, 4, v_traceState_4390_);
lean_ctor_set(v_reuseFailAlloc_4405_, 5, v_cache_4391_);
lean_ctor_set(v_reuseFailAlloc_4405_, 6, v_recordedDeps_4392_);
lean_ctor_set(v_reuseFailAlloc_4405_, 7, v___x_4400_);
lean_ctor_set(v_reuseFailAlloc_4405_, 8, v_infoState_4394_);
lean_ctor_set(v_reuseFailAlloc_4405_, 9, v_snapshotTasks_4395_);
v___x_4402_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = lean_st_ref_put(v___y_4379_, v___x_4402_);
v___x_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4399_);
return v___x_4404_;
}
}
}
v___jp_4407_:
{
lean_object* v_fileName_4416_; lean_object* v_fileMap_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4433_; 
v_fileName_4416_ = lean_ctor_get(v___y_4410_, 0);
v_fileMap_4417_ = lean_ctor_get(v___y_4410_, 1);
v___x_4418_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4362_);
v___x_4419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4418_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4422_ = v___x_4419_;
v_isShared_4423_ = v_isSharedCheck_4433_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4419_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4433_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; 
lean_inc_ref_n(v_fileMap_4417_, 2);
v___x_4424_ = l_Lean_FileMap_toPosition(v_fileMap_4417_, v___y_4413_);
lean_dec(v___y_4413_);
v___x_4425_ = l_Lean_FileMap_toPosition(v_fileMap_4417_, v___y_4415_);
lean_dec(v___y_4415_);
v___x_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
v___x_4427_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4412_ == 0)
{
lean_del_object(v___x_4422_);
lean_dec_ref(v___y_4409_);
v___y_4371_ = v___x_4426_;
v___y_4372_ = v___x_4427_;
v___y_4373_ = v___y_4411_;
v___y_4374_ = v___x_4424_;
v___y_4375_ = v___y_4414_;
v___y_4376_ = v_fileName_4416_;
v___y_4377_ = v_a_4420_;
v_toCold_4378_ = v___y_4408_;
v___y_4379_ = v___y_4368_;
goto v___jp_4370_;
}
else
{
uint8_t v___x_4428_; 
lean_inc(v_a_4420_);
v___x_4428_ = l_Lean_MessageData_hasTag(v___y_4409_, v_a_4420_);
if (v___x_4428_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4431_; 
lean_dec_ref_known(v___x_4426_, 1);
lean_dec_ref(v___x_4424_);
lean_dec(v_a_4420_);
v___x_4429_ = lean_box(0);
if (v_isShared_4423_ == 0)
{
lean_ctor_set(v___x_4422_, 0, v___x_4429_);
v___x_4431_ = v___x_4422_;
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
else
{
lean_del_object(v___x_4422_);
v___y_4371_ = v___x_4426_;
v___y_4372_ = v___x_4427_;
v___y_4373_ = v___y_4411_;
v___y_4374_ = v___x_4424_;
v___y_4375_ = v___y_4414_;
v___y_4376_ = v_fileName_4416_;
v___y_4377_ = v_a_4420_;
v_toCold_4378_ = v___y_4408_;
v___y_4379_ = v___y_4368_;
goto v___jp_4370_;
}
}
}
}
v___jp_4434_:
{
lean_object* v___x_4442_; 
v___x_4442_ = l_Lean_Syntax_getTailPos_x3f(v___y_4439_, v___y_4438_);
lean_dec(v___y_4439_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_inc(v___y_4441_);
v___y_4408_ = v___y_4435_;
v___y_4409_ = v___y_4436_;
v___y_4410_ = v___y_4435_;
v___y_4411_ = v___y_4438_;
v___y_4412_ = v___y_4437_;
v___y_4413_ = v___y_4441_;
v___y_4414_ = v___y_4440_;
v___y_4415_ = v___y_4441_;
goto v___jp_4407_;
}
else
{
lean_object* v_val_4443_; 
v_val_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_val_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v___y_4408_ = v___y_4435_;
v___y_4409_ = v___y_4436_;
v___y_4410_ = v___y_4435_;
v___y_4411_ = v___y_4438_;
v___y_4412_ = v___y_4437_;
v___y_4413_ = v___y_4441_;
v___y_4414_ = v___y_4440_;
v___y_4415_ = v_val_4443_;
goto v___jp_4407_;
}
}
v___jp_4444_:
{
lean_object* v_toCold_4448_; lean_object* v_ref_4449_; uint8_t v_suppressElabErrors_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___f_4453_; lean_object* v_ref_4454_; lean_object* v___x_4455_; 
v_toCold_4448_ = lean_ctor_get(v___y_4367_, 0);
v_ref_4449_ = lean_ctor_get(v___y_4367_, 2);
v_suppressElabErrors_4450_ = lean_ctor_get_uint8(v___y_4367_, sizeof(void*)*3 + 2);
v___x_4451_ = lean_box(v_suppressElabErrors_4450_);
v___x_4452_ = lean_box(v___y_4445_);
v___f_4453_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4453_, 0, v___x_4451_);
lean_closure_set(v___f_4453_, 1, v___x_4452_);
v_ref_4454_ = l_Lean_replaceRef(v_ref_4361_, v_ref_4449_);
v___x_4455_ = l_Lean_Syntax_getPos_x3f(v_ref_4454_, v___y_4446_);
if (lean_obj_tag(v___x_4455_) == 0)
{
lean_object* v___x_4456_; 
v___x_4456_ = lean_unsigned_to_nat(0u);
v___y_4435_ = v_toCold_4448_;
v___y_4436_ = v___f_4453_;
v___y_4437_ = v_suppressElabErrors_4450_;
v___y_4438_ = v___y_4446_;
v___y_4439_ = v_ref_4454_;
v___y_4440_ = v___y_4447_;
v___y_4441_ = v___x_4456_;
goto v___jp_4434_;
}
else
{
lean_object* v_val_4457_; 
v_val_4457_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_val_4457_);
lean_dec_ref_known(v___x_4455_, 1);
v___y_4435_ = v_toCold_4448_;
v___y_4436_ = v___f_4453_;
v___y_4437_ = v_suppressElabErrors_4450_;
v___y_4438_ = v___y_4446_;
v___y_4439_ = v_ref_4454_;
v___y_4440_ = v___y_4447_;
v___y_4441_ = v_val_4457_;
goto v___jp_4434_;
}
}
v___jp_4459_:
{
if (v___y_4462_ == 0)
{
v___y_4445_ = v___y_4460_;
v___y_4446_ = v___y_4461_;
v___y_4447_ = v_severity_4363_;
goto v___jp_4444_;
}
else
{
v___y_4445_ = v___y_4460_;
v___y_4446_ = v___y_4461_;
v___y_4447_ = v___x_4458_;
goto v___jp_4444_;
}
}
v___jp_4463_:
{
if (v___y_4464_ == 0)
{
uint8_t v___x_4465_; uint8_t v___x_4466_; 
v___x_4465_ = 1;
v___x_4466_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4363_, v___x_4465_);
if (v___x_4466_ == 0)
{
v___y_4460_ = v___y_4464_;
v___y_4461_ = v___y_4464_;
v___y_4462_ = v___x_4466_;
goto v___jp_4459_;
}
else
{
lean_object* v___x_4467_; lean_object* v___x_4468_; uint8_t v___x_4469_; 
v___x_4467_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4367_);
v___x_4468_ = l_Lean_warningAsError;
v___x_4469_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v___x_4467_, v___x_4468_);
lean_dec_ref(v___x_4467_);
v___y_4460_ = v___y_4464_;
v___y_4461_ = v___y_4464_;
v___y_4462_ = v___x_4469_;
goto v___jp_4459_;
}
}
else
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
lean_dec_ref(v_msgData_4362_);
v___x_4470_ = lean_box(0);
v___x_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4470_);
return v___x_4471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4474_, lean_object* v_msgData_4475_, lean_object* v_severity_4476_, lean_object* v_isSilent_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
uint8_t v_severity_boxed_4483_; uint8_t v_isSilent_boxed_4484_; lean_object* v_res_4485_; 
v_severity_boxed_4483_ = lean_unbox(v_severity_4476_);
v_isSilent_boxed_4484_ = lean_unbox(v_isSilent_4477_);
v_res_4485_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4474_, v_msgData_4475_, v_severity_boxed_4483_, v_isSilent_boxed_4484_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec(v_ref_4474_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4486_, uint8_t v_severity_4487_, uint8_t v_isSilent_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v_ref_4494_; lean_object* v___x_4495_; 
v_ref_4494_ = lean_ctor_get(v___y_4491_, 2);
v___x_4495_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4494_, v_msgData_4486_, v_severity_4487_, v_isSilent_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4496_, lean_object* v_severity_4497_, lean_object* v_isSilent_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
uint8_t v_severity_boxed_4504_; uint8_t v_isSilent_boxed_4505_; lean_object* v_res_4506_; 
v_severity_boxed_4504_ = lean_unbox(v_severity_4497_);
v_isSilent_boxed_4505_ = lean_unbox(v_isSilent_4498_);
v_res_4506_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4496_, v_severity_boxed_4504_, v_isSilent_boxed_4505_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
uint8_t v___x_4513_; uint8_t v___x_4514_; lean_object* v___x_4515_; 
v___x_4513_ = 0;
v___x_4514_ = 0;
v___x_4515_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4507_, v___x_4513_, v___x_4514_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
return v_res_4522_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4525_ = l_Lean_stringToMessageData(v___x_4524_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4526_, lean_object* v___altIdx_4527_, lean_object* v_expAltType_4528_, lean_object* v___altFVars_4529_, lean_object* v_alt_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v___x_4536_; 
lean_inc(v___y_4534_);
lean_inc_ref(v___y_4533_);
lean_inc(v___y_4532_);
lean_inc_ref(v___y_4531_);
lean_inc_ref(v_alt_4530_);
v___x_4536_ = lean_infer_type(v_alt_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4537_);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = l_Lean_Meta_mkEq(v_expAltType_4528_, v_a_4537_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_object* v_a_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v___x_4538_, 1);
v___x_4540_ = lean_box(0);
v___x_4541_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4539_, v___x_4540_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___y_4544_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___x_4554_ = l_Lean_Expr_mvarId_x21(v_a_4542_);
v___x_4555_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4554_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc_n(v_a_4556_, 2);
lean_dec_ref_known(v___x_4555_, 1);
v___x_4557_ = l_Lean_MVarId_refl(v_a_4556_, v___x_4526_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_dec(v_a_4556_);
v___y_4544_ = v___x_4557_;
goto v___jp_4543_;
}
else
{
lean_object* v_a_4558_; uint8_t v___y_4560_; uint8_t v___x_4573_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
v___x_4573_ = l_Lean_Exception_isInterrupt(v_a_4558_);
if (v___x_4573_ == 0)
{
uint8_t v___x_4574_; 
v___x_4574_ = l_Lean_Exception_isRuntime(v_a_4558_);
v___y_4560_ = v___x_4574_;
goto v___jp_4559_;
}
else
{
lean_dec(v_a_4558_);
v___y_4560_ = v___x_4573_;
goto v___jp_4559_;
}
v___jp_4559_:
{
if (v___y_4560_ == 0)
{
lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4571_; 
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4557_);
if (v_isSharedCheck_4571_ == 0)
{
lean_object* v_unused_4572_; 
v_unused_4572_ = lean_ctor_get(v___x_4557_, 0);
lean_dec(v_unused_4572_);
v___x_4562_ = v___x_4557_;
v_isShared_4563_ = v_isSharedCheck_4571_;
goto v_resetjp_4561_;
}
else
{
lean_dec(v___x_4557_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4571_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4564_; lean_object* v___x_4566_; 
v___x_4564_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4556_);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 0, v_a_4556_);
v___x_4566_ = v___x_4562_;
goto v_reusejp_4565_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_a_4556_);
v___x_4566_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4565_;
}
v_reusejp_4565_:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; 
v___x_4567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4567_, 0, v___x_4564_);
lean_ctor_set(v___x_4567_, 1, v___x_4566_);
v___x_4568_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4567_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
if (lean_obj_tag(v___x_4568_) == 0)
{
lean_object* v___x_4569_; 
lean_dec_ref_known(v___x_4568_, 1);
v___x_4569_ = l_Lean_MVarId_admit(v_a_4556_, v___x_4526_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
v___y_4544_ = v___x_4569_;
goto v___jp_4543_;
}
else
{
lean_dec(v_a_4556_);
v___y_4544_ = v___x_4568_;
goto v___jp_4543_;
}
}
}
}
else
{
lean_dec(v_a_4556_);
v___y_4544_ = v___x_4557_;
goto v___jp_4543_;
}
}
}
}
else
{
lean_object* v_a_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4582_; 
lean_dec(v_a_4542_);
lean_dec_ref(v_alt_4530_);
v_a_4575_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4582_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4582_ == 0)
{
v___x_4577_ = v___x_4555_;
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_a_4575_);
lean_dec(v___x_4555_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4582_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4580_; 
if (v_isShared_4578_ == 0)
{
v___x_4580_ = v___x_4577_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4581_; 
v_reuseFailAlloc_4581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4581_, 0, v_a_4575_);
v___x_4580_ = v_reuseFailAlloc_4581_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
return v___x_4580_;
}
}
}
v___jp_4543_:
{
if (lean_obj_tag(v___y_4544_) == 0)
{
lean_object* v___x_4545_; 
lean_dec_ref_known(v___y_4544_, 1);
v___x_4545_ = l_Lean_Meta_mkEqMPR(v_a_4542_, v_alt_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
return v___x_4545_;
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
lean_dec(v_a_4542_);
lean_dec_ref(v_alt_4530_);
v_a_4546_ = lean_ctor_get(v___y_4544_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___y_4544_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___y_4544_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___y_4544_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4530_);
return v___x_4541_;
}
}
else
{
lean_dec_ref(v_alt_4530_);
return v___x_4538_;
}
}
else
{
lean_dec_ref(v_alt_4530_);
lean_dec_ref(v_expAltType_4528_);
return v___x_4536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4583_, lean_object* v___altIdx_4584_, lean_object* v_expAltType_4585_, lean_object* v___altFVars_4586_, lean_object* v_alt_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
uint8_t v___x_32524__boxed_4593_; lean_object* v_res_4594_; 
v___x_32524__boxed_4593_ = lean_unbox(v___x_4583_);
v_res_4594_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32524__boxed_4593_, v___altIdx_4584_, v_expAltType_4585_, v___altFVars_4586_, v_alt_4587_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
lean_dec(v___y_4591_);
lean_dec_ref(v___y_4590_);
lean_dec(v___y_4589_);
lean_dec_ref(v___y_4588_);
lean_dec_ref(v___altFVars_4586_);
lean_dec(v___altIdx_4584_);
return v_res_4594_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4595_, lean_object* v_e_4596_){
_start:
{
uint8_t v___x_4597_; lean_object* v_d_4599_; lean_object* v_b_4600_; 
v___x_4597_ = l_Lean_Expr_hasFVar(v_e_4596_);
if (v___x_4597_ == 0)
{
return v___x_4597_;
}
else
{
switch(lean_obj_tag(v_e_4596_))
{
case 7:
{
lean_object* v_binderType_4603_; lean_object* v_body_4604_; 
v_binderType_4603_ = lean_ctor_get(v_e_4596_, 1);
v_body_4604_ = lean_ctor_get(v_e_4596_, 2);
v_d_4599_ = v_binderType_4603_;
v_b_4600_ = v_body_4604_;
goto v___jp_4598_;
}
case 6:
{
lean_object* v_binderType_4605_; lean_object* v_body_4606_; 
v_binderType_4605_ = lean_ctor_get(v_e_4596_, 1);
v_body_4606_ = lean_ctor_get(v_e_4596_, 2);
v_d_4599_ = v_binderType_4605_;
v_b_4600_ = v_body_4606_;
goto v___jp_4598_;
}
case 10:
{
lean_object* v_expr_4607_; 
v_expr_4607_ = lean_ctor_get(v_e_4596_, 1);
v_e_4596_ = v_expr_4607_;
goto _start;
}
case 8:
{
lean_object* v_type_4609_; lean_object* v_value_4610_; lean_object* v_body_4611_; uint8_t v___x_4612_; 
v_type_4609_ = lean_ctor_get(v_e_4596_, 1);
v_value_4610_ = lean_ctor_get(v_e_4596_, 2);
v_body_4611_ = lean_ctor_get(v_e_4596_, 3);
v___x_4612_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4595_, v_type_4609_);
if (v___x_4612_ == 0)
{
uint8_t v___x_4613_; 
v___x_4613_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4595_, v_value_4610_);
if (v___x_4613_ == 0)
{
v_e_4596_ = v_body_4611_;
goto _start;
}
else
{
return v___x_4597_;
}
}
else
{
return v___x_4597_;
}
}
case 5:
{
lean_object* v_fn_4615_; lean_object* v_arg_4616_; uint8_t v___x_4617_; 
v_fn_4615_ = lean_ctor_get(v_e_4596_, 0);
v_arg_4616_ = lean_ctor_get(v_e_4596_, 1);
v___x_4617_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4595_, v_fn_4615_);
if (v___x_4617_ == 0)
{
v_e_4596_ = v_arg_4616_;
goto _start;
}
else
{
return v___x_4597_;
}
}
case 11:
{
lean_object* v_struct_4619_; 
v_struct_4619_ = lean_ctor_get(v_e_4596_, 2);
v_e_4596_ = v_struct_4619_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4621_; lean_object* v___x_4622_; uint8_t v___x_4623_; 
v_fvarId_4621_ = lean_ctor_get(v_e_4596_, 0);
v___x_4622_ = l_Lean_Expr_fvarId_x21(v___x_4595_);
v___x_4623_ = l_Lean_instBEqFVarId_beq(v_fvarId_4621_, v___x_4622_);
lean_dec(v___x_4622_);
return v___x_4623_;
}
default: 
{
uint8_t v___x_4624_; 
v___x_4624_ = 0;
return v___x_4624_;
}
}
}
v___jp_4598_:
{
uint8_t v___x_4601_; 
v___x_4601_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4595_, v_d_4599_);
if (v___x_4601_ == 0)
{
v_e_4596_ = v_b_4600_;
goto _start;
}
else
{
return v___x_4597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4625_, lean_object* v_e_4626_){
_start:
{
uint8_t v_res_4627_; lean_object* v_r_4628_; 
v_res_4627_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4625_, v_e_4626_);
lean_dec_ref(v_e_4626_);
lean_dec_ref(v___x_4625_);
v_r_4628_ = lean_box(v_res_4627_);
return v_r_4628_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4631_ = l_Lean_stringToMessageData(v___x_4630_);
return v___x_4631_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4634_ = l_Lean_stringToMessageData(v___x_4633_);
return v___x_4634_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4637_ = l_Lean_stringToMessageData(v___x_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4638_, lean_object* v_termAlt_4639_, lean_object* v_a_4640_, lean_object* v_b_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v_array_4647_; lean_object* v_start_4648_; lean_object* v_stop_4649_; lean_object* v___x_4651_; uint8_t v_isShared_4652_; uint8_t v_isSharedCheck_4677_; 
v_array_4647_ = lean_ctor_get(v_a_4640_, 0);
v_start_4648_ = lean_ctor_get(v_a_4640_, 1);
v_stop_4649_ = lean_ctor_get(v_a_4640_, 2);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_a_4640_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4651_ = v_a_4640_;
v_isShared_4652_ = v_isSharedCheck_4677_;
goto v_resetjp_4650_;
}
else
{
lean_inc(v_stop_4649_);
lean_inc(v_start_4648_);
lean_inc(v_array_4647_);
lean_dec(v_a_4640_);
v___x_4651_ = lean_box(0);
v_isShared_4652_ = v_isSharedCheck_4677_;
goto v_resetjp_4650_;
}
v_resetjp_4650_:
{
uint8_t v___x_4653_; 
v___x_4653_ = lean_nat_dec_lt(v_start_4648_, v_stop_4649_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; 
lean_del_object(v___x_4651_);
lean_dec(v_stop_4649_);
lean_dec(v_start_4648_);
lean_dec_ref(v_array_4647_);
lean_dec_ref(v_termAlt_4639_);
lean_dec_ref(v_a_4638_);
v___x_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4654_, 0, v_b_4641_);
return v___x_4654_;
}
else
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4659_; 
v___x_4655_ = lean_box(0);
v___x_4656_ = lean_unsigned_to_nat(1u);
v___x_4657_ = lean_nat_add(v_start_4648_, v___x_4656_);
lean_inc_ref(v_array_4647_);
if (v_isShared_4652_ == 0)
{
lean_ctor_set(v___x_4651_, 1, v___x_4657_);
v___x_4659_ = v___x_4651_;
goto v_reusejp_4658_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v_array_4647_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4676_, 2, v_stop_4649_);
v___x_4659_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4658_;
}
v_reusejp_4658_:
{
lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4660_ = lean_array_fget(v_array_4647_, v_start_4648_);
lean_dec(v_start_4648_);
lean_dec_ref(v_array_4647_);
v___x_4661_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4660_, v_a_4638_);
if (v___x_4661_ == 0)
{
lean_dec(v___x_4660_);
v_a_4640_ = v___x_4659_;
v_b_4641_ = v___x_4655_;
goto _start;
}
else
{
lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4663_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4638_);
v___x_4664_ = l_Lean_MessageData_ofExpr(v_a_4638_);
v___x_4665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4663_);
lean_ctor_set(v___x_4665_, 1, v___x_4664_);
v___x_4666_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4665_);
lean_ctor_set(v___x_4667_, 1, v___x_4666_);
lean_inc_ref(v_termAlt_4639_);
v___x_4668_ = l_Lean_MessageData_ofExpr(v_termAlt_4639_);
v___x_4669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4669_, 0, v___x_4667_);
lean_ctor_set(v___x_4669_, 1, v___x_4668_);
v___x_4670_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4669_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
v___x_4672_ = l_Lean_MessageData_ofExpr(v___x_4660_);
v___x_4673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4671_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
v___x_4674_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4673_, v___y_4642_, v___y_4643_, v___y_4644_, v___y_4645_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_dec_ref_known(v___x_4674_, 1);
v_a_4640_ = v___x_4659_;
v_b_4641_ = v___x_4655_;
goto _start;
}
else
{
lean_dec_ref(v___x_4659_);
lean_dec_ref(v_termAlt_4639_);
lean_dec_ref(v_a_4638_);
return v___x_4674_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4678_, lean_object* v_termAlt_4679_, lean_object* v_a_4680_, lean_object* v_b_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4678_, v_termAlt_4679_, v_a_4680_, v_b_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
return v_res_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4688_, lean_object* v_v_4689_, uint8_t v___x_4690_, uint8_t v___x_4691_, uint8_t v___x_4692_, lean_object* v_xs_4693_, lean_object* v_termAltBody_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4700_ = lean_array_get_size(v_xs_4693_);
v___x_4701_ = lean_nat_sub(v___x_4700_, v_nExtra_4688_);
v___x_4702_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4701_);
lean_inc_ref(v_xs_4693_);
v___x_4703_ = l_Array_toSubarray___redArg(v_xs_4693_, v___x_4702_, v___x_4701_);
v___x_4704_ = l_Array_toSubarray___redArg(v_xs_4693_, v___x_4701_, v___x_4700_);
lean_inc(v___y_4698_);
lean_inc_ref(v___y_4697_);
lean_inc(v___y_4696_);
lean_inc_ref(v___y_4695_);
v___x_4705_ = lean_infer_type(v_termAltBody_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4705_) == 0)
{
lean_object* v_a_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
lean_inc_n(v_a_4706_, 2);
lean_dec_ref_known(v___x_4705_, 1);
v___x_4707_ = lean_box(0);
v___x_4708_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4706_, v_v_4689_, v___x_4704_, v___x_4707_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
lean_dec_ref_known(v___x_4708_, 1);
v___x_4709_ = l_Subarray_copy___redArg(v___x_4703_);
v___x_4710_ = l_Lean_Meta_mkLambdaFVars(v___x_4709_, v_a_4706_, v___x_4690_, v___x_4691_, v___x_4690_, v___x_4691_, v___x_4692_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec_ref(v___x_4709_);
return v___x_4710_;
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_dec(v_a_4706_);
lean_dec_ref(v___x_4703_);
v_a_4711_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4708_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4708_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
else
{
lean_dec_ref(v___x_4704_);
lean_dec_ref(v___x_4703_);
lean_dec(v_v_4689_);
return v___x_4705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4719_, lean_object* v_v_4720_, lean_object* v___x_4721_, lean_object* v___x_4722_, lean_object* v___x_4723_, lean_object* v_xs_4724_, lean_object* v_termAltBody_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
uint8_t v___x_32813__boxed_4731_; uint8_t v___x_32814__boxed_4732_; uint8_t v___x_32815__boxed_4733_; lean_object* v_res_4734_; 
v___x_32813__boxed_4731_ = lean_unbox(v___x_4721_);
v___x_32814__boxed_4732_ = lean_unbox(v___x_4722_);
v___x_32815__boxed_4733_ = lean_unbox(v___x_4723_);
v_res_4734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4719_, v_v_4720_, v___x_32813__boxed_4731_, v___x_32814__boxed_4732_, v___x_32815__boxed_4733_, v_xs_4724_, v_termAltBody_4725_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
lean_dec(v___y_4729_);
lean_dec_ref(v___y_4728_);
lean_dec(v___y_4727_);
lean_dec_ref(v___y_4726_);
lean_dec(v_nExtra_4719_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4735_, size_t v_sz_4736_, size_t v_i_4737_, lean_object* v_bs_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
uint8_t v___x_4744_; 
v___x_4744_ = lean_usize_dec_lt(v_i_4737_, v_sz_4736_);
if (v___x_4744_ == 0)
{
lean_object* v___x_4745_; 
lean_dec(v_nExtra_4735_);
v___x_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4745_, 0, v_bs_4738_);
return v___x_4745_;
}
else
{
uint8_t v___x_4746_; uint8_t v___x_4747_; lean_object* v_v_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___f_4752_; lean_object* v___x_4753_; lean_object* v_bs_x27_4754_; lean_object* v___x_4755_; 
v___x_4746_ = 0;
v___x_4747_ = 1;
v_v_4748_ = lean_array_uget(v_bs_4738_, v_i_4737_);
v___x_4749_ = lean_box(v___x_4746_);
v___x_4750_ = lean_box(v___x_4744_);
v___x_4751_ = lean_box(v___x_4747_);
lean_inc(v_v_4748_);
lean_inc(v_nExtra_4735_);
v___f_4752_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4752_, 0, v_nExtra_4735_);
lean_closure_set(v___f_4752_, 1, v_v_4748_);
lean_closure_set(v___f_4752_, 2, v___x_4749_);
lean_closure_set(v___f_4752_, 3, v___x_4750_);
lean_closure_set(v___f_4752_, 4, v___x_4751_);
v___x_4753_ = lean_unsigned_to_nat(0u);
v_bs_x27_4754_ = lean_array_uset(v_bs_4738_, v_i_4737_, v___x_4753_);
v___x_4755_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4748_, v___f_4752_, v___x_4746_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v_a_4756_; size_t v___x_4757_; size_t v___x_4758_; lean_object* v___x_4759_; 
v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
lean_inc(v_a_4756_);
lean_dec_ref_known(v___x_4755_, 1);
v___x_4757_ = ((size_t)1ULL);
v___x_4758_ = lean_usize_add(v_i_4737_, v___x_4757_);
v___x_4759_ = lean_array_uset(v_bs_x27_4754_, v_i_4737_, v_a_4756_);
v_i_4737_ = v___x_4758_;
v_bs_4738_ = v___x_4759_;
goto _start;
}
else
{
lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v_bs_x27_4754_);
lean_dec(v_nExtra_4735_);
v_a_4761_ = lean_ctor_get(v___x_4755_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4755_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4755_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4755_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4769_, lean_object* v_sz_4770_, lean_object* v_i_4771_, lean_object* v_bs_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
size_t v_sz_boxed_4778_; size_t v_i_boxed_4779_; lean_object* v_res_4780_; 
v_sz_boxed_4778_ = lean_unbox_usize(v_sz_4770_);
lean_dec(v_sz_4770_);
v_i_boxed_4779_ = lean_unbox_usize(v_i_4771_);
lean_dec(v_i_4771_);
v_res_4780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4769_, v_sz_boxed_4778_, v_i_boxed_4779_, v_bs_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
return v_res_4780_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = lean_box(0);
v___x_4782_ = l_Lean_Expr_sort___override(v___x_4781_);
return v___x_4782_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4783_ = lean_box(0);
v___x_4784_ = l_Lean_Level_succ___override(v___x_4783_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4785_, uint8_t v___x_4786_, uint8_t v___x_4787_, lean_object* v_alts_4788_, lean_object* v_toMatcherInfo_4789_, lean_object* v_matcherName_4790_, lean_object* v_params_4791_, lean_object* v_matcherLevels_4792_, lean_object* v_motiveArgs_4793_, lean_object* v_body_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v___x_4800_; 
lean_inc(v_nExtra_4785_);
v___x_4800_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4785_, v_body_4794_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; lean_object* v___x_4804_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc(v_a_4801_);
lean_dec_ref_known(v___x_4800_, 1);
v___x_4802_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4803_ = 1;
v___x_4804_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4793_, v___x_4802_, v___x_4786_, v___x_4787_, v___x_4786_, v___x_4787_, v___x_4803_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4804_) == 0)
{
lean_object* v_a_4805_; size_t v_sz_4806_; size_t v___x_4807_; lean_object* v___x_4808_; 
v_a_4805_ = lean_ctor_get(v___x_4804_, 0);
lean_inc(v_a_4805_);
lean_dec_ref_known(v___x_4804_, 1);
v_sz_4806_ = lean_array_size(v_alts_4788_);
v___x_4807_ = ((size_t)0ULL);
v___x_4808_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4785_, v_sz_4806_, v___x_4807_, v_alts_4788_, v___y_4795_, v___y_4796_, v___y_4797_, v___y_4798_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; lean_object* v_matcherLevels_4811_; lean_object* v___y_4812_; lean_object* v___y_4813_; lean_object* v_uElimPos_x3f_4818_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4809_);
lean_dec_ref_known(v___x_4808_, 1);
v_uElimPos_x3f_4818_ = lean_ctor_get(v_toMatcherInfo_4789_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4818_) == 0)
{
v_matcherLevels_4811_ = v_matcherLevels_4792_;
v___y_4812_ = v___y_4797_;
v___y_4813_ = v___y_4798_;
goto v___jp_4810_;
}
else
{
lean_object* v_val_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v_val_4819_ = lean_ctor_get(v_uElimPos_x3f_4818_, 0);
v___x_4820_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4821_ = lean_array_set(v_matcherLevels_4792_, v_val_4819_, v___x_4820_);
v_matcherLevels_4811_ = v___x_4821_;
v___y_4812_ = v___y_4797_;
v___y_4813_ = v___y_4798_;
goto v___jp_4810_;
}
v___jp_4810_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4814_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4815_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4815_, 0, v_toMatcherInfo_4789_);
lean_ctor_set(v___x_4815_, 1, v_matcherName_4790_);
lean_ctor_set(v___x_4815_, 2, v_matcherLevels_4811_);
lean_ctor_set(v___x_4815_, 3, v_params_4791_);
lean_ctor_set(v___x_4815_, 4, v_a_4805_);
lean_ctor_set(v___x_4815_, 5, v_motiveArgs_4793_);
lean_ctor_set(v___x_4815_, 6, v_a_4809_);
lean_ctor_set(v___x_4815_, 7, v___x_4814_);
v___x_4816_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4815_);
v___x_4817_ = l_Lean_mkArrowN(v_a_4801_, v___x_4816_, v___y_4812_, v___y_4813_);
lean_dec(v_a_4801_);
return v___x_4817_;
}
}
else
{
lean_object* v_a_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_4829_; 
lean_dec(v_a_4805_);
lean_dec(v_a_4801_);
lean_dec_ref(v_motiveArgs_4793_);
lean_dec_ref(v_matcherLevels_4792_);
lean_dec_ref(v_params_4791_);
lean_dec(v_matcherName_4790_);
lean_dec_ref(v_toMatcherInfo_4789_);
v_a_4822_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4829_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4829_ == 0)
{
v___x_4824_ = v___x_4808_;
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_a_4822_);
lean_dec(v___x_4808_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_4829_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4827_; 
if (v_isShared_4825_ == 0)
{
v___x_4827_ = v___x_4824_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4828_; 
v_reuseFailAlloc_4828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4828_, 0, v_a_4822_);
v___x_4827_ = v_reuseFailAlloc_4828_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
return v___x_4827_;
}
}
}
}
else
{
lean_dec(v_a_4801_);
lean_dec_ref(v_motiveArgs_4793_);
lean_dec_ref(v_matcherLevels_4792_);
lean_dec_ref(v_params_4791_);
lean_dec(v_matcherName_4790_);
lean_dec_ref(v_toMatcherInfo_4789_);
lean_dec_ref(v_alts_4788_);
lean_dec(v_nExtra_4785_);
return v___x_4804_;
}
}
else
{
lean_object* v_a_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4837_; 
lean_dec_ref(v_motiveArgs_4793_);
lean_dec_ref(v_matcherLevels_4792_);
lean_dec_ref(v_params_4791_);
lean_dec(v_matcherName_4790_);
lean_dec_ref(v_toMatcherInfo_4789_);
lean_dec_ref(v_alts_4788_);
lean_dec(v_nExtra_4785_);
v_a_4830_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4837_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4837_ == 0)
{
v___x_4832_ = v___x_4800_;
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_a_4830_);
lean_dec(v___x_4800_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4837_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4835_; 
if (v_isShared_4833_ == 0)
{
v___x_4835_ = v___x_4832_;
goto v_reusejp_4834_;
}
else
{
lean_object* v_reuseFailAlloc_4836_; 
v_reuseFailAlloc_4836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4836_, 0, v_a_4830_);
v___x_4835_ = v_reuseFailAlloc_4836_;
goto v_reusejp_4834_;
}
v_reusejp_4834_:
{
return v___x_4835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4838_, lean_object* v___x_4839_, lean_object* v___x_4840_, lean_object* v_alts_4841_, lean_object* v_toMatcherInfo_4842_, lean_object* v_matcherName_4843_, lean_object* v_params_4844_, lean_object* v_matcherLevels_4845_, lean_object* v_motiveArgs_4846_, lean_object* v_body_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
uint8_t v___x_32948__boxed_4853_; uint8_t v___x_32949__boxed_4854_; lean_object* v_res_4855_; 
v___x_32948__boxed_4853_ = lean_unbox(v___x_4839_);
v___x_32949__boxed_4854_ = lean_unbox(v___x_4840_);
v_res_4855_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4838_, v___x_32948__boxed_4853_, v___x_32949__boxed_4854_, v_alts_4841_, v_toMatcherInfo_4842_, v_matcherName_4843_, v_params_4844_, v_matcherLevels_4845_, v_motiveArgs_4846_, v_body_4847_, v___y_4848_, v___y_4849_, v___y_4850_, v___y_4851_);
lean_dec(v___y_4851_);
lean_dec_ref(v___y_4850_);
lean_dec(v___y_4849_);
lean_dec_ref(v___y_4848_);
return v_res_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4856_, lean_object* v_ys_4857_, lean_object* v_args_4858_, lean_object* v___mask_4859_, lean_object* v___bodyType_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v___x_4866_; 
lean_inc(v___y_4864_);
lean_inc_ref(v___y_4863_);
lean_inc(v___y_4862_);
lean_inc_ref(v___y_4861_);
v___x_4866_ = lean_apply_7(v_k_4856_, v_ys_4857_, v_args_4858_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, lean_box(0));
return v___x_4866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4867_, lean_object* v_ys_4868_, lean_object* v_args_4869_, lean_object* v___mask_4870_, lean_object* v___bodyType_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4867_, v_ys_4868_, v_args_4869_, v___mask_4870_, v___bodyType_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec_ref(v___bodyType_4871_);
lean_dec_ref(v___mask_4870_);
return v_res_4877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4878_, lean_object* v_altInfo_4879_, lean_object* v_k_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_){
_start:
{
lean_object* v___f_4886_; lean_object* v___x_4887_; 
v___f_4886_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4886_, 0, v_k_4880_);
v___x_4887_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4878_, v_altInfo_4879_, v___f_4886_, v___y_4881_, v___y_4882_, v___y_4883_, v___y_4884_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
else
{
lean_object* v_a_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v_a_4896_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4898_ = v___x_4887_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_a_4896_);
lean_dec(v___x_4887_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4904_, lean_object* v_altInfo_4905_, lean_object* v_k_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_){
_start:
{
lean_object* v_res_4912_; 
v_res_4912_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4904_, v_altInfo_4905_, v_k_4906_, v___y_4907_, v___y_4908_, v___y_4909_, v___y_4910_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
lean_dec(v___y_4908_);
lean_dec_ref(v___y_4907_);
return v_res_4912_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4913_, lean_object* v___x_4914_, lean_object* v___f_4915_, lean_object* v_fst_4916_, lean_object* v___x_4917_, lean_object* v___x_4918_, lean_object* v___x_4919_, lean_object* v___x_4920_, lean_object* v___x_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4913_, v___x_4914_, v___f_4915_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v_a_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4942_; 
v_a_4928_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4930_ = v___x_4927_;
v_isShared_4931_ = v_isSharedCheck_4942_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_a_4928_);
lean_dec(v___x_4927_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4942_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4940_; 
v___x_4932_ = lean_array_push(v_fst_4916_, v_a_4928_);
v___x_4933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4917_);
lean_ctor_set(v___x_4933_, 1, v___x_4918_);
v___x_4934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4919_);
lean_ctor_set(v___x_4934_, 1, v___x_4933_);
v___x_4935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4920_);
lean_ctor_set(v___x_4935_, 1, v___x_4934_);
v___x_4936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4921_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4937_, 0, v___x_4932_);
lean_ctor_set(v___x_4937_, 1, v___x_4936_);
v___x_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v___x_4938_);
v___x_4940_ = v___x_4930_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
else
{
lean_object* v_a_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4950_; 
lean_dec_ref(v___x_4921_);
lean_dec_ref(v___x_4920_);
lean_dec_ref(v___x_4919_);
lean_dec_ref(v___x_4918_);
lean_dec_ref(v___x_4917_);
lean_dec(v_fst_4916_);
v_a_4943_ = lean_ctor_get(v___x_4927_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4945_ = v___x_4927_;
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_a_4943_);
lean_dec(v___x_4927_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4948_; 
if (v_isShared_4946_ == 0)
{
v___x_4948_ = v___x_4945_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4943_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4951_, lean_object* v___x_4952_, lean_object* v___f_4953_, lean_object* v_fst_4954_, lean_object* v___x_4955_, lean_object* v___x_4956_, lean_object* v___x_4957_, lean_object* v___x_4958_, lean_object* v___x_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
lean_object* v_res_4965_; 
v_res_4965_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4951_, v___x_4952_, v___f_4953_, v_fst_4954_, v___x_4955_, v___x_4956_, v___x_4957_, v___x_4958_, v___x_4959_, v___y_4960_, v___y_4961_, v___y_4962_, v___y_4963_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
lean_dec(v___y_4961_);
lean_dec_ref(v___y_4960_);
return v_res_4965_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_4966_, lean_object* v_ys_4967_, lean_object* v_ys2_4968_, lean_object* v_ys3_4969_, lean_object* v_onAlt_4970_, lean_object* v_a_4971_, uint8_t v___x_4972_, uint8_t v_useSplitter_4973_, lean_object* v___x_4974_, lean_object* v_ys4_4975_, lean_object* v_altType_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v___y_4983_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
lean_inc_ref(v_args_4966_);
v___x_4993_ = l_Array_append___redArg(v_args_4966_, v_ys3_4969_);
v___x_4994_ = l_Lean_Meta_instantiateLambda(v___x_4974_, v___x_4993_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
lean_dec_ref(v___x_4993_);
if (lean_obj_tag(v___x_4994_) == 0)
{
v___y_4983_ = v___x_4994_;
goto v___jp_4982_;
}
else
{
lean_object* v_a_4995_; uint8_t v___y_4997_; uint8_t v___x_5000_; 
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
v___x_5000_ = l_Lean_Exception_isInterrupt(v_a_4995_);
if (v___x_5000_ == 0)
{
uint8_t v___x_5001_; 
v___x_5001_ = l_Lean_Exception_isRuntime(v_a_4995_);
v___y_4997_ = v___x_5001_;
goto v___jp_4996_;
}
else
{
lean_dec(v_a_4995_);
v___y_4997_ = v___x_5000_;
goto v___jp_4996_;
}
v___jp_4996_:
{
if (v___y_4997_ == 0)
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec_ref_known(v___x_4994_, 1);
v___x_4998_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3);
v___x_4999_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4998_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
v___y_4983_ = v___x_4999_;
goto v___jp_4982_;
}
else
{
v___y_4983_ = v___x_4994_;
goto v___jp_4982_;
}
}
}
v___jp_4982_:
{
if (lean_obj_tag(v___y_4983_) == 0)
{
lean_object* v_a_4984_; lean_object* v___x_4985_; lean_object* v___x_4986_; 
v_a_4984_ = lean_ctor_get(v___y_4983_, 0);
lean_inc(v_a_4984_);
lean_dec_ref_known(v___y_4983_, 1);
lean_inc_ref(v_ys4_4975_);
lean_inc_ref(v_ys3_4969_);
lean_inc_ref(v_ys2_4968_);
lean_inc_ref(v_ys_4967_);
v___x_4985_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4985_, 0, v_args_4966_);
lean_ctor_set(v___x_4985_, 1, v_ys_4967_);
lean_ctor_set(v___x_4985_, 2, v_ys2_4968_);
lean_ctor_set(v___x_4985_, 3, v_ys3_4969_);
lean_ctor_set(v___x_4985_, 4, v_ys4_4975_);
lean_inc(v___y_4980_);
lean_inc_ref(v___y_4979_);
lean_inc(v___y_4978_);
lean_inc_ref(v___y_4977_);
v___x_4986_ = lean_apply_9(v_onAlt_4970_, v_a_4971_, v_altType_4976_, v___x_4985_, v_a_4984_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, lean_box(0));
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; uint8_t v___x_4991_; lean_object* v___x_4992_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc(v_a_4987_);
lean_dec_ref_known(v___x_4986_, 1);
v___x_4988_ = l_Array_append___redArg(v_ys_4967_, v_ys2_4968_);
lean_dec_ref(v_ys2_4968_);
v___x_4989_ = l_Array_append___redArg(v___x_4988_, v_ys3_4969_);
lean_dec_ref(v_ys3_4969_);
v___x_4990_ = l_Array_append___redArg(v___x_4989_, v_ys4_4975_);
lean_dec_ref(v_ys4_4975_);
v___x_4991_ = 1;
v___x_4992_ = l_Lean_Meta_mkLambdaFVars(v___x_4990_, v_a_4987_, v___x_4972_, v_useSplitter_4973_, v___x_4972_, v_useSplitter_4973_, v___x_4991_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
lean_dec_ref(v___x_4990_);
return v___x_4992_;
}
else
{
lean_dec_ref(v_ys4_4975_);
lean_dec_ref(v_ys3_4969_);
lean_dec_ref(v_ys2_4968_);
lean_dec_ref(v_ys_4967_);
return v___x_4986_;
}
}
else
{
lean_dec_ref(v_altType_4976_);
lean_dec_ref(v_ys4_4975_);
lean_dec(v_a_4971_);
lean_dec_ref(v_onAlt_4970_);
lean_dec_ref(v_ys3_4969_);
lean_dec_ref(v_ys2_4968_);
lean_dec_ref(v_ys_4967_);
lean_dec_ref(v_args_4966_);
return v___y_4983_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5002_, lean_object* v_ys_5003_, lean_object* v_ys2_5004_, lean_object* v_ys3_5005_, lean_object* v_onAlt_5006_, lean_object* v_a_5007_, lean_object* v___x_5008_, lean_object* v_useSplitter_5009_, lean_object* v___x_5010_, lean_object* v_ys4_5011_, lean_object* v_altType_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_){
_start:
{
uint8_t v___x_33202__boxed_5018_; uint8_t v_useSplitter_boxed_5019_; lean_object* v_res_5020_; 
v___x_33202__boxed_5018_ = lean_unbox(v___x_5008_);
v_useSplitter_boxed_5019_ = lean_unbox(v_useSplitter_5009_);
v_res_5020_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5002_, v_ys_5003_, v_ys2_5004_, v_ys3_5005_, v_onAlt_5006_, v_a_5007_, v___x_33202__boxed_5018_, v_useSplitter_boxed_5019_, v___x_5010_, v_ys4_5011_, v_altType_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
lean_dec(v___y_5016_);
lean_dec_ref(v___y_5015_);
lean_dec(v___y_5014_);
lean_dec_ref(v___y_5013_);
return v_res_5020_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5021_, lean_object* v_ys_5022_, lean_object* v_ys2_5023_, lean_object* v_onAlt_5024_, lean_object* v_a_5025_, uint8_t v___x_5026_, uint8_t v_useSplitter_5027_, lean_object* v___x_5028_, lean_object* v_extraEqualities_5029_, lean_object* v_ys3_5030_, lean_object* v_altType_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___f_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5037_ = lean_box(v___x_5026_);
v___x_5038_ = lean_box(v_useSplitter_5027_);
v___f_5039_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5039_, 0, v_args_5021_);
lean_closure_set(v___f_5039_, 1, v_ys_5022_);
lean_closure_set(v___f_5039_, 2, v_ys2_5023_);
lean_closure_set(v___f_5039_, 3, v_ys3_5030_);
lean_closure_set(v___f_5039_, 4, v_onAlt_5024_);
lean_closure_set(v___f_5039_, 5, v_a_5025_);
lean_closure_set(v___f_5039_, 6, v___x_5037_);
lean_closure_set(v___f_5039_, 7, v___x_5038_);
lean_closure_set(v___f_5039_, 8, v___x_5028_);
v___x_5040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5040_, 0, v_extraEqualities_5029_);
v___x_5041_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5031_, v___x_5040_, v___f_5039_, v___x_5026_, v___x_5026_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5042_, lean_object* v_ys_5043_, lean_object* v_ys2_5044_, lean_object* v_onAlt_5045_, lean_object* v_a_5046_, lean_object* v___x_5047_, lean_object* v_useSplitter_5048_, lean_object* v___x_5049_, lean_object* v_extraEqualities_5050_, lean_object* v_ys3_5051_, lean_object* v_altType_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_){
_start:
{
uint8_t v___x_33267__boxed_5058_; uint8_t v_useSplitter_boxed_5059_; lean_object* v_res_5060_; 
v___x_33267__boxed_5058_ = lean_unbox(v___x_5047_);
v_useSplitter_boxed_5059_ = lean_unbox(v_useSplitter_5048_);
v_res_5060_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5042_, v_ys_5043_, v_ys2_5044_, v_onAlt_5045_, v_a_5046_, v___x_33267__boxed_5058_, v_useSplitter_boxed_5059_, v___x_5049_, v_extraEqualities_5050_, v_ys3_5051_, v_altType_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
return v_res_5060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5061_, lean_object* v_ys_5062_, lean_object* v_onAlt_5063_, lean_object* v_a_5064_, uint8_t v___x_5065_, uint8_t v_useSplitter_5066_, lean_object* v___x_5067_, lean_object* v_extraEqualities_5068_, lean_object* v_numDiscrEqs_5069_, lean_object* v_ys2_5070_, lean_object* v_altType_5071_, lean_object* v___y_5072_, lean_object* v___y_5073_, lean_object* v___y_5074_, lean_object* v___y_5075_){
_start:
{
lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___f_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5077_ = lean_box(v___x_5065_);
v___x_5078_ = lean_box(v_useSplitter_5066_);
v___f_5079_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5079_, 0, v_args_5061_);
lean_closure_set(v___f_5079_, 1, v_ys_5062_);
lean_closure_set(v___f_5079_, 2, v_ys2_5070_);
lean_closure_set(v___f_5079_, 3, v_onAlt_5063_);
lean_closure_set(v___f_5079_, 4, v_a_5064_);
lean_closure_set(v___f_5079_, 5, v___x_5077_);
lean_closure_set(v___f_5079_, 6, v___x_5078_);
lean_closure_set(v___f_5079_, 7, v___x_5067_);
lean_closure_set(v___f_5079_, 8, v_extraEqualities_5068_);
v___x_5080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5080_, 0, v_numDiscrEqs_5069_);
v___x_5081_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5071_, v___x_5080_, v___f_5079_, v___x_5065_, v___x_5065_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5082_, lean_object* v_ys_5083_, lean_object* v_onAlt_5084_, lean_object* v_a_5085_, lean_object* v___x_5086_, lean_object* v_useSplitter_5087_, lean_object* v___x_5088_, lean_object* v_extraEqualities_5089_, lean_object* v_numDiscrEqs_5090_, lean_object* v_ys2_5091_, lean_object* v_altType_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_){
_start:
{
uint8_t v___x_33298__boxed_5098_; uint8_t v_useSplitter_boxed_5099_; lean_object* v_res_5100_; 
v___x_33298__boxed_5098_ = lean_unbox(v___x_5086_);
v_useSplitter_boxed_5099_ = lean_unbox(v_useSplitter_5087_);
v_res_5100_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5082_, v_ys_5083_, v_onAlt_5084_, v_a_5085_, v___x_33298__boxed_5098_, v_useSplitter_boxed_5099_, v___x_5088_, v_extraEqualities_5089_, v_numDiscrEqs_5090_, v_ys2_5091_, v_altType_5092_, v___y_5093_, v___y_5094_, v___y_5095_, v___y_5096_);
lean_dec(v___y_5096_);
lean_dec_ref(v___y_5095_);
lean_dec(v___y_5094_);
lean_dec_ref(v___y_5093_);
return v_res_5100_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0(void){
_start:
{
lean_object* v___x_5101_; 
v___x_5101_ = l_instMonadEIO___redArg();
return v___x_5101_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_){
_start:
{
lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v_toApplicative_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5175_; 
v___x_5112_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5113_ = l_StateRefT_x27_instMonad___redArg(v___x_5112_);
v_toApplicative_5114_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5175_ == 0)
{
lean_object* v_unused_5176_; 
v_unused_5176_ = lean_ctor_get(v___x_5113_, 1);
lean_dec(v_unused_5176_);
v___x_5116_ = v___x_5113_;
v_isShared_5117_ = v_isSharedCheck_5175_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_toApplicative_5114_);
lean_dec(v___x_5113_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5175_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
lean_object* v_toFunctor_5118_; lean_object* v_toSeq_5119_; lean_object* v_toSeqLeft_5120_; lean_object* v_toSeqRight_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5173_; 
v_toFunctor_5118_ = lean_ctor_get(v_toApplicative_5114_, 0);
v_toSeq_5119_ = lean_ctor_get(v_toApplicative_5114_, 2);
v_toSeqLeft_5120_ = lean_ctor_get(v_toApplicative_5114_, 3);
v_toSeqRight_5121_ = lean_ctor_get(v_toApplicative_5114_, 4);
v_isSharedCheck_5173_ = !lean_is_exclusive(v_toApplicative_5114_);
if (v_isSharedCheck_5173_ == 0)
{
lean_object* v_unused_5174_; 
v_unused_5174_ = lean_ctor_get(v_toApplicative_5114_, 1);
lean_dec(v_unused_5174_);
v___x_5123_ = v_toApplicative_5114_;
v_isShared_5124_ = v_isSharedCheck_5173_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_toSeqRight_5121_);
lean_inc(v_toSeqLeft_5120_);
lean_inc(v_toSeq_5119_);
lean_inc(v_toFunctor_5118_);
lean_dec(v_toApplicative_5114_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5173_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___f_5125_; lean_object* v___f_5126_; lean_object* v___f_5127_; lean_object* v___f_5128_; lean_object* v___x_5129_; lean_object* v___f_5130_; lean_object* v___f_5131_; lean_object* v___f_5132_; lean_object* v___x_5134_; 
v___f_5125_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5126_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5118_);
v___f_5127_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5127_, 0, v_toFunctor_5118_);
v___f_5128_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5128_, 0, v_toFunctor_5118_);
v___x_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5129_, 0, v___f_5127_);
lean_ctor_set(v___x_5129_, 1, v___f_5128_);
v___f_5130_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5130_, 0, v_toSeqRight_5121_);
v___f_5131_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5131_, 0, v_toSeqLeft_5120_);
v___f_5132_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5132_, 0, v_toSeq_5119_);
if (v_isShared_5124_ == 0)
{
lean_ctor_set(v___x_5123_, 4, v___f_5130_);
lean_ctor_set(v___x_5123_, 3, v___f_5131_);
lean_ctor_set(v___x_5123_, 2, v___f_5132_);
lean_ctor_set(v___x_5123_, 1, v___f_5125_);
lean_ctor_set(v___x_5123_, 0, v___x_5129_);
v___x_5134_ = v___x_5123_;
goto v_reusejp_5133_;
}
else
{
lean_object* v_reuseFailAlloc_5172_; 
v_reuseFailAlloc_5172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5129_);
lean_ctor_set(v_reuseFailAlloc_5172_, 1, v___f_5125_);
lean_ctor_set(v_reuseFailAlloc_5172_, 2, v___f_5132_);
lean_ctor_set(v_reuseFailAlloc_5172_, 3, v___f_5131_);
lean_ctor_set(v_reuseFailAlloc_5172_, 4, v___f_5130_);
v___x_5134_ = v_reuseFailAlloc_5172_;
goto v_reusejp_5133_;
}
v_reusejp_5133_:
{
lean_object* v___x_5136_; 
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 1, v___f_5126_);
lean_ctor_set(v___x_5116_, 0, v___x_5134_);
v___x_5136_ = v___x_5116_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5134_);
lean_ctor_set(v_reuseFailAlloc_5171_, 1, v___f_5126_);
v___x_5136_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
lean_object* v___x_5137_; lean_object* v_toApplicative_5138_; lean_object* v___x_5140_; uint8_t v_isShared_5141_; uint8_t v_isSharedCheck_5169_; 
v___x_5137_ = l_StateRefT_x27_instMonad___redArg(v___x_5136_);
v_toApplicative_5138_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5169_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5169_ == 0)
{
lean_object* v_unused_5170_; 
v_unused_5170_ = lean_ctor_get(v___x_5137_, 1);
lean_dec(v_unused_5170_);
v___x_5140_ = v___x_5137_;
v_isShared_5141_ = v_isSharedCheck_5169_;
goto v_resetjp_5139_;
}
else
{
lean_inc(v_toApplicative_5138_);
lean_dec(v___x_5137_);
v___x_5140_ = lean_box(0);
v_isShared_5141_ = v_isSharedCheck_5169_;
goto v_resetjp_5139_;
}
v_resetjp_5139_:
{
lean_object* v_toFunctor_5142_; lean_object* v_toSeq_5143_; lean_object* v_toSeqLeft_5144_; lean_object* v_toSeqRight_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5167_; 
v_toFunctor_5142_ = lean_ctor_get(v_toApplicative_5138_, 0);
v_toSeq_5143_ = lean_ctor_get(v_toApplicative_5138_, 2);
v_toSeqLeft_5144_ = lean_ctor_get(v_toApplicative_5138_, 3);
v_toSeqRight_5145_ = lean_ctor_get(v_toApplicative_5138_, 4);
v_isSharedCheck_5167_ = !lean_is_exclusive(v_toApplicative_5138_);
if (v_isSharedCheck_5167_ == 0)
{
lean_object* v_unused_5168_; 
v_unused_5168_ = lean_ctor_get(v_toApplicative_5138_, 1);
lean_dec(v_unused_5168_);
v___x_5147_ = v_toApplicative_5138_;
v_isShared_5148_ = v_isSharedCheck_5167_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_toSeqRight_5145_);
lean_inc(v_toSeqLeft_5144_);
lean_inc(v_toSeq_5143_);
lean_inc(v_toFunctor_5142_);
lean_dec(v_toApplicative_5138_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5167_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___f_5149_; lean_object* v___f_5150_; lean_object* v___f_5151_; lean_object* v___f_5152_; lean_object* v___x_5153_; lean_object* v___f_5154_; lean_object* v___f_5155_; lean_object* v___f_5156_; lean_object* v___x_5158_; 
v___f_5149_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5150_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5142_);
v___f_5151_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5151_, 0, v_toFunctor_5142_);
v___f_5152_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5152_, 0, v_toFunctor_5142_);
v___x_5153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5153_, 0, v___f_5151_);
lean_ctor_set(v___x_5153_, 1, v___f_5152_);
v___f_5154_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5154_, 0, v_toSeqRight_5145_);
v___f_5155_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5155_, 0, v_toSeqLeft_5144_);
v___f_5156_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5156_, 0, v_toSeq_5143_);
if (v_isShared_5148_ == 0)
{
lean_ctor_set(v___x_5147_, 4, v___f_5154_);
lean_ctor_set(v___x_5147_, 3, v___f_5155_);
lean_ctor_set(v___x_5147_, 2, v___f_5156_);
lean_ctor_set(v___x_5147_, 1, v___f_5149_);
lean_ctor_set(v___x_5147_, 0, v___x_5153_);
v___x_5158_ = v___x_5147_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v___x_5153_);
lean_ctor_set(v_reuseFailAlloc_5166_, 1, v___f_5149_);
lean_ctor_set(v_reuseFailAlloc_5166_, 2, v___f_5156_);
lean_ctor_set(v_reuseFailAlloc_5166_, 3, v___f_5155_);
lean_ctor_set(v_reuseFailAlloc_5166_, 4, v___f_5154_);
v___x_5158_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
lean_object* v___x_5160_; 
if (v_isShared_5141_ == 0)
{
lean_ctor_set(v___x_5140_, 1, v___f_5150_);
lean_ctor_set(v___x_5140_, 0, v___x_5158_);
v___x_5160_ = v___x_5140_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v___x_5158_);
lean_ctor_set(v_reuseFailAlloc_5165_, 1, v___f_5150_);
v___x_5160_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_27317__overap_5163_; lean_object* v___x_5164_; 
v___x_5161_ = l_Lean_instInhabitedExpr;
v___x_5162_ = l_instInhabitedOfMonad___redArg(v___x_5160_, v___x_5161_);
v___x_27317__overap_5163_ = lean_panic_fn_borrowed(v___x_5162_, v_msg_5106_);
lean_dec(v___x_5162_);
lean_inc(v___y_5110_);
lean_inc_ref(v___y_5109_);
lean_inc(v___y_5108_);
lean_inc_ref(v___y_5107_);
v___x_5164_ = lean_apply_5(v___x_27317__overap_5163_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, lean_box(0));
return v___x_5164_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_){
_start:
{
lean_object* v_res_5183_; 
v_res_5183_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5177_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
lean_dec(v___y_5181_);
lean_dec_ref(v___y_5180_);
lean_dec(v___y_5179_);
lean_dec_ref(v___y_5178_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5184_, lean_object* v_onAlt_5185_, lean_object* v_a_5186_, uint8_t v___x_5187_, uint8_t v_useSplitter_5188_, lean_object* v___x_5189_, lean_object* v_extraEqualities_5190_, lean_object* v_numDiscrEqs_5191_, lean_object* v___x_5192_, lean_object* v___x_5193_, lean_object* v___x_5194_, lean_object* v_ys_5195_, lean_object* v_args_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v_numFields_5202_; lean_object* v_numOverlaps_5203_; uint8_t v_hasUnitThunk_5204_; lean_object* v___x_5205_; uint8_t v___x_5206_; 
v_numFields_5202_ = lean_ctor_get(v___x_5184_, 0);
v_numOverlaps_5203_ = lean_ctor_get(v___x_5184_, 1);
v_hasUnitThunk_5204_ = lean_ctor_get_uint8(v___x_5184_, sizeof(void*)*2);
v___x_5205_ = lean_array_get_size(v_ys_5195_);
v___x_5206_ = lean_nat_dec_eq(v___x_5205_, v_numFields_5202_);
if (v___x_5206_ == 0)
{
lean_object* v___x_5207_; lean_object* v___x_5208_; 
lean_dec_ref(v_args_5196_);
lean_dec_ref(v_ys_5195_);
lean_dec_ref(v___x_5192_);
lean_dec(v_numDiscrEqs_5191_);
lean_dec(v_extraEqualities_5190_);
lean_dec_ref(v___x_5189_);
lean_dec(v_a_5186_);
lean_dec_ref(v_onAlt_5185_);
v___x_5207_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5208_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v___x_5207_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
return v___x_5208_;
}
else
{
lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___f_5211_; lean_object* v_altType_5213_; lean_object* v___y_5214_; lean_object* v___y_5215_; lean_object* v___y_5216_; lean_object* v___y_5217_; lean_object* v___x_5227_; 
v___x_5209_ = lean_box(v___x_5187_);
v___x_5210_ = lean_box(v_useSplitter_5188_);
lean_inc_ref(v_ys_5195_);
v___f_5211_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5211_, 0, v_args_5196_);
lean_closure_set(v___f_5211_, 1, v_ys_5195_);
lean_closure_set(v___f_5211_, 2, v_onAlt_5185_);
lean_closure_set(v___f_5211_, 3, v_a_5186_);
lean_closure_set(v___f_5211_, 4, v___x_5209_);
lean_closure_set(v___f_5211_, 5, v___x_5210_);
lean_closure_set(v___f_5211_, 6, v___x_5189_);
lean_closure_set(v___f_5211_, 7, v_extraEqualities_5190_);
lean_closure_set(v___f_5211_, 8, v_numDiscrEqs_5191_);
v___x_5227_ = l_Lean_Meta_instantiateForall(v___x_5192_, v_ys_5195_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
lean_dec_ref(v_ys_5195_);
if (lean_obj_tag(v___x_5227_) == 0)
{
uint8_t v_hasUnitThunk_5228_; 
v_hasUnitThunk_5228_ = lean_ctor_get_uint8(v___x_5193_, sizeof(void*)*2);
if (v_hasUnitThunk_5228_ == 0)
{
lean_object* v_a_5229_; 
v_a_5229_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v___x_5227_, 1);
v_altType_5213_ = v_a_5229_;
v___y_5214_ = v___y_5197_;
v___y_5215_ = v___y_5198_;
v___y_5216_ = v___y_5199_;
v___y_5217_ = v___y_5200_;
goto v___jp_5212_;
}
else
{
lean_object* v_a_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
v_a_5230_ = lean_ctor_get(v___x_5227_, 0);
lean_inc(v_a_5230_);
lean_dec_ref_known(v___x_5227_, 1);
v___x_5231_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5232_ = lean_mk_empty_array_with_capacity(v___x_5194_);
v___x_5233_ = lean_array_push(v___x_5232_, v___x_5231_);
v___x_5234_ = l_Lean_Meta_instantiateForall(v_a_5230_, v___x_5233_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
lean_dec_ref(v___x_5233_);
if (lean_obj_tag(v___x_5234_) == 0)
{
lean_object* v_a_5235_; 
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref_known(v___x_5234_, 1);
v_altType_5213_ = v_a_5235_;
v___y_5214_ = v___y_5197_;
v___y_5215_ = v___y_5198_;
v___y_5216_ = v___y_5199_;
v___y_5217_ = v___y_5200_;
goto v___jp_5212_;
}
else
{
lean_dec_ref(v___f_5211_);
return v___x_5234_;
}
}
}
else
{
lean_dec_ref(v___f_5211_);
return v___x_5227_;
}
v___jp_5212_:
{
lean_object* v___x_5218_; lean_object* v___x_5219_; 
lean_inc(v_numOverlaps_5203_);
v___x_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5218_, 0, v_numOverlaps_5203_);
v___x_5219_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_5213_, v___x_5218_, v___f_5211_, v___x_5187_, v___x_5187_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
if (lean_obj_tag(v___x_5219_) == 0)
{
if (v_hasUnitThunk_5204_ == 0)
{
return v___x_5219_;
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5226_; 
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
lean_inc(v_a_5220_);
lean_dec_ref_known(v___x_5219_, 1);
v___x_5221_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5222_ = lean_unsigned_to_nat(2u);
v___x_5223_ = lean_mk_empty_array_with_capacity(v___x_5222_);
lean_dec_ref(v___x_5223_);
v___x_5224_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5225_ = lean_array_push(v___x_5224_, v_a_5220_);
v___x_5226_ = l_Lean_Meta_mkAppM(v___x_5221_, v___x_5225_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
return v___x_5226_;
}
}
else
{
return v___x_5219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5236_ = _args[0];
lean_object* v_onAlt_5237_ = _args[1];
lean_object* v_a_5238_ = _args[2];
lean_object* v___x_5239_ = _args[3];
lean_object* v_useSplitter_5240_ = _args[4];
lean_object* v___x_5241_ = _args[5];
lean_object* v_extraEqualities_5242_ = _args[6];
lean_object* v_numDiscrEqs_5243_ = _args[7];
lean_object* v___x_5244_ = _args[8];
lean_object* v___x_5245_ = _args[9];
lean_object* v___x_5246_ = _args[10];
lean_object* v_ys_5247_ = _args[11];
lean_object* v_args_5248_ = _args[12];
lean_object* v___y_5249_ = _args[13];
lean_object* v___y_5250_ = _args[14];
lean_object* v___y_5251_ = _args[15];
lean_object* v___y_5252_ = _args[16];
lean_object* v___y_5253_ = _args[17];
_start:
{
uint8_t v___x_33500__boxed_5254_; uint8_t v_useSplitter_boxed_5255_; lean_object* v_res_5256_; 
v___x_33500__boxed_5254_ = lean_unbox(v___x_5239_);
v_useSplitter_boxed_5255_ = lean_unbox(v_useSplitter_5240_);
v_res_5256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5236_, v_onAlt_5237_, v_a_5238_, v___x_33500__boxed_5254_, v_useSplitter_boxed_5255_, v___x_5241_, v_extraEqualities_5242_, v_numDiscrEqs_5243_, v___x_5244_, v___x_5245_, v___x_5246_, v_ys_5247_, v_args_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_);
lean_dec(v___y_5252_);
lean_dec_ref(v___y_5251_);
lean_dec(v___y_5250_);
lean_dec_ref(v___y_5249_);
lean_dec(v___x_5246_);
lean_dec_ref(v___x_5245_);
lean_dec_ref(v___x_5236_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_){
_start:
{
lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v_toApplicative_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5326_; 
v___x_5263_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__0);
v___x_5264_ = l_StateRefT_x27_instMonad___redArg(v___x_5263_);
v_toApplicative_5265_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5326_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5326_ == 0)
{
lean_object* v_unused_5327_; 
v_unused_5327_ = lean_ctor_get(v___x_5264_, 1);
lean_dec(v_unused_5327_);
v___x_5267_ = v___x_5264_;
v_isShared_5268_ = v_isSharedCheck_5326_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_toApplicative_5265_);
lean_dec(v___x_5264_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5326_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v_toFunctor_5269_; lean_object* v_toSeq_5270_; lean_object* v_toSeqLeft_5271_; lean_object* v_toSeqRight_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5324_; 
v_toFunctor_5269_ = lean_ctor_get(v_toApplicative_5265_, 0);
v_toSeq_5270_ = lean_ctor_get(v_toApplicative_5265_, 2);
v_toSeqLeft_5271_ = lean_ctor_get(v_toApplicative_5265_, 3);
v_toSeqRight_5272_ = lean_ctor_get(v_toApplicative_5265_, 4);
v_isSharedCheck_5324_ = !lean_is_exclusive(v_toApplicative_5265_);
if (v_isSharedCheck_5324_ == 0)
{
lean_object* v_unused_5325_; 
v_unused_5325_ = lean_ctor_get(v_toApplicative_5265_, 1);
lean_dec(v_unused_5325_);
v___x_5274_ = v_toApplicative_5265_;
v_isShared_5275_ = v_isSharedCheck_5324_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_toSeqRight_5272_);
lean_inc(v_toSeqLeft_5271_);
lean_inc(v_toSeq_5270_);
lean_inc(v_toFunctor_5269_);
lean_dec(v_toApplicative_5265_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5324_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___f_5276_; lean_object* v___f_5277_; lean_object* v___f_5278_; lean_object* v___f_5279_; lean_object* v___x_5280_; lean_object* v___f_5281_; lean_object* v___f_5282_; lean_object* v___f_5283_; lean_object* v___x_5285_; 
v___f_5276_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__1));
v___f_5277_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__2));
lean_inc_ref(v_toFunctor_5269_);
v___f_5278_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5278_, 0, v_toFunctor_5269_);
v___f_5279_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5279_, 0, v_toFunctor_5269_);
v___x_5280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5280_, 0, v___f_5278_);
lean_ctor_set(v___x_5280_, 1, v___f_5279_);
v___f_5281_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5281_, 0, v_toSeqRight_5272_);
v___f_5282_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5282_, 0, v_toSeqLeft_5271_);
v___f_5283_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5283_, 0, v_toSeq_5270_);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 4, v___f_5281_);
lean_ctor_set(v___x_5274_, 3, v___f_5282_);
lean_ctor_set(v___x_5274_, 2, v___f_5283_);
lean_ctor_set(v___x_5274_, 1, v___f_5276_);
lean_ctor_set(v___x_5274_, 0, v___x_5280_);
v___x_5285_ = v___x_5274_;
goto v_reusejp_5284_;
}
else
{
lean_object* v_reuseFailAlloc_5323_; 
v_reuseFailAlloc_5323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5323_, 0, v___x_5280_);
lean_ctor_set(v_reuseFailAlloc_5323_, 1, v___f_5276_);
lean_ctor_set(v_reuseFailAlloc_5323_, 2, v___f_5283_);
lean_ctor_set(v_reuseFailAlloc_5323_, 3, v___f_5282_);
lean_ctor_set(v_reuseFailAlloc_5323_, 4, v___f_5281_);
v___x_5285_ = v_reuseFailAlloc_5323_;
goto v_reusejp_5284_;
}
v_reusejp_5284_:
{
lean_object* v___x_5287_; 
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 1, v___f_5277_);
lean_ctor_set(v___x_5267_, 0, v___x_5285_);
v___x_5287_ = v___x_5267_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5285_);
lean_ctor_set(v_reuseFailAlloc_5322_, 1, v___f_5277_);
v___x_5287_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
lean_object* v___x_5288_; lean_object* v_toApplicative_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5320_; 
v___x_5288_ = l_StateRefT_x27_instMonad___redArg(v___x_5287_);
v_toApplicative_5289_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5320_ == 0)
{
lean_object* v_unused_5321_; 
v_unused_5321_ = lean_ctor_get(v___x_5288_, 1);
lean_dec(v_unused_5321_);
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5320_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_toApplicative_5289_);
lean_dec(v___x_5288_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5320_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v_toFunctor_5293_; lean_object* v_toSeq_5294_; lean_object* v_toSeqLeft_5295_; lean_object* v_toSeqRight_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5318_; 
v_toFunctor_5293_ = lean_ctor_get(v_toApplicative_5289_, 0);
v_toSeq_5294_ = lean_ctor_get(v_toApplicative_5289_, 2);
v_toSeqLeft_5295_ = lean_ctor_get(v_toApplicative_5289_, 3);
v_toSeqRight_5296_ = lean_ctor_get(v_toApplicative_5289_, 4);
v_isSharedCheck_5318_ = !lean_is_exclusive(v_toApplicative_5289_);
if (v_isSharedCheck_5318_ == 0)
{
lean_object* v_unused_5319_; 
v_unused_5319_ = lean_ctor_get(v_toApplicative_5289_, 1);
lean_dec(v_unused_5319_);
v___x_5298_ = v_toApplicative_5289_;
v_isShared_5299_ = v_isSharedCheck_5318_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_toSeqRight_5296_);
lean_inc(v_toSeqLeft_5295_);
lean_inc(v_toSeq_5294_);
lean_inc(v_toFunctor_5293_);
lean_dec(v_toApplicative_5289_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5318_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___f_5300_; lean_object* v___f_5301_; lean_object* v___f_5302_; lean_object* v___f_5303_; lean_object* v___x_5304_; lean_object* v___f_5305_; lean_object* v___f_5306_; lean_object* v___f_5307_; lean_object* v___x_5309_; 
v___f_5300_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__3));
v___f_5301_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___closed__4));
lean_inc_ref(v_toFunctor_5293_);
v___f_5302_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_5302_, 0, v_toFunctor_5293_);
v___f_5303_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5303_, 0, v_toFunctor_5293_);
v___x_5304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5304_, 0, v___f_5302_);
lean_ctor_set(v___x_5304_, 1, v___f_5303_);
v___f_5305_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5305_, 0, v_toSeqRight_5296_);
v___f_5306_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5306_, 0, v_toSeqLeft_5295_);
v___f_5307_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5307_, 0, v_toSeq_5294_);
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 4, v___f_5305_);
lean_ctor_set(v___x_5298_, 3, v___f_5306_);
lean_ctor_set(v___x_5298_, 2, v___f_5307_);
lean_ctor_set(v___x_5298_, 1, v___f_5300_);
lean_ctor_set(v___x_5298_, 0, v___x_5304_);
v___x_5309_ = v___x_5298_;
goto v_reusejp_5308_;
}
else
{
lean_object* v_reuseFailAlloc_5317_; 
v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5317_, 0, v___x_5304_);
lean_ctor_set(v_reuseFailAlloc_5317_, 1, v___f_5300_);
lean_ctor_set(v_reuseFailAlloc_5317_, 2, v___f_5307_);
lean_ctor_set(v_reuseFailAlloc_5317_, 3, v___f_5306_);
lean_ctor_set(v_reuseFailAlloc_5317_, 4, v___f_5305_);
v___x_5309_ = v_reuseFailAlloc_5317_;
goto v_reusejp_5308_;
}
v_reusejp_5308_:
{
lean_object* v___x_5311_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set(v___x_5291_, 1, v___f_5301_);
lean_ctor_set(v___x_5291_, 0, v___x_5309_);
v___x_5311_ = v___x_5291_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5316_; 
v_reuseFailAlloc_5316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5316_, 0, v___x_5309_);
lean_ctor_set(v_reuseFailAlloc_5316_, 1, v___f_5301_);
v___x_5311_ = v_reuseFailAlloc_5316_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_27337__overap_5314_; lean_object* v___x_5315_; 
v___x_5312_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___closed__7);
v___x_5313_ = l_instInhabitedOfMonad___redArg(v___x_5311_, v___x_5312_);
v___x_27337__overap_5314_ = lean_panic_fn_borrowed(v___x_5313_, v_msg_5257_);
lean_dec(v___x_5313_);
lean_inc(v___y_5261_);
lean_inc_ref(v___y_5260_);
lean_inc(v___y_5259_);
lean_inc_ref(v___y_5258_);
v___x_5315_ = lean_apply_5(v___x_27337__overap_5314_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, lean_box(0));
return v___x_5315_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
lean_object* v_res_5334_; 
v_res_5334_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
lean_dec(v___y_5330_);
lean_dec_ref(v___y_5329_);
return v_res_5334_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_){
_start:
{
lean_object* v___x_5341_; 
v___x_5341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5341_, 0, v___x_5335_);
return v___x_5341_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v_res_5348_; 
v_res_5348_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
return v_res_5348_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5349_, lean_object* v_onAlt_5350_, uint8_t v_useSplitter_5351_, lean_object* v_extraEqualities_5352_, lean_object* v_numDiscrEqs_5353_, lean_object* v_a_5354_, lean_object* v_b_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_){
_start:
{
lean_object* v___y_5362_; uint8_t v___x_5385_; 
v___x_5385_ = lean_nat_dec_lt(v_a_5354_, v_upperBound_5349_);
if (v___x_5385_ == 0)
{
lean_object* v___x_5386_; 
lean_dec(v_a_5354_);
lean_dec(v_numDiscrEqs_5353_);
lean_dec(v_extraEqualities_5352_);
lean_dec_ref(v_onAlt_5350_);
v___x_5386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5386_, 0, v_b_5355_);
return v___x_5386_;
}
else
{
lean_object* v_snd_5387_; lean_object* v_snd_5388_; lean_object* v_snd_5389_; lean_object* v_snd_5390_; lean_object* v_snd_5391_; lean_object* v_fst_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5596_; 
v_snd_5387_ = lean_ctor_get(v_b_5355_, 1);
lean_inc(v_snd_5387_);
v_snd_5388_ = lean_ctor_get(v_snd_5387_, 1);
lean_inc(v_snd_5388_);
v_snd_5389_ = lean_ctor_get(v_snd_5388_, 1);
lean_inc(v_snd_5389_);
v_snd_5390_ = lean_ctor_get(v_snd_5389_, 1);
lean_inc(v_snd_5390_);
v_snd_5391_ = lean_ctor_get(v_snd_5390_, 1);
lean_inc(v_snd_5391_);
v_fst_5392_ = lean_ctor_get(v_b_5355_, 0);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_b_5355_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; 
v_unused_5597_ = lean_ctor_get(v_b_5355_, 1);
lean_dec(v_unused_5597_);
v___x_5394_ = v_b_5355_;
v_isShared_5395_ = v_isSharedCheck_5596_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_fst_5392_);
lean_dec(v_b_5355_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5596_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v_fst_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5594_; 
v_fst_5396_ = lean_ctor_get(v_snd_5387_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v_snd_5387_);
if (v_isSharedCheck_5594_ == 0)
{
lean_object* v_unused_5595_; 
v_unused_5595_ = lean_ctor_get(v_snd_5387_, 1);
lean_dec(v_unused_5595_);
v___x_5398_ = v_snd_5387_;
v_isShared_5399_ = v_isSharedCheck_5594_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_fst_5396_);
lean_dec(v_snd_5387_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5594_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v_fst_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5592_; 
v_fst_5400_ = lean_ctor_get(v_snd_5388_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v_snd_5388_);
if (v_isSharedCheck_5592_ == 0)
{
lean_object* v_unused_5593_; 
v_unused_5593_ = lean_ctor_get(v_snd_5388_, 1);
lean_dec(v_unused_5593_);
v___x_5402_ = v_snd_5388_;
v_isShared_5403_ = v_isSharedCheck_5592_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_fst_5400_);
lean_dec(v_snd_5388_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5592_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v_fst_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5590_; 
v_fst_5404_ = lean_ctor_get(v_snd_5389_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v_snd_5389_);
if (v_isSharedCheck_5590_ == 0)
{
lean_object* v_unused_5591_; 
v_unused_5591_ = lean_ctor_get(v_snd_5389_, 1);
lean_dec(v_unused_5591_);
v___x_5406_ = v_snd_5389_;
v_isShared_5407_ = v_isSharedCheck_5590_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_fst_5404_);
lean_dec(v_snd_5389_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5590_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v_fst_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5588_; 
v_fst_5408_ = lean_ctor_get(v_snd_5390_, 0);
v_isSharedCheck_5588_ = !lean_is_exclusive(v_snd_5390_);
if (v_isSharedCheck_5588_ == 0)
{
lean_object* v_unused_5589_; 
v_unused_5589_ = lean_ctor_get(v_snd_5390_, 1);
lean_dec(v_unused_5589_);
v___x_5410_ = v_snd_5390_;
v_isShared_5411_ = v_isSharedCheck_5588_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_fst_5408_);
lean_dec(v_snd_5390_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5588_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v_array_5412_; lean_object* v_start_5413_; lean_object* v_stop_5414_; uint8_t v___x_5415_; 
v_array_5412_ = lean_ctor_get(v_snd_5391_, 0);
v_start_5413_ = lean_ctor_get(v_snd_5391_, 1);
v_stop_5414_ = lean_ctor_get(v_snd_5391_, 2);
v___x_5415_ = lean_nat_dec_lt(v_start_5413_, v_stop_5414_);
if (v___x_5415_ == 0)
{
lean_object* v___x_5417_; 
if (v_isShared_5411_ == 0)
{
v___x_5417_ = v___x_5410_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5432_; 
v_reuseFailAlloc_5432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5432_, 0, v_fst_5408_);
lean_ctor_set(v_reuseFailAlloc_5432_, 1, v_snd_5391_);
v___x_5417_ = v_reuseFailAlloc_5432_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
lean_object* v___x_5419_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5417_);
v___x_5419_ = v___x_5406_;
goto v_reusejp_5418_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5431_, 1, v___x_5417_);
v___x_5419_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5418_;
}
v_reusejp_5418_:
{
lean_object* v___x_5421_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 1, v___x_5419_);
v___x_5421_ = v___x_5402_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_fst_5400_);
lean_ctor_set(v_reuseFailAlloc_5430_, 1, v___x_5419_);
v___x_5421_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
lean_object* v___x_5423_; 
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5421_);
v___x_5423_ = v___x_5398_;
goto v_reusejp_5422_;
}
else
{
lean_object* v_reuseFailAlloc_5429_; 
v_reuseFailAlloc_5429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_fst_5396_);
lean_ctor_set(v_reuseFailAlloc_5429_, 1, v___x_5421_);
v___x_5423_ = v_reuseFailAlloc_5429_;
goto v_reusejp_5422_;
}
v_reusejp_5422_:
{
lean_object* v___x_5425_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5423_);
v___x_5425_ = v___x_5394_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5428_, 1, v___x_5423_);
v___x_5425_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
lean_object* v___x_5426_; lean_object* v___f_5427_; 
v___x_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5426_, 0, v___x_5425_);
v___f_5427_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5427_, 0, v___x_5426_);
v___y_5362_ = v___f_5427_;
goto v___jp_5361_;
}
}
}
}
}
}
else
{
lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5584_; 
lean_inc(v_stop_5414_);
lean_inc(v_start_5413_);
lean_inc_ref(v_array_5412_);
v_isSharedCheck_5584_ = !lean_is_exclusive(v_snd_5391_);
if (v_isSharedCheck_5584_ == 0)
{
lean_object* v_unused_5585_; lean_object* v_unused_5586_; lean_object* v_unused_5587_; 
v_unused_5585_ = lean_ctor_get(v_snd_5391_, 2);
lean_dec(v_unused_5585_);
v_unused_5586_ = lean_ctor_get(v_snd_5391_, 1);
lean_dec(v_unused_5586_);
v_unused_5587_ = lean_ctor_get(v_snd_5391_, 0);
lean_dec(v_unused_5587_);
v___x_5434_ = v_snd_5391_;
v_isShared_5435_ = v_isSharedCheck_5584_;
goto v_resetjp_5433_;
}
else
{
lean_dec(v_snd_5391_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5584_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v_array_5436_; lean_object* v_start_5437_; lean_object* v_stop_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___x_5443_; 
v_array_5436_ = lean_ctor_get(v_fst_5408_, 0);
v_start_5437_ = lean_ctor_get(v_fst_5408_, 1);
v_stop_5438_ = lean_ctor_get(v_fst_5408_, 2);
v___x_5439_ = lean_array_fget(v_array_5412_, v_start_5413_);
v___x_5440_ = lean_unsigned_to_nat(1u);
v___x_5441_ = lean_nat_add(v_start_5413_, v___x_5440_);
lean_dec(v_start_5413_);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 1, v___x_5441_);
v___x_5443_ = v___x_5434_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_array_5412_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v___x_5441_);
lean_ctor_set(v_reuseFailAlloc_5583_, 2, v_stop_5414_);
v___x_5443_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
uint8_t v___x_5444_; 
v___x_5444_ = lean_nat_dec_lt(v_start_5437_, v_stop_5438_);
if (v___x_5444_ == 0)
{
lean_object* v___x_5446_; 
lean_dec(v___x_5439_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5443_);
v___x_5446_ = v___x_5410_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_fst_5408_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v___x_5443_);
v___x_5446_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
lean_object* v___x_5448_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5446_);
v___x_5448_ = v___x_5406_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5460_, 1, v___x_5446_);
v___x_5448_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
lean_object* v___x_5450_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 1, v___x_5448_);
v___x_5450_ = v___x_5402_;
goto v_reusejp_5449_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v_fst_5400_);
lean_ctor_set(v_reuseFailAlloc_5459_, 1, v___x_5448_);
v___x_5450_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5449_;
}
v_reusejp_5449_:
{
lean_object* v___x_5452_; 
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5450_);
v___x_5452_ = v___x_5398_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_fst_5396_);
lean_ctor_set(v_reuseFailAlloc_5458_, 1, v___x_5450_);
v___x_5452_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
lean_object* v___x_5454_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5452_);
v___x_5454_ = v___x_5394_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v___x_5452_);
v___x_5454_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5455_; lean_object* v___f_5456_; 
v___x_5455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5455_, 0, v___x_5454_);
v___f_5456_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5456_, 0, v___x_5455_);
v___y_5362_ = v___f_5456_;
goto v___jp_5361_;
}
}
}
}
}
}
else
{
lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5579_; 
lean_inc(v_stop_5438_);
lean_inc(v_start_5437_);
lean_inc_ref(v_array_5436_);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_fst_5408_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; lean_object* v_unused_5581_; lean_object* v_unused_5582_; 
v_unused_5580_ = lean_ctor_get(v_fst_5408_, 2);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_fst_5408_, 1);
lean_dec(v_unused_5581_);
v_unused_5582_ = lean_ctor_get(v_fst_5408_, 0);
lean_dec(v_unused_5582_);
v___x_5463_ = v_fst_5408_;
v_isShared_5464_ = v_isSharedCheck_5579_;
goto v_resetjp_5462_;
}
else
{
lean_dec(v_fst_5408_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5579_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v_array_5465_; lean_object* v_start_5466_; lean_object* v_stop_5467_; lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5471_; 
v_array_5465_ = lean_ctor_get(v_fst_5404_, 0);
v_start_5466_ = lean_ctor_get(v_fst_5404_, 1);
v_stop_5467_ = lean_ctor_get(v_fst_5404_, 2);
v___x_5468_ = lean_array_fget(v_array_5436_, v_start_5437_);
v___x_5469_ = lean_nat_add(v_start_5437_, v___x_5440_);
lean_dec(v_start_5437_);
if (v_isShared_5464_ == 0)
{
lean_ctor_set(v___x_5463_, 1, v___x_5469_);
v___x_5471_ = v___x_5463_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v_array_5436_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v___x_5469_);
lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_stop_5438_);
v___x_5471_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
uint8_t v___x_5472_; 
v___x_5472_ = lean_nat_dec_lt(v_start_5466_, v_stop_5467_);
if (v___x_5472_ == 0)
{
lean_object* v___x_5474_; 
lean_dec(v___x_5468_);
lean_dec(v___x_5439_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5443_);
lean_ctor_set(v___x_5410_, 0, v___x_5471_);
v___x_5474_ = v___x_5410_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v___x_5443_);
v___x_5474_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
lean_object* v___x_5476_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5474_);
v___x_5476_ = v___x_5406_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5488_; 
v_reuseFailAlloc_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5488_, 0, v_fst_5404_);
lean_ctor_set(v_reuseFailAlloc_5488_, 1, v___x_5474_);
v___x_5476_ = v_reuseFailAlloc_5488_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
lean_object* v___x_5478_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 1, v___x_5476_);
v___x_5478_ = v___x_5402_;
goto v_reusejp_5477_;
}
else
{
lean_object* v_reuseFailAlloc_5487_; 
v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5487_, 0, v_fst_5400_);
lean_ctor_set(v_reuseFailAlloc_5487_, 1, v___x_5476_);
v___x_5478_ = v_reuseFailAlloc_5487_;
goto v_reusejp_5477_;
}
v_reusejp_5477_:
{
lean_object* v___x_5480_; 
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5478_);
v___x_5480_ = v___x_5398_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_fst_5396_);
lean_ctor_set(v_reuseFailAlloc_5486_, 1, v___x_5478_);
v___x_5480_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
lean_object* v___x_5482_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5480_);
v___x_5482_ = v___x_5394_;
goto v_reusejp_5481_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5485_, 1, v___x_5480_);
v___x_5482_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5481_;
}
v_reusejp_5481_:
{
lean_object* v___x_5483_; lean_object* v___f_5484_; 
v___x_5483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5483_, 0, v___x_5482_);
v___f_5484_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5484_, 0, v___x_5483_);
v___y_5362_ = v___f_5484_;
goto v___jp_5361_;
}
}
}
}
}
}
else
{
lean_object* v___x_5491_; uint8_t v_isShared_5492_; uint8_t v_isSharedCheck_5574_; 
lean_inc(v_stop_5467_);
lean_inc(v_start_5466_);
lean_inc_ref(v_array_5465_);
v_isSharedCheck_5574_ = !lean_is_exclusive(v_fst_5404_);
if (v_isSharedCheck_5574_ == 0)
{
lean_object* v_unused_5575_; lean_object* v_unused_5576_; lean_object* v_unused_5577_; 
v_unused_5575_ = lean_ctor_get(v_fst_5404_, 2);
lean_dec(v_unused_5575_);
v_unused_5576_ = lean_ctor_get(v_fst_5404_, 1);
lean_dec(v_unused_5576_);
v_unused_5577_ = lean_ctor_get(v_fst_5404_, 0);
lean_dec(v_unused_5577_);
v___x_5491_ = v_fst_5404_;
v_isShared_5492_ = v_isSharedCheck_5574_;
goto v_resetjp_5490_;
}
else
{
lean_dec(v_fst_5404_);
v___x_5491_ = lean_box(0);
v_isShared_5492_ = v_isSharedCheck_5574_;
goto v_resetjp_5490_;
}
v_resetjp_5490_:
{
lean_object* v_array_5493_; lean_object* v_start_5494_; lean_object* v_stop_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; lean_object* v___x_5499_; 
v_array_5493_ = lean_ctor_get(v_fst_5400_, 0);
v_start_5494_ = lean_ctor_get(v_fst_5400_, 1);
v_stop_5495_ = lean_ctor_get(v_fst_5400_, 2);
v___x_5496_ = lean_array_fget(v_array_5465_, v_start_5466_);
v___x_5497_ = lean_nat_add(v_start_5466_, v___x_5440_);
lean_dec(v_start_5466_);
if (v_isShared_5492_ == 0)
{
lean_ctor_set(v___x_5491_, 1, v___x_5497_);
v___x_5499_ = v___x_5491_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_array_5465_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v___x_5497_);
lean_ctor_set(v_reuseFailAlloc_5573_, 2, v_stop_5467_);
v___x_5499_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
uint8_t v___x_5500_; 
v___x_5500_ = lean_nat_dec_lt(v_start_5494_, v_stop_5495_);
if (v___x_5500_ == 0)
{
lean_object* v___x_5502_; 
lean_dec(v___x_5496_);
lean_dec(v___x_5468_);
lean_dec(v___x_5439_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5443_);
lean_ctor_set(v___x_5410_, 0, v___x_5471_);
v___x_5502_ = v___x_5410_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5517_, 1, v___x_5443_);
v___x_5502_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5504_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5502_);
lean_ctor_set(v___x_5406_, 0, v___x_5499_);
v___x_5504_ = v___x_5406_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5506_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 1, v___x_5504_);
v___x_5506_ = v___x_5402_;
goto v_reusejp_5505_;
}
else
{
lean_object* v_reuseFailAlloc_5515_; 
v_reuseFailAlloc_5515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5515_, 0, v_fst_5400_);
lean_ctor_set(v_reuseFailAlloc_5515_, 1, v___x_5504_);
v___x_5506_ = v_reuseFailAlloc_5515_;
goto v_reusejp_5505_;
}
v_reusejp_5505_:
{
lean_object* v___x_5508_; 
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5506_);
v___x_5508_ = v___x_5398_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5514_; 
v_reuseFailAlloc_5514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5514_, 0, v_fst_5396_);
lean_ctor_set(v_reuseFailAlloc_5514_, 1, v___x_5506_);
v___x_5508_ = v_reuseFailAlloc_5514_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
lean_object* v___x_5510_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5508_);
v___x_5510_ = v___x_5394_;
goto v_reusejp_5509_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v___x_5508_);
v___x_5510_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5509_;
}
v_reusejp_5509_:
{
lean_object* v___x_5511_; lean_object* v___f_5512_; 
v___x_5511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5511_, 0, v___x_5510_);
v___f_5512_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5512_, 0, v___x_5511_);
v___y_5362_ = v___f_5512_;
goto v___jp_5361_;
}
}
}
}
}
}
else
{
lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5569_; 
lean_inc(v_stop_5495_);
lean_inc(v_start_5494_);
lean_inc_ref(v_array_5493_);
v_isSharedCheck_5569_ = !lean_is_exclusive(v_fst_5400_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; lean_object* v_unused_5571_; lean_object* v_unused_5572_; 
v_unused_5570_ = lean_ctor_get(v_fst_5400_, 2);
lean_dec(v_unused_5570_);
v_unused_5571_ = lean_ctor_get(v_fst_5400_, 1);
lean_dec(v_unused_5571_);
v_unused_5572_ = lean_ctor_get(v_fst_5400_, 0);
lean_dec(v_unused_5572_);
v___x_5519_ = v_fst_5400_;
v_isShared_5520_ = v_isSharedCheck_5569_;
goto v_resetjp_5518_;
}
else
{
lean_dec(v_fst_5400_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5569_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v_array_5521_; lean_object* v_start_5522_; lean_object* v_stop_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5527_; 
v_array_5521_ = lean_ctor_get(v_fst_5396_, 0);
v_start_5522_ = lean_ctor_get(v_fst_5396_, 1);
v_stop_5523_ = lean_ctor_get(v_fst_5396_, 2);
v___x_5524_ = lean_array_fget(v_array_5493_, v_start_5494_);
v___x_5525_ = lean_nat_add(v_start_5494_, v___x_5440_);
lean_dec(v_start_5494_);
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 1, v___x_5525_);
v___x_5527_ = v___x_5519_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_array_5493_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5525_);
lean_ctor_set(v_reuseFailAlloc_5568_, 2, v_stop_5495_);
v___x_5527_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
uint8_t v___x_5528_; 
v___x_5528_ = lean_nat_dec_lt(v_start_5522_, v_stop_5523_);
if (v___x_5528_ == 0)
{
lean_object* v___x_5530_; 
lean_dec(v___x_5524_);
lean_dec(v___x_5496_);
lean_dec(v___x_5468_);
lean_dec(v___x_5439_);
if (v_isShared_5411_ == 0)
{
lean_ctor_set(v___x_5410_, 1, v___x_5443_);
lean_ctor_set(v___x_5410_, 0, v___x_5471_);
v___x_5530_ = v___x_5410_;
goto v_reusejp_5529_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5545_, 1, v___x_5443_);
v___x_5530_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5529_;
}
v_reusejp_5529_:
{
lean_object* v___x_5532_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 1, v___x_5530_);
lean_ctor_set(v___x_5406_, 0, v___x_5499_);
v___x_5532_ = v___x_5406_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5499_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5530_);
v___x_5532_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
lean_object* v___x_5534_; 
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 1, v___x_5532_);
lean_ctor_set(v___x_5402_, 0, v___x_5527_);
v___x_5534_ = v___x_5402_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v___x_5532_);
v___x_5534_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5536_; 
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5534_);
v___x_5536_ = v___x_5398_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_fst_5396_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
lean_object* v___x_5538_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5536_);
v___x_5538_ = v___x_5394_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5541_, 1, v___x_5536_);
v___x_5538_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
lean_object* v___x_5539_; lean_object* v___f_5540_; 
v___x_5539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5538_);
v___f_5540_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5540_, 0, v___x_5539_);
v___y_5362_ = v___f_5540_;
goto v___jp_5361_;
}
}
}
}
}
}
else
{
lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5564_; 
lean_inc(v_stop_5523_);
lean_inc(v_start_5522_);
lean_inc_ref(v_array_5521_);
lean_del_object(v___x_5410_);
lean_del_object(v___x_5406_);
lean_del_object(v___x_5402_);
lean_del_object(v___x_5398_);
lean_del_object(v___x_5394_);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_fst_5396_);
if (v_isSharedCheck_5564_ == 0)
{
lean_object* v_unused_5565_; lean_object* v_unused_5566_; lean_object* v_unused_5567_; 
v_unused_5565_ = lean_ctor_get(v_fst_5396_, 2);
lean_dec(v_unused_5565_);
v_unused_5566_ = lean_ctor_get(v_fst_5396_, 1);
lean_dec(v_unused_5566_);
v_unused_5567_ = lean_ctor_get(v_fst_5396_, 0);
lean_dec(v_unused_5567_);
v___x_5547_ = v_fst_5396_;
v_isShared_5548_ = v_isSharedCheck_5564_;
goto v_resetjp_5546_;
}
else
{
lean_dec(v_fst_5396_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5564_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v_numOverlaps_5549_; lean_object* v___x_5550_; uint8_t v___x_5551_; 
v_numOverlaps_5549_ = lean_ctor_get(v___x_5524_, 1);
v___x_5550_ = lean_unsigned_to_nat(0u);
v___x_5551_ = lean_nat_dec_eq(v_numOverlaps_5549_, v___x_5550_);
if (v___x_5551_ == 0)
{
lean_object* v___x_5552_; lean_object* v___x_5553_; 
lean_del_object(v___x_5547_);
lean_dec_ref(v___x_5527_);
lean_dec(v___x_5524_);
lean_dec(v_stop_5523_);
lean_dec(v_start_5522_);
lean_dec_ref(v_array_5521_);
lean_dec_ref(v___x_5499_);
lean_dec(v___x_5496_);
lean_dec_ref(v___x_5471_);
lean_dec(v___x_5468_);
lean_dec_ref(v___x_5443_);
lean_dec(v___x_5439_);
lean_dec(v_fst_5392_);
v___x_5552_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_5553_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed), 6, 1);
lean_closure_set(v___x_5553_, 0, v___x_5552_);
v___y_5362_ = v___x_5553_;
goto v___jp_5361_;
}
else
{
uint8_t v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___f_5558_; lean_object* v___x_5559_; lean_object* v___x_5561_; 
v___x_5554_ = 0;
v___x_5555_ = lean_array_fget_borrowed(v_array_5521_, v_start_5522_);
v___x_5556_ = lean_box(v___x_5554_);
v___x_5557_ = lean_box(v_useSplitter_5351_);
lean_inc(v___x_5524_);
lean_inc(v_numDiscrEqs_5353_);
lean_inc(v_extraEqualities_5352_);
lean_inc(v___x_5555_);
lean_inc(v_a_5354_);
lean_inc_ref(v_onAlt_5350_);
v___f_5558_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5558_, 0, v___x_5496_);
lean_closure_set(v___f_5558_, 1, v_onAlt_5350_);
lean_closure_set(v___f_5558_, 2, v_a_5354_);
lean_closure_set(v___f_5558_, 3, v___x_5556_);
lean_closure_set(v___f_5558_, 4, v___x_5557_);
lean_closure_set(v___f_5558_, 5, v___x_5555_);
lean_closure_set(v___f_5558_, 6, v_extraEqualities_5352_);
lean_closure_set(v___f_5558_, 7, v_numDiscrEqs_5353_);
lean_closure_set(v___f_5558_, 8, v___x_5439_);
lean_closure_set(v___f_5558_, 9, v___x_5524_);
lean_closure_set(v___f_5558_, 10, v___x_5440_);
v___x_5559_ = lean_nat_add(v_start_5522_, v___x_5440_);
lean_dec(v_start_5522_);
if (v_isShared_5548_ == 0)
{
lean_ctor_set(v___x_5547_, 1, v___x_5559_);
v___x_5561_ = v___x_5547_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_array_5521_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v___x_5559_);
lean_ctor_set(v_reuseFailAlloc_5563_, 2, v_stop_5523_);
v___x_5561_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___f_5562_; 
v___f_5562_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5562_, 0, v___x_5468_);
lean_closure_set(v___f_5562_, 1, v___x_5524_);
lean_closure_set(v___f_5562_, 2, v___f_5558_);
lean_closure_set(v___f_5562_, 3, v_fst_5392_);
lean_closure_set(v___f_5562_, 4, v___x_5471_);
lean_closure_set(v___f_5562_, 5, v___x_5443_);
lean_closure_set(v___f_5562_, 6, v___x_5499_);
lean_closure_set(v___f_5562_, 7, v___x_5527_);
lean_closure_set(v___f_5562_, 8, v___x_5561_);
v___y_5362_ = v___f_5562_;
goto v___jp_5361_;
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
v___jp_5361_:
{
lean_object* v___x_5363_; 
lean_inc(v___y_5359_);
lean_inc_ref(v___y_5358_);
lean_inc(v___y_5357_);
lean_inc_ref(v___y_5356_);
v___x_5363_ = lean_apply_5(v___y_5362_, v___y_5356_, v___y_5357_, v___y_5358_, v___y_5359_, lean_box(0));
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5376_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5376_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5376_ == 0)
{
v___x_5366_ = v___x_5363_;
v_isShared_5367_ = v_isSharedCheck_5376_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_a_5364_);
lean_dec(v___x_5363_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5376_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
if (lean_obj_tag(v_a_5364_) == 0)
{
lean_object* v_a_5368_; lean_object* v___x_5370_; 
lean_dec(v_a_5354_);
lean_dec(v_numDiscrEqs_5353_);
lean_dec(v_extraEqualities_5352_);
lean_dec_ref(v_onAlt_5350_);
v_a_5368_ = lean_ctor_get(v_a_5364_, 0);
lean_inc(v_a_5368_);
lean_dec_ref_known(v_a_5364_, 1);
if (v_isShared_5367_ == 0)
{
lean_ctor_set(v___x_5366_, 0, v_a_5368_);
v___x_5370_ = v___x_5366_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5368_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
else
{
lean_object* v_a_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; 
lean_del_object(v___x_5366_);
v_a_5372_ = lean_ctor_get(v_a_5364_, 0);
lean_inc(v_a_5372_);
lean_dec_ref_known(v_a_5364_, 1);
v___x_5373_ = lean_unsigned_to_nat(1u);
v___x_5374_ = lean_nat_add(v_a_5354_, v___x_5373_);
lean_dec(v_a_5354_);
v_a_5354_ = v___x_5374_;
v_b_5355_ = v_a_5372_;
goto _start;
}
}
}
else
{
lean_object* v_a_5377_; lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
lean_dec(v_a_5354_);
lean_dec(v_numDiscrEqs_5353_);
lean_dec(v_extraEqualities_5352_);
lean_dec_ref(v_onAlt_5350_);
v_a_5377_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5379_ = v___x_5363_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_inc(v_a_5377_);
lean_dec(v___x_5363_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5598_, lean_object* v_onAlt_5599_, lean_object* v_useSplitter_5600_, lean_object* v_extraEqualities_5601_, lean_object* v_numDiscrEqs_5602_, lean_object* v_a_5603_, lean_object* v_b_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
uint8_t v_useSplitter_boxed_5610_; lean_object* v_res_5611_; 
v_useSplitter_boxed_5610_ = lean_unbox(v_useSplitter_5600_);
v_res_5611_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5598_, v_onAlt_5599_, v_useSplitter_boxed_5610_, v_extraEqualities_5601_, v_numDiscrEqs_5602_, v_a_5603_, v_b_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec(v_upperBound_5598_);
return v_res_5611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5612_, lean_object* v_as_5613_, size_t v_sz_5614_, size_t v_i_5615_, lean_object* v_b_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
lean_object* v_a_5623_; uint8_t v___x_5627_; 
v___x_5627_ = lean_usize_dec_lt(v_i_5615_, v_sz_5614_);
if (v___x_5627_ == 0)
{
lean_object* v___x_5628_; 
v___x_5628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5628_, 0, v_b_5616_);
return v___x_5628_;
}
else
{
lean_object* v_snd_5629_; lean_object* v_snd_5630_; lean_object* v_snd_5631_; lean_object* v_snd_5632_; lean_object* v_fst_5633_; lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5779_; 
v_snd_5629_ = lean_ctor_get(v_b_5616_, 1);
lean_inc(v_snd_5629_);
v_snd_5630_ = lean_ctor_get(v_snd_5629_, 1);
lean_inc(v_snd_5630_);
v_snd_5631_ = lean_ctor_get(v_snd_5630_, 1);
lean_inc(v_snd_5631_);
v_snd_5632_ = lean_ctor_get(v_snd_5631_, 1);
lean_inc(v_snd_5632_);
v_fst_5633_ = lean_ctor_get(v_b_5616_, 0);
v_isSharedCheck_5779_ = !lean_is_exclusive(v_b_5616_);
if (v_isSharedCheck_5779_ == 0)
{
lean_object* v_unused_5780_; 
v_unused_5780_ = lean_ctor_get(v_b_5616_, 1);
lean_dec(v_unused_5780_);
v___x_5635_ = v_b_5616_;
v_isShared_5636_ = v_isSharedCheck_5779_;
goto v_resetjp_5634_;
}
else
{
lean_inc(v_fst_5633_);
lean_dec(v_b_5616_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5779_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v_fst_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5777_; 
v_fst_5637_ = lean_ctor_get(v_snd_5629_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v_snd_5629_);
if (v_isSharedCheck_5777_ == 0)
{
lean_object* v_unused_5778_; 
v_unused_5778_ = lean_ctor_get(v_snd_5629_, 1);
lean_dec(v_unused_5778_);
v___x_5639_ = v_snd_5629_;
v_isShared_5640_ = v_isSharedCheck_5777_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_fst_5637_);
lean_dec(v_snd_5629_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5777_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v_fst_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5775_; 
v_fst_5641_ = lean_ctor_get(v_snd_5630_, 0);
v_isSharedCheck_5775_ = !lean_is_exclusive(v_snd_5630_);
if (v_isSharedCheck_5775_ == 0)
{
lean_object* v_unused_5776_; 
v_unused_5776_ = lean_ctor_get(v_snd_5630_, 1);
lean_dec(v_unused_5776_);
v___x_5643_ = v_snd_5630_;
v_isShared_5644_ = v_isSharedCheck_5775_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_fst_5641_);
lean_dec(v_snd_5630_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5775_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v_fst_5645_; lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5773_; 
v_fst_5645_ = lean_ctor_get(v_snd_5631_, 0);
v_isSharedCheck_5773_ = !lean_is_exclusive(v_snd_5631_);
if (v_isSharedCheck_5773_ == 0)
{
lean_object* v_unused_5774_; 
v_unused_5774_ = lean_ctor_get(v_snd_5631_, 1);
lean_dec(v_unused_5774_);
v___x_5647_ = v_snd_5631_;
v_isShared_5648_ = v_isSharedCheck_5773_;
goto v_resetjp_5646_;
}
else
{
lean_inc(v_fst_5645_);
lean_dec(v_snd_5631_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5773_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
lean_object* v_array_5649_; lean_object* v_start_5650_; lean_object* v_stop_5651_; uint8_t v___x_5652_; 
v_array_5649_ = lean_ctor_get(v_snd_5632_, 0);
v_start_5650_ = lean_ctor_get(v_snd_5632_, 1);
v_stop_5651_ = lean_ctor_get(v_snd_5632_, 2);
v___x_5652_ = lean_nat_dec_lt(v_start_5650_, v_stop_5651_);
if (v___x_5652_ == 0)
{
lean_object* v___x_5654_; 
if (v_isShared_5648_ == 0)
{
v___x_5654_ = v___x_5647_;
goto v_reusejp_5653_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_fst_5645_);
lean_ctor_set(v_reuseFailAlloc_5665_, 1, v_snd_5632_);
v___x_5654_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5653_;
}
v_reusejp_5653_:
{
lean_object* v___x_5656_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 1, v___x_5654_);
v___x_5656_ = v___x_5643_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_fst_5641_);
lean_ctor_set(v_reuseFailAlloc_5664_, 1, v___x_5654_);
v___x_5656_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
lean_object* v___x_5658_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 1, v___x_5656_);
v___x_5658_ = v___x_5639_;
goto v_reusejp_5657_;
}
else
{
lean_object* v_reuseFailAlloc_5663_; 
v_reuseFailAlloc_5663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5663_, 0, v_fst_5637_);
lean_ctor_set(v_reuseFailAlloc_5663_, 1, v___x_5656_);
v___x_5658_ = v_reuseFailAlloc_5663_;
goto v_reusejp_5657_;
}
v_reusejp_5657_:
{
lean_object* v___x_5660_; 
if (v_isShared_5636_ == 0)
{
lean_ctor_set(v___x_5635_, 1, v___x_5658_);
v___x_5660_ = v___x_5635_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_fst_5633_);
lean_ctor_set(v_reuseFailAlloc_5662_, 1, v___x_5658_);
v___x_5660_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
lean_object* v___x_5661_; 
v___x_5661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5661_, 0, v___x_5660_);
return v___x_5661_;
}
}
}
}
}
else
{
lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5769_; 
lean_inc(v_stop_5651_);
lean_inc(v_start_5650_);
lean_inc_ref(v_array_5649_);
v_isSharedCheck_5769_ = !lean_is_exclusive(v_snd_5632_);
if (v_isSharedCheck_5769_ == 0)
{
lean_object* v_unused_5770_; lean_object* v_unused_5771_; lean_object* v_unused_5772_; 
v_unused_5770_ = lean_ctor_get(v_snd_5632_, 2);
lean_dec(v_unused_5770_);
v_unused_5771_ = lean_ctor_get(v_snd_5632_, 1);
lean_dec(v_unused_5771_);
v_unused_5772_ = lean_ctor_get(v_snd_5632_, 0);
lean_dec(v_unused_5772_);
v___x_5667_ = v_snd_5632_;
v_isShared_5668_ = v_isSharedCheck_5769_;
goto v_resetjp_5666_;
}
else
{
lean_dec(v_snd_5632_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5769_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v_array_5669_; lean_object* v_start_5670_; lean_object* v_stop_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5676_; 
v_array_5669_ = lean_ctor_get(v_fst_5645_, 0);
v_start_5670_ = lean_ctor_get(v_fst_5645_, 1);
v_stop_5671_ = lean_ctor_get(v_fst_5645_, 2);
v___x_5672_ = lean_array_fget(v_array_5649_, v_start_5650_);
v___x_5673_ = lean_unsigned_to_nat(1u);
v___x_5674_ = lean_nat_add(v_start_5650_, v___x_5673_);
lean_dec(v_start_5650_);
if (v_isShared_5668_ == 0)
{
lean_ctor_set(v___x_5667_, 1, v___x_5674_);
v___x_5676_ = v___x_5667_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_array_5649_);
lean_ctor_set(v_reuseFailAlloc_5768_, 1, v___x_5674_);
lean_ctor_set(v_reuseFailAlloc_5768_, 2, v_stop_5651_);
v___x_5676_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
uint8_t v___x_5677_; 
v___x_5677_ = lean_nat_dec_lt(v_start_5670_, v_stop_5671_);
if (v___x_5677_ == 0)
{
lean_object* v___x_5679_; 
lean_dec(v___x_5672_);
if (v_isShared_5648_ == 0)
{
lean_ctor_set(v___x_5647_, 1, v___x_5676_);
v___x_5679_ = v___x_5647_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5690_; 
v_reuseFailAlloc_5690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_fst_5645_);
lean_ctor_set(v_reuseFailAlloc_5690_, 1, v___x_5676_);
v___x_5679_ = v_reuseFailAlloc_5690_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
lean_object* v___x_5681_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 1, v___x_5679_);
v___x_5681_ = v___x_5643_;
goto v_reusejp_5680_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_fst_5641_);
lean_ctor_set(v_reuseFailAlloc_5689_, 1, v___x_5679_);
v___x_5681_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5680_;
}
v_reusejp_5680_:
{
lean_object* v___x_5683_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 1, v___x_5681_);
v___x_5683_ = v___x_5639_;
goto v_reusejp_5682_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_fst_5637_);
lean_ctor_set(v_reuseFailAlloc_5688_, 1, v___x_5681_);
v___x_5683_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5682_;
}
v_reusejp_5682_:
{
lean_object* v___x_5685_; 
if (v_isShared_5636_ == 0)
{
lean_ctor_set(v___x_5635_, 1, v___x_5683_);
v___x_5685_ = v___x_5635_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_fst_5633_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v___x_5683_);
v___x_5685_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
lean_object* v___x_5686_; 
v___x_5686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5685_);
return v___x_5686_;
}
}
}
}
}
else
{
lean_object* v___x_5692_; uint8_t v_isShared_5693_; uint8_t v_isSharedCheck_5764_; 
lean_inc(v_stop_5671_);
lean_inc(v_start_5670_);
lean_inc_ref(v_array_5669_);
v_isSharedCheck_5764_ = !lean_is_exclusive(v_fst_5645_);
if (v_isSharedCheck_5764_ == 0)
{
lean_object* v_unused_5765_; lean_object* v_unused_5766_; lean_object* v_unused_5767_; 
v_unused_5765_ = lean_ctor_get(v_fst_5645_, 2);
lean_dec(v_unused_5765_);
v_unused_5766_ = lean_ctor_get(v_fst_5645_, 1);
lean_dec(v_unused_5766_);
v_unused_5767_ = lean_ctor_get(v_fst_5645_, 0);
lean_dec(v_unused_5767_);
v___x_5692_ = v_fst_5645_;
v_isShared_5693_ = v_isSharedCheck_5764_;
goto v_resetjp_5691_;
}
else
{
lean_dec(v_fst_5645_);
v___x_5692_ = lean_box(0);
v_isShared_5693_ = v_isSharedCheck_5764_;
goto v_resetjp_5691_;
}
v_resetjp_5691_:
{
lean_object* v___x_5694_; lean_object* v___x_5695_; lean_object* v___x_5697_; 
v___x_5694_ = lean_array_fget(v_array_5669_, v_start_5670_);
v___x_5695_ = lean_nat_add(v_start_5670_, v___x_5673_);
lean_dec(v_start_5670_);
if (v_isShared_5693_ == 0)
{
lean_ctor_set(v___x_5692_, 1, v___x_5695_);
v___x_5697_ = v___x_5692_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_array_5669_);
lean_ctor_set(v_reuseFailAlloc_5763_, 1, v___x_5695_);
lean_ctor_set(v_reuseFailAlloc_5763_, 2, v_stop_5671_);
v___x_5697_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
if (v_addEqualities_5612_ == 0)
{
lean_dec(v___x_5694_);
goto v___jp_5698_;
}
else
{
if (lean_obj_tag(v___x_5672_) == 0)
{
lean_object* v_a_5714_; lean_object* v___x_5715_; 
lean_del_object(v___x_5647_);
lean_del_object(v___x_5643_);
lean_del_object(v___x_5639_);
lean_del_object(v___x_5635_);
v_a_5714_ = lean_array_uget_borrowed(v_as_5613_, v_i_5615_);
lean_inc(v_a_5714_);
v___x_5715_ = l_Lean_Meta_isProof(v_a_5714_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
if (lean_obj_tag(v___x_5715_) == 0)
{
lean_object* v_a_5716_; uint8_t v___x_5717_; 
v_a_5716_ = lean_ctor_get(v___x_5715_, 0);
lean_inc(v_a_5716_);
lean_dec_ref_known(v___x_5715_, 1);
v___x_5717_ = lean_unbox(v_a_5716_);
lean_dec(v_a_5716_);
if (v___x_5717_ == 0)
{
lean_object* v___x_5718_; 
lean_inc(v_a_5714_);
v___x_5718_ = l_Lean_Meta_mkEqHEq(v___x_5694_, v_a_5714_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
if (lean_obj_tag(v___x_5718_) == 0)
{
lean_object* v_a_5719_; lean_object* v___x_5720_; 
v_a_5719_ = lean_ctor_get(v___x_5718_, 0);
lean_inc_n(v_a_5719_, 2);
lean_dec_ref_known(v___x_5718_, 1);
v___x_5720_ = l_Lean_mkArrow(v_a_5719_, v_fst_5633_, v___y_5619_, v___y_5620_);
if (lean_obj_tag(v___x_5720_) == 0)
{
lean_object* v_a_5721_; uint8_t v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5724_; lean_object* v___x_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; 
v_a_5721_ = lean_ctor_get(v___x_5720_, 0);
lean_inc(v_a_5721_);
lean_dec_ref_known(v___x_5720_, 1);
v___x_5722_ = l_Lean_Expr_isHEq(v_a_5719_);
lean_dec(v_a_5719_);
v___x_5723_ = lean_box(v___x_5722_);
v___x_5724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5724_, 0, v___x_5723_);
v___x_5725_ = lean_array_push(v_fst_5637_, v___x_5724_);
v___x_5726_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7___closed__0));
v___x_5727_ = lean_array_push(v_fst_5641_, v___x_5726_);
v___x_5728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5697_);
lean_ctor_set(v___x_5728_, 1, v___x_5676_);
v___x_5729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5727_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5725_);
lean_ctor_set(v___x_5730_, 1, v___x_5729_);
v___x_5731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5731_, 0, v_a_5721_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
v_a_5623_ = v___x_5731_;
goto v___jp_5622_;
}
else
{
lean_object* v_a_5732_; lean_object* v___x_5734_; uint8_t v_isShared_5735_; uint8_t v_isSharedCheck_5739_; 
lean_dec(v_a_5719_);
lean_dec_ref(v___x_5697_);
lean_dec_ref(v___x_5676_);
lean_dec(v_fst_5641_);
lean_dec(v_fst_5637_);
v_a_5732_ = lean_ctor_get(v___x_5720_, 0);
v_isSharedCheck_5739_ = !lean_is_exclusive(v___x_5720_);
if (v_isSharedCheck_5739_ == 0)
{
v___x_5734_ = v___x_5720_;
v_isShared_5735_ = v_isSharedCheck_5739_;
goto v_resetjp_5733_;
}
else
{
lean_inc(v_a_5732_);
lean_dec(v___x_5720_);
v___x_5734_ = lean_box(0);
v_isShared_5735_ = v_isSharedCheck_5739_;
goto v_resetjp_5733_;
}
v_resetjp_5733_:
{
lean_object* v___x_5737_; 
if (v_isShared_5735_ == 0)
{
v___x_5737_ = v___x_5734_;
goto v_reusejp_5736_;
}
else
{
lean_object* v_reuseFailAlloc_5738_; 
v_reuseFailAlloc_5738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5738_, 0, v_a_5732_);
v___x_5737_ = v_reuseFailAlloc_5738_;
goto v_reusejp_5736_;
}
v_reusejp_5736_:
{
return v___x_5737_;
}
}
}
}
else
{
lean_object* v_a_5740_; lean_object* v___x_5742_; uint8_t v_isShared_5743_; uint8_t v_isSharedCheck_5747_; 
lean_dec_ref(v___x_5697_);
lean_dec_ref(v___x_5676_);
lean_dec(v_fst_5641_);
lean_dec(v_fst_5637_);
lean_dec(v_fst_5633_);
v_a_5740_ = lean_ctor_get(v___x_5718_, 0);
v_isSharedCheck_5747_ = !lean_is_exclusive(v___x_5718_);
if (v_isSharedCheck_5747_ == 0)
{
v___x_5742_ = v___x_5718_;
v_isShared_5743_ = v_isSharedCheck_5747_;
goto v_resetjp_5741_;
}
else
{
lean_inc(v_a_5740_);
lean_dec(v___x_5718_);
v___x_5742_ = lean_box(0);
v_isShared_5743_ = v_isSharedCheck_5747_;
goto v_resetjp_5741_;
}
v_resetjp_5741_:
{
lean_object* v___x_5745_; 
if (v_isShared_5743_ == 0)
{
v___x_5745_ = v___x_5742_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v_a_5740_);
v___x_5745_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
return v___x_5745_;
}
}
}
}
else
{
lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; 
lean_dec(v___x_5694_);
v___x_5748_ = lean_box(0);
v___x_5749_ = lean_array_push(v_fst_5637_, v___x_5748_);
v___x_5750_ = lean_array_push(v_fst_5641_, v___x_5672_);
v___x_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5697_);
lean_ctor_set(v___x_5751_, 1, v___x_5676_);
v___x_5752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5750_);
lean_ctor_set(v___x_5752_, 1, v___x_5751_);
v___x_5753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5753_, 0, v___x_5749_);
lean_ctor_set(v___x_5753_, 1, v___x_5752_);
v___x_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5754_, 0, v_fst_5633_);
lean_ctor_set(v___x_5754_, 1, v___x_5753_);
v_a_5623_ = v___x_5754_;
goto v___jp_5622_;
}
}
else
{
lean_object* v_a_5755_; lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5762_; 
lean_dec_ref(v___x_5697_);
lean_dec(v___x_5694_);
lean_dec_ref(v___x_5676_);
lean_dec(v_fst_5641_);
lean_dec(v_fst_5637_);
lean_dec(v_fst_5633_);
v_a_5755_ = lean_ctor_get(v___x_5715_, 0);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5715_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5757_ = v___x_5715_;
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
else
{
lean_inc(v_a_5755_);
lean_dec(v___x_5715_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5760_; 
if (v_isShared_5758_ == 0)
{
v___x_5760_ = v___x_5757_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_a_5755_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
}
else
{
lean_dec(v___x_5694_);
goto v___jp_5698_;
}
}
v___jp_5698_:
{
lean_object* v___x_5699_; lean_object* v___x_5700_; lean_object* v___x_5701_; lean_object* v___x_5703_; 
v___x_5699_ = lean_box(0);
v___x_5700_ = lean_array_push(v_fst_5637_, v___x_5699_);
v___x_5701_ = lean_array_push(v_fst_5641_, v___x_5672_);
if (v_isShared_5648_ == 0)
{
lean_ctor_set(v___x_5647_, 1, v___x_5676_);
lean_ctor_set(v___x_5647_, 0, v___x_5697_);
v___x_5703_ = v___x_5647_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5713_; 
v_reuseFailAlloc_5713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5713_, 0, v___x_5697_);
lean_ctor_set(v_reuseFailAlloc_5713_, 1, v___x_5676_);
v___x_5703_ = v_reuseFailAlloc_5713_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
lean_object* v___x_5705_; 
if (v_isShared_5644_ == 0)
{
lean_ctor_set(v___x_5643_, 1, v___x_5703_);
lean_ctor_set(v___x_5643_, 0, v___x_5701_);
v___x_5705_ = v___x_5643_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v___x_5701_);
lean_ctor_set(v_reuseFailAlloc_5712_, 1, v___x_5703_);
v___x_5705_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
lean_object* v___x_5707_; 
if (v_isShared_5640_ == 0)
{
lean_ctor_set(v___x_5639_, 1, v___x_5705_);
lean_ctor_set(v___x_5639_, 0, v___x_5700_);
v___x_5707_ = v___x_5639_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v___x_5700_);
lean_ctor_set(v_reuseFailAlloc_5711_, 1, v___x_5705_);
v___x_5707_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
lean_object* v___x_5709_; 
if (v_isShared_5636_ == 0)
{
lean_ctor_set(v___x_5635_, 1, v___x_5707_);
v___x_5709_ = v___x_5635_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_fst_5633_);
lean_ctor_set(v_reuseFailAlloc_5710_, 1, v___x_5707_);
v___x_5709_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
v_a_5623_ = v___x_5709_;
goto v___jp_5622_;
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
v___jp_5622_:
{
size_t v___x_5624_; size_t v___x_5625_; 
v___x_5624_ = ((size_t)1ULL);
v___x_5625_ = lean_usize_add(v_i_5615_, v___x_5624_);
v_i_5615_ = v___x_5625_;
v_b_5616_ = v_a_5623_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5781_, lean_object* v_as_5782_, lean_object* v_sz_5783_, lean_object* v_i_5784_, lean_object* v_b_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
uint8_t v_addEqualities_boxed_5791_; size_t v_sz_boxed_5792_; size_t v_i_boxed_5793_; lean_object* v_res_5794_; 
v_addEqualities_boxed_5791_ = lean_unbox(v_addEqualities_5781_);
v_sz_boxed_5792_ = lean_unbox_usize(v_sz_5783_);
lean_dec(v_sz_5783_);
v_i_boxed_5793_ = lean_unbox_usize(v_i_5784_);
lean_dec(v_i_5784_);
v_res_5794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5791_, v_as_5782_, v_sz_boxed_5792_, v_i_boxed_5793_, v_b_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
lean_dec_ref(v_as_5782_);
return v_res_5794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5795_, lean_object* v_toMatcherInfo_5796_, lean_object* v_a_5797_, uint8_t v_addEqualities_5798_, size_t v___x_5799_, lean_object* v_discrs_5800_, lean_object* v_motiveArgs_5801_, lean_object* v_motiveBody_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_){
_start:
{
lean_object* v___x_5900_; lean_object* v___x_5901_; uint8_t v___x_5902_; 
v___x_5900_ = lean_array_get_size(v_motiveArgs_5801_);
v___x_5901_ = lean_array_get_size(v_discrs_5800_);
v___x_5902_ = lean_nat_dec_eq(v___x_5900_, v___x_5901_);
if (v___x_5902_ == 0)
{
lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v_a_5911_; lean_object* v___x_5913_; uint8_t v_isShared_5914_; uint8_t v_isSharedCheck_5918_; 
lean_dec_ref(v_motiveBody_5802_);
lean_dec_ref(v_motiveArgs_5801_);
lean_dec_ref(v_a_5797_);
lean_dec_ref(v_toMatcherInfo_5796_);
lean_dec_ref(v_onMotive_5795_);
v___x_5903_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5904_ = l_Nat_reprFast(v___x_5901_);
v___x_5905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5904_);
v___x_5906_ = l_Lean_MessageData_ofFormat(v___x_5905_);
v___x_5907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5903_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
v___x_5908_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5907_);
lean_ctor_set(v___x_5909_, 1, v___x_5908_);
v___x_5910_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5909_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_);
v_a_5911_ = lean_ctor_get(v___x_5910_, 0);
v_isSharedCheck_5918_ = !lean_is_exclusive(v___x_5910_);
if (v_isSharedCheck_5918_ == 0)
{
v___x_5913_ = v___x_5910_;
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
else
{
lean_inc(v_a_5911_);
lean_dec(v___x_5910_);
v___x_5913_ = lean_box(0);
v_isShared_5914_ = v_isSharedCheck_5918_;
goto v_resetjp_5912_;
}
v_resetjp_5912_:
{
lean_object* v___x_5916_; 
if (v_isShared_5914_ == 0)
{
v___x_5916_ = v___x_5913_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5917_; 
v_reuseFailAlloc_5917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
v___x_5916_ = v_reuseFailAlloc_5917_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
return v___x_5916_;
}
}
}
else
{
goto v___jp_5808_;
}
v___jp_5808_:
{
lean_object* v___x_5809_; 
lean_inc(v___y_5806_);
lean_inc_ref(v___y_5805_);
lean_inc(v___y_5804_);
lean_inc_ref(v___y_5803_);
lean_inc_ref(v_motiveArgs_5801_);
v___x_5809_ = lean_apply_7(v_onMotive_5795_, v_motiveArgs_5801_, v_motiveBody_5802_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_, lean_box(0));
if (lean_obj_tag(v___x_5809_) == 0)
{
lean_object* v_a_5810_; lean_object* v_discrInfos_5811_; lean_object* v___x_5812_; lean_object* v_addHEqualities_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; size_t v_sz_5822_; lean_object* v___x_5823_; 
v_a_5810_ = lean_ctor_get(v___x_5809_, 0);
lean_inc(v_a_5810_);
lean_dec_ref_known(v___x_5809_, 1);
v_discrInfos_5811_ = lean_ctor_get(v_toMatcherInfo_5796_, 4);
lean_inc_ref(v_discrInfos_5811_);
lean_dec_ref(v_toMatcherInfo_5796_);
v___x_5812_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5813_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5814_ = lean_array_get_size(v_a_5797_);
v___x_5815_ = l_Array_toSubarray___redArg(v_a_5797_, v___x_5812_, v___x_5814_);
v___x_5816_ = lean_array_get_size(v_discrInfos_5811_);
v___x_5817_ = l_Array_toSubarray___redArg(v_discrInfos_5811_, v___x_5812_, v___x_5816_);
v___x_5818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5818_, 0, v___x_5815_);
lean_ctor_set(v___x_5818_, 1, v___x_5817_);
v___x_5819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5819_, 0, v_addHEqualities_5813_);
lean_ctor_set(v___x_5819_, 1, v___x_5818_);
v___x_5820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5820_, 0, v_addHEqualities_5813_);
lean_ctor_set(v___x_5820_, 1, v___x_5819_);
v___x_5821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5821_, 0, v_a_5810_);
lean_ctor_set(v___x_5821_, 1, v___x_5820_);
v_sz_5822_ = lean_array_size(v_motiveArgs_5801_);
v___x_5823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5798_, v_motiveArgs_5801_, v_sz_5822_, v___x_5799_, v___x_5821_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_);
if (lean_obj_tag(v___x_5823_) == 0)
{
lean_object* v_a_5824_; lean_object* v_snd_5825_; lean_object* v_snd_5826_; lean_object* v_fst_5827_; lean_object* v___x_5829_; uint8_t v_isShared_5830_; uint8_t v_isSharedCheck_5882_; 
v_a_5824_ = lean_ctor_get(v___x_5823_, 0);
lean_inc(v_a_5824_);
lean_dec_ref_known(v___x_5823_, 1);
v_snd_5825_ = lean_ctor_get(v_a_5824_, 1);
lean_inc(v_snd_5825_);
v_snd_5826_ = lean_ctor_get(v_snd_5825_, 1);
lean_inc(v_snd_5826_);
v_fst_5827_ = lean_ctor_get(v_a_5824_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v_a_5824_);
if (v_isSharedCheck_5882_ == 0)
{
lean_object* v_unused_5883_; 
v_unused_5883_ = lean_ctor_get(v_a_5824_, 1);
lean_dec(v_unused_5883_);
v___x_5829_ = v_a_5824_;
v_isShared_5830_ = v_isSharedCheck_5882_;
goto v_resetjp_5828_;
}
else
{
lean_inc(v_fst_5827_);
lean_dec(v_a_5824_);
v___x_5829_ = lean_box(0);
v_isShared_5830_ = v_isSharedCheck_5882_;
goto v_resetjp_5828_;
}
v_resetjp_5828_:
{
lean_object* v_fst_5831_; lean_object* v___x_5833_; uint8_t v_isShared_5834_; uint8_t v_isSharedCheck_5880_; 
v_fst_5831_ = lean_ctor_get(v_snd_5825_, 0);
v_isSharedCheck_5880_ = !lean_is_exclusive(v_snd_5825_);
if (v_isSharedCheck_5880_ == 0)
{
lean_object* v_unused_5881_; 
v_unused_5881_ = lean_ctor_get(v_snd_5825_, 1);
lean_dec(v_unused_5881_);
v___x_5833_ = v_snd_5825_;
v_isShared_5834_ = v_isSharedCheck_5880_;
goto v_resetjp_5832_;
}
else
{
lean_inc(v_fst_5831_);
lean_dec(v_snd_5825_);
v___x_5833_ = lean_box(0);
v_isShared_5834_ = v_isSharedCheck_5880_;
goto v_resetjp_5832_;
}
v_resetjp_5832_:
{
lean_object* v_fst_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5878_; 
v_fst_5835_ = lean_ctor_get(v_snd_5826_, 0);
v_isSharedCheck_5878_ = !lean_is_exclusive(v_snd_5826_);
if (v_isSharedCheck_5878_ == 0)
{
lean_object* v_unused_5879_; 
v_unused_5879_ = lean_ctor_get(v_snd_5826_, 1);
lean_dec(v_unused_5879_);
v___x_5837_ = v_snd_5826_;
v_isShared_5838_ = v_isSharedCheck_5878_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_fst_5835_);
lean_dec(v_snd_5826_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5878_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
uint8_t v___x_5839_; uint8_t v___x_5840_; uint8_t v___x_5841_; lean_object* v___x_5842_; 
v___x_5839_ = 0;
v___x_5840_ = 1;
v___x_5841_ = 1;
lean_inc(v_fst_5827_);
v___x_5842_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5801_, v_fst_5827_, v___x_5839_, v___x_5840_, v___x_5839_, v___x_5840_, v___x_5841_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_);
lean_dec_ref(v_motiveArgs_5801_);
if (lean_obj_tag(v___x_5842_) == 0)
{
lean_object* v_a_5843_; lean_object* v___x_5844_; 
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
lean_inc(v_a_5843_);
lean_dec_ref_known(v___x_5842_, 1);
v___x_5844_ = l_Lean_Meta_getLevel(v_fst_5827_, v___y_5803_, v___y_5804_, v___y_5805_, v___y_5806_);
if (lean_obj_tag(v___x_5844_) == 0)
{
lean_object* v_a_5845_; lean_object* v___x_5847_; uint8_t v_isShared_5848_; uint8_t v_isSharedCheck_5861_; 
v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
v_isSharedCheck_5861_ = !lean_is_exclusive(v___x_5844_);
if (v_isSharedCheck_5861_ == 0)
{
v___x_5847_ = v___x_5844_;
v_isShared_5848_ = v_isSharedCheck_5861_;
goto v_resetjp_5846_;
}
else
{
lean_inc(v_a_5845_);
lean_dec(v___x_5844_);
v___x_5847_ = lean_box(0);
v_isShared_5848_ = v_isSharedCheck_5861_;
goto v_resetjp_5846_;
}
v_resetjp_5846_:
{
lean_object* v___x_5850_; 
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 1, v_fst_5835_);
lean_ctor_set(v___x_5837_, 0, v_fst_5831_);
v___x_5850_ = v___x_5837_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5860_; 
v_reuseFailAlloc_5860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_fst_5831_);
lean_ctor_set(v_reuseFailAlloc_5860_, 1, v_fst_5835_);
v___x_5850_ = v_reuseFailAlloc_5860_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
lean_object* v___x_5852_; 
if (v_isShared_5834_ == 0)
{
lean_ctor_set(v___x_5833_, 1, v___x_5850_);
lean_ctor_set(v___x_5833_, 0, v_a_5845_);
v___x_5852_ = v___x_5833_;
goto v_reusejp_5851_;
}
else
{
lean_object* v_reuseFailAlloc_5859_; 
v_reuseFailAlloc_5859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5859_, 0, v_a_5845_);
lean_ctor_set(v_reuseFailAlloc_5859_, 1, v___x_5850_);
v___x_5852_ = v_reuseFailAlloc_5859_;
goto v_reusejp_5851_;
}
v_reusejp_5851_:
{
lean_object* v___x_5854_; 
if (v_isShared_5830_ == 0)
{
lean_ctor_set(v___x_5829_, 1, v___x_5852_);
lean_ctor_set(v___x_5829_, 0, v_a_5843_);
v___x_5854_ = v___x_5829_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5843_);
lean_ctor_set(v_reuseFailAlloc_5858_, 1, v___x_5852_);
v___x_5854_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
lean_object* v___x_5856_; 
if (v_isShared_5848_ == 0)
{
lean_ctor_set(v___x_5847_, 0, v___x_5854_);
v___x_5856_ = v___x_5847_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v___x_5854_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
return v___x_5856_;
}
}
}
}
}
}
else
{
lean_object* v_a_5862_; lean_object* v___x_5864_; uint8_t v_isShared_5865_; uint8_t v_isSharedCheck_5869_; 
lean_dec(v_a_5843_);
lean_del_object(v___x_5837_);
lean_dec(v_fst_5835_);
lean_del_object(v___x_5833_);
lean_dec(v_fst_5831_);
lean_del_object(v___x_5829_);
v_a_5862_ = lean_ctor_get(v___x_5844_, 0);
v_isSharedCheck_5869_ = !lean_is_exclusive(v___x_5844_);
if (v_isSharedCheck_5869_ == 0)
{
v___x_5864_ = v___x_5844_;
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
else
{
lean_inc(v_a_5862_);
lean_dec(v___x_5844_);
v___x_5864_ = lean_box(0);
v_isShared_5865_ = v_isSharedCheck_5869_;
goto v_resetjp_5863_;
}
v_resetjp_5863_:
{
lean_object* v___x_5867_; 
if (v_isShared_5865_ == 0)
{
v___x_5867_ = v___x_5864_;
goto v_reusejp_5866_;
}
else
{
lean_object* v_reuseFailAlloc_5868_; 
v_reuseFailAlloc_5868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5868_, 0, v_a_5862_);
v___x_5867_ = v_reuseFailAlloc_5868_;
goto v_reusejp_5866_;
}
v_reusejp_5866_:
{
return v___x_5867_;
}
}
}
}
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_del_object(v___x_5837_);
lean_dec(v_fst_5835_);
lean_del_object(v___x_5833_);
lean_dec(v_fst_5831_);
lean_del_object(v___x_5829_);
lean_dec(v_fst_5827_);
v_a_5870_ = lean_ctor_get(v___x_5842_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5842_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5842_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5842_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5891_; 
lean_dec_ref(v_motiveArgs_5801_);
v_a_5884_ = lean_ctor_get(v___x_5823_, 0);
v_isSharedCheck_5891_ = !lean_is_exclusive(v___x_5823_);
if (v_isSharedCheck_5891_ == 0)
{
v___x_5886_ = v___x_5823_;
v_isShared_5887_ = v_isSharedCheck_5891_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_a_5884_);
lean_dec(v___x_5823_);
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
else
{
lean_object* v_a_5892_; lean_object* v___x_5894_; uint8_t v_isShared_5895_; uint8_t v_isSharedCheck_5899_; 
lean_dec_ref(v_motiveArgs_5801_);
lean_dec_ref(v_a_5797_);
lean_dec_ref(v_toMatcherInfo_5796_);
v_a_5892_ = lean_ctor_get(v___x_5809_, 0);
v_isSharedCheck_5899_ = !lean_is_exclusive(v___x_5809_);
if (v_isSharedCheck_5899_ == 0)
{
v___x_5894_ = v___x_5809_;
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
else
{
lean_inc(v_a_5892_);
lean_dec(v___x_5809_);
v___x_5894_ = lean_box(0);
v_isShared_5895_ = v_isSharedCheck_5899_;
goto v_resetjp_5893_;
}
v_resetjp_5893_:
{
lean_object* v___x_5897_; 
if (v_isShared_5895_ == 0)
{
v___x_5897_ = v___x_5894_;
goto v_reusejp_5896_;
}
else
{
lean_object* v_reuseFailAlloc_5898_; 
v_reuseFailAlloc_5898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5898_, 0, v_a_5892_);
v___x_5897_ = v_reuseFailAlloc_5898_;
goto v_reusejp_5896_;
}
v_reusejp_5896_:
{
return v___x_5897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5919_, lean_object* v_toMatcherInfo_5920_, lean_object* v_a_5921_, lean_object* v_addEqualities_5922_, lean_object* v___x_5923_, lean_object* v_discrs_5924_, lean_object* v_motiveArgs_5925_, lean_object* v_motiveBody_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_){
_start:
{
uint8_t v_addEqualities_boxed_5932_; size_t v___x_34551__boxed_5933_; lean_object* v_res_5934_; 
v_addEqualities_boxed_5932_ = lean_unbox(v_addEqualities_5922_);
v___x_34551__boxed_5933_ = lean_unbox_usize(v___x_5923_);
lean_dec(v___x_5923_);
v_res_5934_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5919_, v_toMatcherInfo_5920_, v_a_5921_, v_addEqualities_boxed_5932_, v___x_34551__boxed_5933_, v_discrs_5924_, v_motiveArgs_5925_, v_motiveBody_5926_, v___y_5927_, v___y_5928_, v___y_5929_, v___y_5930_);
lean_dec(v___y_5930_);
lean_dec_ref(v___y_5929_);
lean_dec(v___y_5928_);
lean_dec_ref(v___y_5927_);
lean_dec_ref(v_discrs_5924_);
return v_res_5934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5935_, size_t v_sz_5936_, size_t v_i_5937_, lean_object* v_b_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_){
_start:
{
lean_object* v_a_5945_; uint8_t v___x_5949_; 
v___x_5949_ = lean_usize_dec_lt(v_i_5937_, v_sz_5936_);
if (v___x_5949_ == 0)
{
lean_object* v___x_5950_; 
v___x_5950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5950_, 0, v_b_5938_);
return v___x_5950_;
}
else
{
lean_object* v_snd_5951_; lean_object* v_snd_5952_; lean_object* v_fst_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_6013_; 
v_snd_5951_ = lean_ctor_get(v_b_5938_, 1);
lean_inc(v_snd_5951_);
v_snd_5952_ = lean_ctor_get(v_snd_5951_, 1);
lean_inc(v_snd_5952_);
v_fst_5953_ = lean_ctor_get(v_b_5938_, 0);
v_isSharedCheck_6013_ = !lean_is_exclusive(v_b_5938_);
if (v_isSharedCheck_6013_ == 0)
{
lean_object* v_unused_6014_; 
v_unused_6014_ = lean_ctor_get(v_b_5938_, 1);
lean_dec(v_unused_6014_);
v___x_5955_ = v_b_5938_;
v_isShared_5956_ = v_isSharedCheck_6013_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_fst_5953_);
lean_dec(v_b_5938_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_6013_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v_fst_5957_; lean_object* v___x_5959_; uint8_t v_isShared_5960_; uint8_t v_isSharedCheck_6011_; 
v_fst_5957_ = lean_ctor_get(v_snd_5951_, 0);
v_isSharedCheck_6011_ = !lean_is_exclusive(v_snd_5951_);
if (v_isSharedCheck_6011_ == 0)
{
lean_object* v_unused_6012_; 
v_unused_6012_ = lean_ctor_get(v_snd_5951_, 1);
lean_dec(v_unused_6012_);
v___x_5959_ = v_snd_5951_;
v_isShared_5960_ = v_isSharedCheck_6011_;
goto v_resetjp_5958_;
}
else
{
lean_inc(v_fst_5957_);
lean_dec(v_snd_5951_);
v___x_5959_ = lean_box(0);
v_isShared_5960_ = v_isSharedCheck_6011_;
goto v_resetjp_5958_;
}
v_resetjp_5958_:
{
lean_object* v_array_5961_; lean_object* v_start_5962_; lean_object* v_stop_5963_; uint8_t v___x_5964_; 
v_array_5961_ = lean_ctor_get(v_snd_5952_, 0);
v_start_5962_ = lean_ctor_get(v_snd_5952_, 1);
v_stop_5963_ = lean_ctor_get(v_snd_5952_, 2);
v___x_5964_ = lean_nat_dec_lt(v_start_5962_, v_stop_5963_);
if (v___x_5964_ == 0)
{
lean_object* v___x_5966_; 
if (v_isShared_5960_ == 0)
{
v___x_5966_ = v___x_5959_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_fst_5957_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v_snd_5952_);
v___x_5966_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
lean_object* v___x_5968_; 
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 1, v___x_5966_);
v___x_5968_ = v___x_5955_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v_fst_5953_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v___x_5966_);
v___x_5968_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
lean_object* v___x_5969_; 
v___x_5969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5968_);
return v___x_5969_;
}
}
}
else
{
lean_object* v___x_5973_; uint8_t v_isShared_5974_; uint8_t v_isSharedCheck_6007_; 
lean_inc(v_stop_5963_);
lean_inc(v_start_5962_);
lean_inc_ref(v_array_5961_);
v_isSharedCheck_6007_ = !lean_is_exclusive(v_snd_5952_);
if (v_isSharedCheck_6007_ == 0)
{
lean_object* v_unused_6008_; lean_object* v_unused_6009_; lean_object* v_unused_6010_; 
v_unused_6008_ = lean_ctor_get(v_snd_5952_, 2);
lean_dec(v_unused_6008_);
v_unused_6009_ = lean_ctor_get(v_snd_5952_, 1);
lean_dec(v_unused_6009_);
v_unused_6010_ = lean_ctor_get(v_snd_5952_, 0);
lean_dec(v_unused_6010_);
v___x_5973_ = v_snd_5952_;
v_isShared_5974_ = v_isSharedCheck_6007_;
goto v_resetjp_5972_;
}
else
{
lean_dec(v_snd_5952_);
v___x_5973_ = lean_box(0);
v_isShared_5974_ = v_isSharedCheck_6007_;
goto v_resetjp_5972_;
}
v_resetjp_5972_:
{
lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5979_; 
v___x_5975_ = lean_array_fget(v_array_5961_, v_start_5962_);
v___x_5976_ = lean_unsigned_to_nat(1u);
v___x_5977_ = lean_nat_add(v_start_5962_, v___x_5976_);
lean_dec(v_start_5962_);
if (v_isShared_5974_ == 0)
{
lean_ctor_set(v___x_5973_, 1, v___x_5977_);
v___x_5979_ = v___x_5973_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v_array_5961_);
lean_ctor_set(v_reuseFailAlloc_6006_, 1, v___x_5977_);
lean_ctor_set(v_reuseFailAlloc_6006_, 2, v_stop_5963_);
v___x_5979_ = v_reuseFailAlloc_6006_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
lean_object* v___y_5981_; 
if (lean_obj_tag(v___x_5975_) == 0)
{
lean_object* v___x_5999_; lean_object* v___x_6000_; 
lean_del_object(v___x_5959_);
lean_del_object(v___x_5955_);
v___x_5999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5999_, 0, v_fst_5957_);
lean_ctor_set(v___x_5999_, 1, v___x_5979_);
v___x_6000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6000_, 0, v_fst_5953_);
lean_ctor_set(v___x_6000_, 1, v___x_5999_);
v_a_5945_ = v___x_6000_;
goto v___jp_5944_;
}
else
{
lean_object* v_val_6001_; lean_object* v_a_6002_; uint8_t v___x_6003_; 
v_val_6001_ = lean_ctor_get(v___x_5975_, 0);
lean_inc(v_val_6001_);
lean_dec_ref_known(v___x_5975_, 1);
v_a_6002_ = lean_array_uget_borrowed(v_as_5935_, v_i_5937_);
v___x_6003_ = lean_unbox(v_val_6001_);
lean_dec(v_val_6001_);
if (v___x_6003_ == 0)
{
lean_object* v___x_6004_; 
lean_inc(v_a_6002_);
v___x_6004_ = l_Lean_Meta_mkEqRefl(v_a_6002_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
v___y_5981_ = v___x_6004_;
goto v___jp_5980_;
}
else
{
lean_object* v___x_6005_; 
lean_inc(v_a_6002_);
v___x_6005_ = l_Lean_Meta_mkHEqRefl(v_a_6002_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
v___y_5981_ = v___x_6005_;
goto v___jp_5980_;
}
}
v___jp_5980_:
{
if (lean_obj_tag(v___y_5981_) == 0)
{
lean_object* v_a_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5986_; 
v_a_5982_ = lean_ctor_get(v___y_5981_, 0);
lean_inc(v_a_5982_);
lean_dec_ref_known(v___y_5981_, 1);
v___x_5983_ = lean_array_push(v_fst_5953_, v_a_5982_);
v___x_5984_ = lean_nat_add(v_fst_5957_, v___x_5976_);
lean_dec(v_fst_5957_);
if (v_isShared_5960_ == 0)
{
lean_ctor_set(v___x_5959_, 1, v___x_5979_);
lean_ctor_set(v___x_5959_, 0, v___x_5984_);
v___x_5986_ = v___x_5959_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v___x_5984_);
lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5979_);
v___x_5986_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
lean_object* v___x_5988_; 
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 1, v___x_5986_);
lean_ctor_set(v___x_5955_, 0, v___x_5983_);
v___x_5988_ = v___x_5955_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5983_);
lean_ctor_set(v_reuseFailAlloc_5989_, 1, v___x_5986_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
v_a_5945_ = v___x_5988_;
goto v___jp_5944_;
}
}
}
else
{
lean_object* v_a_5991_; lean_object* v___x_5993_; uint8_t v_isShared_5994_; uint8_t v_isSharedCheck_5998_; 
lean_dec_ref(v___x_5979_);
lean_del_object(v___x_5959_);
lean_dec(v_fst_5957_);
lean_del_object(v___x_5955_);
lean_dec(v_fst_5953_);
v_a_5991_ = lean_ctor_get(v___y_5981_, 0);
v_isSharedCheck_5998_ = !lean_is_exclusive(v___y_5981_);
if (v_isSharedCheck_5998_ == 0)
{
v___x_5993_ = v___y_5981_;
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
else
{
lean_inc(v_a_5991_);
lean_dec(v___y_5981_);
v___x_5993_ = lean_box(0);
v_isShared_5994_ = v_isSharedCheck_5998_;
goto v_resetjp_5992_;
}
v_resetjp_5992_:
{
lean_object* v___x_5996_; 
if (v_isShared_5994_ == 0)
{
v___x_5996_ = v___x_5993_;
goto v_reusejp_5995_;
}
else
{
lean_object* v_reuseFailAlloc_5997_; 
v_reuseFailAlloc_5997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5991_);
v___x_5996_ = v_reuseFailAlloc_5997_;
goto v_reusejp_5995_;
}
v_reusejp_5995_:
{
return v___x_5996_;
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
v___jp_5944_:
{
size_t v___x_5946_; size_t v___x_5947_; 
v___x_5946_ = ((size_t)1ULL);
v___x_5947_ = lean_usize_add(v_i_5937_, v___x_5946_);
v_i_5937_ = v___x_5947_;
v_b_5938_ = v_a_5945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6015_, lean_object* v_sz_6016_, lean_object* v_i_6017_, lean_object* v_b_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
size_t v_sz_boxed_6024_; size_t v_i_boxed_6025_; lean_object* v_res_6026_; 
v_sz_boxed_6024_ = lean_unbox_usize(v_sz_6016_);
lean_dec(v_sz_6016_);
v_i_boxed_6025_ = lean_unbox_usize(v_i_6017_);
lean_dec(v_i_6017_);
v_res_6026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6015_, v_sz_boxed_6024_, v_i_boxed_6025_, v_b_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_);
lean_dec(v___y_6022_);
lean_dec_ref(v___y_6021_);
lean_dec(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec_ref(v_as_6015_);
return v_res_6026_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_){
_start:
{
lean_object* v___x_6033_; 
v___x_6033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6027_);
return v___x_6033_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_){
_start:
{
lean_object* v_res_6040_; 
v_res_6040_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6034_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
lean_dec(v___y_6038_);
lean_dec_ref(v___y_6037_);
lean_dec(v___y_6036_);
lean_dec_ref(v___y_6035_);
return v_res_6040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6041_, size_t v_i_6042_, lean_object* v_bs_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_){
_start:
{
uint8_t v___x_6048_; 
v___x_6048_ = lean_usize_dec_lt(v_i_6042_, v_sz_6041_);
if (v___x_6048_ == 0)
{
lean_object* v___x_6049_; 
v___x_6049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6049_, 0, v_bs_6043_);
return v___x_6049_;
}
else
{
lean_object* v_v_6050_; lean_object* v___x_6051_; lean_object* v_bs_x27_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; 
v_v_6050_ = lean_array_uget(v_bs_6043_, v_i_6042_);
v___x_6051_ = lean_unsigned_to_nat(0u);
v_bs_x27_6052_ = lean_array_uset(v_bs_6043_, v_i_6042_, v___x_6051_);
v___x_6053_ = l_Lean_Expr_fvarId_x21(v_v_6050_);
lean_dec(v_v_6050_);
v___x_6054_ = l_Lean_FVarId_getUserName___redArg(v___x_6053_, v___y_6044_, v___y_6045_, v___y_6046_);
if (lean_obj_tag(v___x_6054_) == 0)
{
lean_object* v_a_6055_; size_t v___x_6056_; size_t v___x_6057_; lean_object* v___x_6058_; 
v_a_6055_ = lean_ctor_get(v___x_6054_, 0);
lean_inc(v_a_6055_);
lean_dec_ref_known(v___x_6054_, 1);
v___x_6056_ = ((size_t)1ULL);
v___x_6057_ = lean_usize_add(v_i_6042_, v___x_6056_);
v___x_6058_ = lean_array_uset(v_bs_x27_6052_, v_i_6042_, v_a_6055_);
v_i_6042_ = v___x_6057_;
v_bs_6043_ = v___x_6058_;
goto _start;
}
else
{
lean_object* v_a_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6067_; 
lean_dec_ref(v_bs_x27_6052_);
v_a_6060_ = lean_ctor_get(v___x_6054_, 0);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___x_6054_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6062_ = v___x_6054_;
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_a_6060_);
lean_dec(v___x_6054_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6065_; 
if (v_isShared_6063_ == 0)
{
v___x_6065_ = v___x_6062_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6060_);
v___x_6065_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
return v___x_6065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6068_, lean_object* v_i_6069_, lean_object* v_bs_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_){
_start:
{
size_t v_sz_boxed_6075_; size_t v_i_boxed_6076_; lean_object* v_res_6077_; 
v_sz_boxed_6075_ = lean_unbox_usize(v_sz_6068_);
lean_dec(v_sz_6068_);
v_i_boxed_6076_ = lean_unbox_usize(v_i_6069_);
lean_dec(v_i_6069_);
v_res_6077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6075_, v_i_boxed_6076_, v_bs_6070_, v___y_6071_, v___y_6072_, v___y_6073_);
lean_dec(v___y_6073_);
lean_dec_ref(v___y_6072_);
lean_dec_ref(v___y_6071_);
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6078_, lean_object* v_x_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_){
_start:
{
size_t v_sz_6085_; size_t v___x_6086_; lean_object* v___x_6087_; 
v_sz_6085_ = lean_array_size(v_xs_6078_);
v___x_6086_ = ((size_t)0ULL);
v___x_6087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6085_, v___x_6086_, v_xs_6078_, v___y_6080_, v___y_6082_, v___y_6083_);
return v___x_6087_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6088_, lean_object* v_x_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_){
_start:
{
lean_object* v_res_6095_; 
v_res_6095_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6088_, v_x_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_);
lean_dec(v___y_6093_);
lean_dec_ref(v___y_6092_);
lean_dec(v___y_6091_);
lean_dec_ref(v___y_6090_);
lean_dec_ref(v_x_6089_);
return v_res_6095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6096_, lean_object* v___x_6097_, lean_object* v___f_6098_, uint8_t v___x_6099_, lean_object* v_fst_6100_, lean_object* v___x_6101_, lean_object* v___x_6102_, lean_object* v___x_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_, lean_object* v___y_6107_){
_start:
{
lean_object* v___x_6109_; 
v___x_6109_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v___x_6096_, v___x_6097_, v___f_6098_, v___x_6099_, v___x_6099_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
if (lean_obj_tag(v___x_6109_) == 0)
{
lean_object* v_a_6110_; lean_object* v___x_6112_; uint8_t v_isShared_6113_; uint8_t v_isSharedCheck_6122_; 
v_a_6110_ = lean_ctor_get(v___x_6109_, 0);
v_isSharedCheck_6122_ = !lean_is_exclusive(v___x_6109_);
if (v_isSharedCheck_6122_ == 0)
{
v___x_6112_ = v___x_6109_;
v_isShared_6113_ = v_isSharedCheck_6122_;
goto v_resetjp_6111_;
}
else
{
lean_inc(v_a_6110_);
lean_dec(v___x_6109_);
v___x_6112_ = lean_box(0);
v_isShared_6113_ = v_isSharedCheck_6122_;
goto v_resetjp_6111_;
}
v_resetjp_6111_:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6120_; 
v___x_6114_ = lean_array_push(v_fst_6100_, v_a_6110_);
v___x_6115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6115_, 0, v___x_6101_);
lean_ctor_set(v___x_6115_, 1, v___x_6102_);
v___x_6116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6103_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6117_, 0, v___x_6114_);
lean_ctor_set(v___x_6117_, 1, v___x_6116_);
v___x_6118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6117_);
if (v_isShared_6113_ == 0)
{
lean_ctor_set(v___x_6112_, 0, v___x_6118_);
v___x_6120_ = v___x_6112_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v___x_6118_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
}
}
}
else
{
lean_object* v_a_6123_; lean_object* v___x_6125_; uint8_t v_isShared_6126_; uint8_t v_isSharedCheck_6130_; 
lean_dec_ref(v___x_6103_);
lean_dec_ref(v___x_6102_);
lean_dec_ref(v___x_6101_);
lean_dec(v_fst_6100_);
v_a_6123_ = lean_ctor_get(v___x_6109_, 0);
v_isSharedCheck_6130_ = !lean_is_exclusive(v___x_6109_);
if (v_isSharedCheck_6130_ == 0)
{
v___x_6125_ = v___x_6109_;
v_isShared_6126_ = v_isSharedCheck_6130_;
goto v_resetjp_6124_;
}
else
{
lean_inc(v_a_6123_);
lean_dec(v___x_6109_);
v___x_6125_ = lean_box(0);
v_isShared_6126_ = v_isSharedCheck_6130_;
goto v_resetjp_6124_;
}
v_resetjp_6124_:
{
lean_object* v___x_6128_; 
if (v_isShared_6126_ == 0)
{
v___x_6128_ = v___x_6125_;
goto v_reusejp_6127_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v_a_6123_);
v___x_6128_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6127_;
}
v_reusejp_6127_:
{
return v___x_6128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6131_, lean_object* v___x_6132_, lean_object* v___f_6133_, lean_object* v___x_6134_, lean_object* v_fst_6135_, lean_object* v___x_6136_, lean_object* v___x_6137_, lean_object* v___x_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_){
_start:
{
uint8_t v___x_35014__boxed_6144_; lean_object* v_res_6145_; 
v___x_35014__boxed_6144_ = lean_unbox(v___x_6134_);
v_res_6145_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6131_, v___x_6132_, v___f_6133_, v___x_35014__boxed_6144_, v_fst_6135_, v___x_6136_, v___x_6137_, v___x_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_);
lean_dec(v___y_6142_);
lean_dec_ref(v___y_6141_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
return v_res_6145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6146_, lean_object* v_names_6147_, lean_object* v_k_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_){
_start:
{
lean_object* v___x_6154_; 
v___x_6154_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6146_, v_names_6147_, v_k_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
if (lean_obj_tag(v___x_6154_) == 0)
{
lean_object* v_a_6155_; lean_object* v___x_6157_; uint8_t v_isShared_6158_; uint8_t v_isSharedCheck_6162_; 
v_a_6155_ = lean_ctor_get(v___x_6154_, 0);
v_isSharedCheck_6162_ = !lean_is_exclusive(v___x_6154_);
if (v_isSharedCheck_6162_ == 0)
{
v___x_6157_ = v___x_6154_;
v_isShared_6158_ = v_isSharedCheck_6162_;
goto v_resetjp_6156_;
}
else
{
lean_inc(v_a_6155_);
lean_dec(v___x_6154_);
v___x_6157_ = lean_box(0);
v_isShared_6158_ = v_isSharedCheck_6162_;
goto v_resetjp_6156_;
}
v_resetjp_6156_:
{
lean_object* v___x_6160_; 
if (v_isShared_6158_ == 0)
{
v___x_6160_ = v___x_6157_;
goto v_reusejp_6159_;
}
else
{
lean_object* v_reuseFailAlloc_6161_; 
v_reuseFailAlloc_6161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6161_, 0, v_a_6155_);
v___x_6160_ = v_reuseFailAlloc_6161_;
goto v_reusejp_6159_;
}
v_reusejp_6159_:
{
return v___x_6160_;
}
}
}
else
{
lean_object* v_a_6163_; lean_object* v___x_6165_; uint8_t v_isShared_6166_; uint8_t v_isSharedCheck_6170_; 
v_a_6163_ = lean_ctor_get(v___x_6154_, 0);
v_isSharedCheck_6170_ = !lean_is_exclusive(v___x_6154_);
if (v_isSharedCheck_6170_ == 0)
{
v___x_6165_ = v___x_6154_;
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
else
{
lean_inc(v_a_6163_);
lean_dec(v___x_6154_);
v___x_6165_ = lean_box(0);
v_isShared_6166_ = v_isSharedCheck_6170_;
goto v_resetjp_6164_;
}
v_resetjp_6164_:
{
lean_object* v___x_6168_; 
if (v_isShared_6166_ == 0)
{
v___x_6168_ = v___x_6165_;
goto v_reusejp_6167_;
}
else
{
lean_object* v_reuseFailAlloc_6169_; 
v_reuseFailAlloc_6169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6169_, 0, v_a_6163_);
v___x_6168_ = v_reuseFailAlloc_6169_;
goto v_reusejp_6167_;
}
v_reusejp_6167_:
{
return v___x_6168_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6171_, lean_object* v_names_6172_, lean_object* v_k_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_){
_start:
{
lean_object* v_res_6179_; 
v_res_6179_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6171_, v_names_6172_, v_k_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec_ref(v_names_6172_);
lean_dec_ref(v_fvars_6171_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6180_, lean_object* v_xs_6181_, lean_object* v_remaining_x27_6182_, lean_object* v_ys4_6183_, lean_object* v_onAlt_6184_, lean_object* v_a_6185_, lean_object* v_altType_6186_, uint8_t v___x_6187_, uint8_t v___x_6188_, lean_object* v___y_6189_, lean_object* v___y_6190_, lean_object* v___y_6191_, lean_object* v___y_6192_){
_start:
{
lean_object* v___x_6194_; 
v___x_6194_ = l_Lean_Meta_instantiateLambda(v___x_6180_, v_xs_6181_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
if (lean_obj_tag(v___x_6194_) == 0)
{
lean_object* v_a_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; 
v_a_6195_ = lean_ctor_get(v___x_6194_, 0);
lean_inc(v_a_6195_);
lean_dec_ref_known(v___x_6194_, 1);
lean_inc_ref(v_ys4_6183_);
lean_inc_ref(v_remaining_x27_6182_);
lean_inc_ref_n(v_xs_6181_, 2);
v___x_6196_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6196_, 0, v_xs_6181_);
lean_ctor_set(v___x_6196_, 1, v_xs_6181_);
lean_ctor_set(v___x_6196_, 2, v_remaining_x27_6182_);
lean_ctor_set(v___x_6196_, 3, v_remaining_x27_6182_);
lean_ctor_set(v___x_6196_, 4, v_ys4_6183_);
lean_inc(v___y_6192_);
lean_inc_ref(v___y_6191_);
lean_inc(v___y_6190_);
lean_inc_ref(v___y_6189_);
v___x_6197_ = lean_apply_9(v_onAlt_6184_, v_a_6185_, v_altType_6186_, v___x_6196_, v_a_6195_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_, lean_box(0));
if (lean_obj_tag(v___x_6197_) == 0)
{
lean_object* v_a_6198_; lean_object* v___x_6199_; uint8_t v___x_6200_; lean_object* v___x_6201_; 
v_a_6198_ = lean_ctor_get(v___x_6197_, 0);
lean_inc(v_a_6198_);
lean_dec_ref_known(v___x_6197_, 1);
v___x_6199_ = l_Array_append___redArg(v_xs_6181_, v_ys4_6183_);
lean_dec_ref(v_ys4_6183_);
v___x_6200_ = 1;
v___x_6201_ = l_Lean_Meta_mkLambdaFVars(v___x_6199_, v_a_6198_, v___x_6187_, v___x_6188_, v___x_6187_, v___x_6188_, v___x_6200_, v___y_6189_, v___y_6190_, v___y_6191_, v___y_6192_);
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec_ref(v___x_6199_);
return v___x_6201_;
}
else
{
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec_ref(v_ys4_6183_);
lean_dec_ref(v_xs_6181_);
return v___x_6197_;
}
}
else
{
lean_dec(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec_ref(v___y_6189_);
lean_dec_ref(v_altType_6186_);
lean_dec(v_a_6185_);
lean_dec_ref(v_onAlt_6184_);
lean_dec_ref(v_ys4_6183_);
lean_dec_ref(v_remaining_x27_6182_);
lean_dec_ref(v_xs_6181_);
return v___x_6194_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6202_, lean_object* v_xs_6203_, lean_object* v_remaining_x27_6204_, lean_object* v_ys4_6205_, lean_object* v_onAlt_6206_, lean_object* v_a_6207_, lean_object* v_altType_6208_, lean_object* v___x_6209_, lean_object* v___x_6210_, lean_object* v___y_6211_, lean_object* v___y_6212_, lean_object* v___y_6213_, lean_object* v___y_6214_, lean_object* v___y_6215_){
_start:
{
uint8_t v___x_35141__boxed_6216_; uint8_t v___x_35142__boxed_6217_; lean_object* v_res_6218_; 
v___x_35141__boxed_6216_ = lean_unbox(v___x_6209_);
v___x_35142__boxed_6217_ = lean_unbox(v___x_6210_);
v_res_6218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6202_, v_xs_6203_, v_remaining_x27_6204_, v_ys4_6205_, v_onAlt_6206_, v_a_6207_, v_altType_6208_, v___x_35141__boxed_6216_, v___x_35142__boxed_6217_, v___y_6211_, v___y_6212_, v___y_6213_, v___y_6214_);
return v_res_6218_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6219_, lean_object* v_xs_6220_, lean_object* v_remaining_x27_6221_, lean_object* v_onAlt_6222_, lean_object* v_a_6223_, uint8_t v___x_6224_, uint8_t v___x_6225_, lean_object* v___f_6226_, lean_object* v_ys4_6227_, lean_object* v_altType_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_){
_start:
{
lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___f_6236_; lean_object* v___x_6237_; 
v___x_6234_ = lean_box(v___x_6224_);
v___x_6235_ = lean_box(v___x_6225_);
lean_inc_ref(v_xs_6220_);
lean_inc_ref(v___x_6219_);
v___f_6236_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6236_, 0, v___x_6219_);
lean_closure_set(v___f_6236_, 1, v_xs_6220_);
lean_closure_set(v___f_6236_, 2, v_remaining_x27_6221_);
lean_closure_set(v___f_6236_, 3, v_ys4_6227_);
lean_closure_set(v___f_6236_, 4, v_onAlt_6222_);
lean_closure_set(v___f_6236_, 5, v_a_6223_);
lean_closure_set(v___f_6236_, 6, v_altType_6228_);
lean_closure_set(v___f_6236_, 7, v___x_6234_);
lean_closure_set(v___f_6236_, 8, v___x_6235_);
v___x_6237_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6219_, v___f_6226_, v___x_6224_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
if (lean_obj_tag(v___x_6237_) == 0)
{
lean_object* v_a_6238_; lean_object* v___x_6239_; 
v_a_6238_ = lean_ctor_get(v___x_6237_, 0);
lean_inc(v_a_6238_);
lean_dec_ref_known(v___x_6237_, 1);
v___x_6239_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6220_, v_a_6238_, v___f_6236_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
lean_dec(v_a_6238_);
lean_dec_ref(v_xs_6220_);
return v___x_6239_;
}
else
{
lean_object* v_a_6240_; lean_object* v___x_6242_; uint8_t v_isShared_6243_; uint8_t v_isSharedCheck_6247_; 
lean_dec_ref(v___f_6236_);
lean_dec_ref(v_xs_6220_);
v_a_6240_ = lean_ctor_get(v___x_6237_, 0);
v_isSharedCheck_6247_ = !lean_is_exclusive(v___x_6237_);
if (v_isSharedCheck_6247_ == 0)
{
v___x_6242_ = v___x_6237_;
v_isShared_6243_ = v_isSharedCheck_6247_;
goto v_resetjp_6241_;
}
else
{
lean_inc(v_a_6240_);
lean_dec(v___x_6237_);
v___x_6242_ = lean_box(0);
v_isShared_6243_ = v_isSharedCheck_6247_;
goto v_resetjp_6241_;
}
v_resetjp_6241_:
{
lean_object* v___x_6245_; 
if (v_isShared_6243_ == 0)
{
v___x_6245_ = v___x_6242_;
goto v_reusejp_6244_;
}
else
{
lean_object* v_reuseFailAlloc_6246_; 
v_reuseFailAlloc_6246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6246_, 0, v_a_6240_);
v___x_6245_ = v_reuseFailAlloc_6246_;
goto v_reusejp_6244_;
}
v_reusejp_6244_:
{
return v___x_6245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6248_, lean_object* v_xs_6249_, lean_object* v_remaining_x27_6250_, lean_object* v_onAlt_6251_, lean_object* v_a_6252_, lean_object* v___x_6253_, lean_object* v___x_6254_, lean_object* v___f_6255_, lean_object* v_ys4_6256_, lean_object* v_altType_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_, lean_object* v___y_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_){
_start:
{
uint8_t v___x_35183__boxed_6263_; uint8_t v___x_35184__boxed_6264_; lean_object* v_res_6265_; 
v___x_35183__boxed_6263_ = lean_unbox(v___x_6253_);
v___x_35184__boxed_6264_ = lean_unbox(v___x_6254_);
v_res_6265_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6248_, v_xs_6249_, v_remaining_x27_6250_, v_onAlt_6251_, v_a_6252_, v___x_35183__boxed_6263_, v___x_35184__boxed_6264_, v___f_6255_, v_ys4_6256_, v_altType_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
lean_dec(v___y_6261_);
lean_dec_ref(v___y_6260_);
lean_dec(v___y_6259_);
lean_dec_ref(v___y_6258_);
return v_res_6265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6266_, lean_object* v_remaining_x27_6267_, lean_object* v_onAlt_6268_, lean_object* v_a_6269_, uint8_t v___x_6270_, uint8_t v___x_6271_, lean_object* v___f_6272_, lean_object* v_extraEqualities_6273_, lean_object* v_xs_6274_, lean_object* v_altType_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_){
_start:
{
lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v___f_6283_; lean_object* v___x_6284_; lean_object* v___x_6285_; 
v___x_6281_ = lean_box(v___x_6270_);
v___x_6282_ = lean_box(v___x_6271_);
v___f_6283_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6283_, 0, v___x_6266_);
lean_closure_set(v___f_6283_, 1, v_xs_6274_);
lean_closure_set(v___f_6283_, 2, v_remaining_x27_6267_);
lean_closure_set(v___f_6283_, 3, v_onAlt_6268_);
lean_closure_set(v___f_6283_, 4, v_a_6269_);
lean_closure_set(v___f_6283_, 5, v___x_6281_);
lean_closure_set(v___f_6283_, 6, v___x_6282_);
lean_closure_set(v___f_6283_, 7, v___f_6272_);
v___x_6284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6284_, 0, v_extraEqualities_6273_);
v___x_6285_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___redArg(v_altType_6275_, v___x_6284_, v___f_6283_, v___x_6270_, v___x_6270_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_);
return v___x_6285_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6286_, lean_object* v_remaining_x27_6287_, lean_object* v_onAlt_6288_, lean_object* v_a_6289_, lean_object* v___x_6290_, lean_object* v___x_6291_, lean_object* v___f_6292_, lean_object* v_extraEqualities_6293_, lean_object* v_xs_6294_, lean_object* v_altType_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_){
_start:
{
uint8_t v___x_35238__boxed_6301_; uint8_t v___x_35239__boxed_6302_; lean_object* v_res_6303_; 
v___x_35238__boxed_6301_ = lean_unbox(v___x_6290_);
v___x_35239__boxed_6302_ = lean_unbox(v___x_6291_);
v_res_6303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6286_, v_remaining_x27_6287_, v_onAlt_6288_, v_a_6289_, v___x_35238__boxed_6301_, v___x_35239__boxed_6302_, v___f_6292_, v_extraEqualities_6293_, v_xs_6294_, v_altType_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_);
lean_dec(v___y_6299_);
lean_dec_ref(v___y_6298_);
lean_dec(v___y_6297_);
lean_dec_ref(v___y_6296_);
return v_res_6303_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6305_, lean_object* v_onAlt_6306_, lean_object* v_extraEqualities_6307_, lean_object* v_a_6308_, lean_object* v_b_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_, lean_object* v___y_6312_, lean_object* v___y_6313_){
_start:
{
lean_object* v___y_6316_; uint8_t v___x_6339_; 
v___x_6339_ = lean_nat_dec_lt(v_a_6308_, v_upperBound_6305_);
if (v___x_6339_ == 0)
{
lean_object* v___x_6340_; 
lean_dec(v_a_6308_);
lean_dec(v_extraEqualities_6307_);
lean_dec_ref(v_onAlt_6306_);
v___x_6340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6340_, 0, v_b_6309_);
return v___x_6340_;
}
else
{
lean_object* v_snd_6341_; lean_object* v_snd_6342_; lean_object* v_snd_6343_; lean_object* v_fst_6344_; lean_object* v___x_6346_; uint8_t v_isShared_6347_; uint8_t v_isSharedCheck_6451_; 
v_snd_6341_ = lean_ctor_get(v_b_6309_, 1);
lean_inc(v_snd_6341_);
v_snd_6342_ = lean_ctor_get(v_snd_6341_, 1);
lean_inc(v_snd_6342_);
v_snd_6343_ = lean_ctor_get(v_snd_6342_, 1);
lean_inc(v_snd_6343_);
v_fst_6344_ = lean_ctor_get(v_b_6309_, 0);
v_isSharedCheck_6451_ = !lean_is_exclusive(v_b_6309_);
if (v_isSharedCheck_6451_ == 0)
{
lean_object* v_unused_6452_; 
v_unused_6452_ = lean_ctor_get(v_b_6309_, 1);
lean_dec(v_unused_6452_);
v___x_6346_ = v_b_6309_;
v_isShared_6347_ = v_isSharedCheck_6451_;
goto v_resetjp_6345_;
}
else
{
lean_inc(v_fst_6344_);
lean_dec(v_b_6309_);
v___x_6346_ = lean_box(0);
v_isShared_6347_ = v_isSharedCheck_6451_;
goto v_resetjp_6345_;
}
v_resetjp_6345_:
{
lean_object* v_fst_6348_; lean_object* v___x_6350_; uint8_t v_isShared_6351_; uint8_t v_isSharedCheck_6449_; 
v_fst_6348_ = lean_ctor_get(v_snd_6341_, 0);
v_isSharedCheck_6449_ = !lean_is_exclusive(v_snd_6341_);
if (v_isSharedCheck_6449_ == 0)
{
lean_object* v_unused_6450_; 
v_unused_6450_ = lean_ctor_get(v_snd_6341_, 1);
lean_dec(v_unused_6450_);
v___x_6350_ = v_snd_6341_;
v_isShared_6351_ = v_isSharedCheck_6449_;
goto v_resetjp_6349_;
}
else
{
lean_inc(v_fst_6348_);
lean_dec(v_snd_6341_);
v___x_6350_ = lean_box(0);
v_isShared_6351_ = v_isSharedCheck_6449_;
goto v_resetjp_6349_;
}
v_resetjp_6349_:
{
lean_object* v_fst_6352_; lean_object* v___x_6354_; uint8_t v_isShared_6355_; uint8_t v_isSharedCheck_6447_; 
v_fst_6352_ = lean_ctor_get(v_snd_6342_, 0);
v_isSharedCheck_6447_ = !lean_is_exclusive(v_snd_6342_);
if (v_isSharedCheck_6447_ == 0)
{
lean_object* v_unused_6448_; 
v_unused_6448_ = lean_ctor_get(v_snd_6342_, 1);
lean_dec(v_unused_6448_);
v___x_6354_ = v_snd_6342_;
v_isShared_6355_ = v_isSharedCheck_6447_;
goto v_resetjp_6353_;
}
else
{
lean_inc(v_fst_6352_);
lean_dec(v_snd_6342_);
v___x_6354_ = lean_box(0);
v_isShared_6355_ = v_isSharedCheck_6447_;
goto v_resetjp_6353_;
}
v_resetjp_6353_:
{
lean_object* v_array_6356_; lean_object* v_start_6357_; lean_object* v_stop_6358_; uint8_t v___x_6359_; 
v_array_6356_ = lean_ctor_get(v_snd_6343_, 0);
v_start_6357_ = lean_ctor_get(v_snd_6343_, 1);
v_stop_6358_ = lean_ctor_get(v_snd_6343_, 2);
v___x_6359_ = lean_nat_dec_lt(v_start_6357_, v_stop_6358_);
if (v___x_6359_ == 0)
{
lean_object* v___x_6361_; 
if (v_isShared_6355_ == 0)
{
v___x_6361_ = v___x_6354_;
goto v_reusejp_6360_;
}
else
{
lean_object* v_reuseFailAlloc_6370_; 
v_reuseFailAlloc_6370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6370_, 0, v_fst_6352_);
lean_ctor_set(v_reuseFailAlloc_6370_, 1, v_snd_6343_);
v___x_6361_ = v_reuseFailAlloc_6370_;
goto v_reusejp_6360_;
}
v_reusejp_6360_:
{
lean_object* v___x_6363_; 
if (v_isShared_6351_ == 0)
{
lean_ctor_set(v___x_6350_, 1, v___x_6361_);
v___x_6363_ = v___x_6350_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6369_; 
v_reuseFailAlloc_6369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6369_, 0, v_fst_6348_);
lean_ctor_set(v_reuseFailAlloc_6369_, 1, v___x_6361_);
v___x_6363_ = v_reuseFailAlloc_6369_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
lean_object* v___x_6365_; 
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 1, v___x_6363_);
v___x_6365_ = v___x_6346_;
goto v_reusejp_6364_;
}
else
{
lean_object* v_reuseFailAlloc_6368_; 
v_reuseFailAlloc_6368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6368_, 0, v_fst_6344_);
lean_ctor_set(v_reuseFailAlloc_6368_, 1, v___x_6363_);
v___x_6365_ = v_reuseFailAlloc_6368_;
goto v_reusejp_6364_;
}
v_reusejp_6364_:
{
lean_object* v___x_6366_; lean_object* v___f_6367_; 
v___x_6366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6366_, 0, v___x_6365_);
v___f_6367_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6367_, 0, v___x_6366_);
v___y_6316_ = v___f_6367_;
goto v___jp_6315_;
}
}
}
}
else
{
lean_object* v___x_6372_; uint8_t v_isShared_6373_; uint8_t v_isSharedCheck_6443_; 
lean_inc(v_stop_6358_);
lean_inc(v_start_6357_);
lean_inc_ref(v_array_6356_);
v_isSharedCheck_6443_ = !lean_is_exclusive(v_snd_6343_);
if (v_isSharedCheck_6443_ == 0)
{
lean_object* v_unused_6444_; lean_object* v_unused_6445_; lean_object* v_unused_6446_; 
v_unused_6444_ = lean_ctor_get(v_snd_6343_, 2);
lean_dec(v_unused_6444_);
v_unused_6445_ = lean_ctor_get(v_snd_6343_, 1);
lean_dec(v_unused_6445_);
v_unused_6446_ = lean_ctor_get(v_snd_6343_, 0);
lean_dec(v_unused_6446_);
v___x_6372_ = v_snd_6343_;
v_isShared_6373_ = v_isSharedCheck_6443_;
goto v_resetjp_6371_;
}
else
{
lean_dec(v_snd_6343_);
v___x_6372_ = lean_box(0);
v_isShared_6373_ = v_isSharedCheck_6443_;
goto v_resetjp_6371_;
}
v_resetjp_6371_:
{
lean_object* v_array_6374_; lean_object* v_start_6375_; lean_object* v_stop_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6381_; 
v_array_6374_ = lean_ctor_get(v_fst_6352_, 0);
v_start_6375_ = lean_ctor_get(v_fst_6352_, 1);
v_stop_6376_ = lean_ctor_get(v_fst_6352_, 2);
v___x_6377_ = lean_array_fget(v_array_6356_, v_start_6357_);
v___x_6378_ = lean_unsigned_to_nat(1u);
v___x_6379_ = lean_nat_add(v_start_6357_, v___x_6378_);
lean_dec(v_start_6357_);
if (v_isShared_6373_ == 0)
{
lean_ctor_set(v___x_6372_, 1, v___x_6379_);
v___x_6381_ = v___x_6372_;
goto v_reusejp_6380_;
}
else
{
lean_object* v_reuseFailAlloc_6442_; 
v_reuseFailAlloc_6442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6442_, 0, v_array_6356_);
lean_ctor_set(v_reuseFailAlloc_6442_, 1, v___x_6379_);
lean_ctor_set(v_reuseFailAlloc_6442_, 2, v_stop_6358_);
v___x_6381_ = v_reuseFailAlloc_6442_;
goto v_reusejp_6380_;
}
v_reusejp_6380_:
{
uint8_t v___x_6382_; 
v___x_6382_ = lean_nat_dec_lt(v_start_6375_, v_stop_6376_);
if (v___x_6382_ == 0)
{
lean_object* v___x_6384_; 
lean_dec(v___x_6377_);
if (v_isShared_6355_ == 0)
{
lean_ctor_set(v___x_6354_, 1, v___x_6381_);
v___x_6384_ = v___x_6354_;
goto v_reusejp_6383_;
}
else
{
lean_object* v_reuseFailAlloc_6393_; 
v_reuseFailAlloc_6393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6393_, 0, v_fst_6352_);
lean_ctor_set(v_reuseFailAlloc_6393_, 1, v___x_6381_);
v___x_6384_ = v_reuseFailAlloc_6393_;
goto v_reusejp_6383_;
}
v_reusejp_6383_:
{
lean_object* v___x_6386_; 
if (v_isShared_6351_ == 0)
{
lean_ctor_set(v___x_6350_, 1, v___x_6384_);
v___x_6386_ = v___x_6350_;
goto v_reusejp_6385_;
}
else
{
lean_object* v_reuseFailAlloc_6392_; 
v_reuseFailAlloc_6392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6392_, 0, v_fst_6348_);
lean_ctor_set(v_reuseFailAlloc_6392_, 1, v___x_6384_);
v___x_6386_ = v_reuseFailAlloc_6392_;
goto v_reusejp_6385_;
}
v_reusejp_6385_:
{
lean_object* v___x_6388_; 
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 1, v___x_6386_);
v___x_6388_ = v___x_6346_;
goto v_reusejp_6387_;
}
else
{
lean_object* v_reuseFailAlloc_6391_; 
v_reuseFailAlloc_6391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6391_, 0, v_fst_6344_);
lean_ctor_set(v_reuseFailAlloc_6391_, 1, v___x_6386_);
v___x_6388_ = v_reuseFailAlloc_6391_;
goto v_reusejp_6387_;
}
v_reusejp_6387_:
{
lean_object* v___x_6389_; lean_object* v___f_6390_; 
v___x_6389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6389_, 0, v___x_6388_);
v___f_6390_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6390_, 0, v___x_6389_);
v___y_6316_ = v___f_6390_;
goto v___jp_6315_;
}
}
}
}
else
{
lean_object* v___x_6395_; uint8_t v_isShared_6396_; uint8_t v_isSharedCheck_6438_; 
lean_inc(v_stop_6376_);
lean_inc(v_start_6375_);
lean_inc_ref(v_array_6374_);
v_isSharedCheck_6438_ = !lean_is_exclusive(v_fst_6352_);
if (v_isSharedCheck_6438_ == 0)
{
lean_object* v_unused_6439_; lean_object* v_unused_6440_; lean_object* v_unused_6441_; 
v_unused_6439_ = lean_ctor_get(v_fst_6352_, 2);
lean_dec(v_unused_6439_);
v_unused_6440_ = lean_ctor_get(v_fst_6352_, 1);
lean_dec(v_unused_6440_);
v_unused_6441_ = lean_ctor_get(v_fst_6352_, 0);
lean_dec(v_unused_6441_);
v___x_6395_ = v_fst_6352_;
v_isShared_6396_ = v_isSharedCheck_6438_;
goto v_resetjp_6394_;
}
else
{
lean_dec(v_fst_6352_);
v___x_6395_ = lean_box(0);
v_isShared_6396_ = v_isSharedCheck_6438_;
goto v_resetjp_6394_;
}
v_resetjp_6394_:
{
lean_object* v_array_6397_; lean_object* v_start_6398_; lean_object* v_stop_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6403_; 
v_array_6397_ = lean_ctor_get(v_fst_6348_, 0);
v_start_6398_ = lean_ctor_get(v_fst_6348_, 1);
v_stop_6399_ = lean_ctor_get(v_fst_6348_, 2);
v___x_6400_ = lean_array_fget(v_array_6374_, v_start_6375_);
v___x_6401_ = lean_nat_add(v_start_6375_, v___x_6378_);
lean_dec(v_start_6375_);
if (v_isShared_6396_ == 0)
{
lean_ctor_set(v___x_6395_, 1, v___x_6401_);
v___x_6403_ = v___x_6395_;
goto v_reusejp_6402_;
}
else
{
lean_object* v_reuseFailAlloc_6437_; 
v_reuseFailAlloc_6437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6437_, 0, v_array_6374_);
lean_ctor_set(v_reuseFailAlloc_6437_, 1, v___x_6401_);
lean_ctor_set(v_reuseFailAlloc_6437_, 2, v_stop_6376_);
v___x_6403_ = v_reuseFailAlloc_6437_;
goto v_reusejp_6402_;
}
v_reusejp_6402_:
{
uint8_t v___x_6404_; 
v___x_6404_ = lean_nat_dec_lt(v_start_6398_, v_stop_6399_);
if (v___x_6404_ == 0)
{
lean_object* v___x_6406_; 
lean_dec(v___x_6400_);
lean_dec(v___x_6377_);
if (v_isShared_6355_ == 0)
{
lean_ctor_set(v___x_6354_, 1, v___x_6381_);
lean_ctor_set(v___x_6354_, 0, v___x_6403_);
v___x_6406_ = v___x_6354_;
goto v_reusejp_6405_;
}
else
{
lean_object* v_reuseFailAlloc_6415_; 
v_reuseFailAlloc_6415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6415_, 0, v___x_6403_);
lean_ctor_set(v_reuseFailAlloc_6415_, 1, v___x_6381_);
v___x_6406_ = v_reuseFailAlloc_6415_;
goto v_reusejp_6405_;
}
v_reusejp_6405_:
{
lean_object* v___x_6408_; 
if (v_isShared_6351_ == 0)
{
lean_ctor_set(v___x_6350_, 1, v___x_6406_);
v___x_6408_ = v___x_6350_;
goto v_reusejp_6407_;
}
else
{
lean_object* v_reuseFailAlloc_6414_; 
v_reuseFailAlloc_6414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6414_, 0, v_fst_6348_);
lean_ctor_set(v_reuseFailAlloc_6414_, 1, v___x_6406_);
v___x_6408_ = v_reuseFailAlloc_6414_;
goto v_reusejp_6407_;
}
v_reusejp_6407_:
{
lean_object* v___x_6410_; 
if (v_isShared_6347_ == 0)
{
lean_ctor_set(v___x_6346_, 1, v___x_6408_);
v___x_6410_ = v___x_6346_;
goto v_reusejp_6409_;
}
else
{
lean_object* v_reuseFailAlloc_6413_; 
v_reuseFailAlloc_6413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_fst_6344_);
lean_ctor_set(v_reuseFailAlloc_6413_, 1, v___x_6408_);
v___x_6410_ = v_reuseFailAlloc_6413_;
goto v_reusejp_6409_;
}
v_reusejp_6409_:
{
lean_object* v___x_6411_; lean_object* v___f_6412_; 
v___x_6411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6411_, 0, v___x_6410_);
v___f_6412_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6412_, 0, v___x_6411_);
v___y_6316_ = v___f_6412_;
goto v___jp_6315_;
}
}
}
}
else
{
lean_object* v___x_6417_; uint8_t v_isShared_6418_; uint8_t v_isSharedCheck_6433_; 
lean_inc(v_stop_6399_);
lean_inc(v_start_6398_);
lean_inc_ref(v_array_6397_);
lean_del_object(v___x_6354_);
lean_del_object(v___x_6350_);
lean_del_object(v___x_6346_);
v_isSharedCheck_6433_ = !lean_is_exclusive(v_fst_6348_);
if (v_isSharedCheck_6433_ == 0)
{
lean_object* v_unused_6434_; lean_object* v_unused_6435_; lean_object* v_unused_6436_; 
v_unused_6434_ = lean_ctor_get(v_fst_6348_, 2);
lean_dec(v_unused_6434_);
v_unused_6435_ = lean_ctor_get(v_fst_6348_, 1);
lean_dec(v_unused_6435_);
v_unused_6436_ = lean_ctor_get(v_fst_6348_, 0);
lean_dec(v_unused_6436_);
v___x_6417_ = v_fst_6348_;
v_isShared_6418_ = v_isSharedCheck_6433_;
goto v_resetjp_6416_;
}
else
{
lean_dec(v_fst_6348_);
v___x_6417_ = lean_box(0);
v_isShared_6418_ = v_isSharedCheck_6433_;
goto v_resetjp_6416_;
}
v_resetjp_6416_:
{
lean_object* v___f_6419_; uint8_t v___x_6420_; lean_object* v_remaining_x27_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___f_6425_; lean_object* v___x_6426_; lean_object* v___x_6428_; 
v___f_6419_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6420_ = 0;
v_remaining_x27_6421_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6422_ = lean_array_fget_borrowed(v_array_6397_, v_start_6398_);
v___x_6423_ = lean_box(v___x_6420_);
v___x_6424_ = lean_box(v___x_6404_);
lean_inc(v_extraEqualities_6307_);
lean_inc(v_a_6308_);
lean_inc_ref(v_onAlt_6306_);
lean_inc(v___x_6422_);
v___f_6425_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6425_, 0, v___x_6422_);
lean_closure_set(v___f_6425_, 1, v_remaining_x27_6421_);
lean_closure_set(v___f_6425_, 2, v_onAlt_6306_);
lean_closure_set(v___f_6425_, 3, v_a_6308_);
lean_closure_set(v___f_6425_, 4, v___x_6423_);
lean_closure_set(v___f_6425_, 5, v___x_6424_);
lean_closure_set(v___f_6425_, 6, v___f_6419_);
lean_closure_set(v___f_6425_, 7, v_extraEqualities_6307_);
v___x_6426_ = lean_nat_add(v_start_6398_, v___x_6378_);
lean_dec(v_start_6398_);
if (v_isShared_6418_ == 0)
{
lean_ctor_set(v___x_6417_, 1, v___x_6426_);
v___x_6428_ = v___x_6417_;
goto v_reusejp_6427_;
}
else
{
lean_object* v_reuseFailAlloc_6432_; 
v_reuseFailAlloc_6432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6432_, 0, v_array_6397_);
lean_ctor_set(v_reuseFailAlloc_6432_, 1, v___x_6426_);
lean_ctor_set(v_reuseFailAlloc_6432_, 2, v_stop_6399_);
v___x_6428_ = v_reuseFailAlloc_6432_;
goto v_reusejp_6427_;
}
v_reusejp_6427_:
{
lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v___f_6431_; 
v___x_6429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6429_, 0, v___x_6400_);
v___x_6430_ = lean_box(v___x_6420_);
v___f_6431_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6431_, 0, v___x_6377_);
lean_closure_set(v___f_6431_, 1, v___x_6429_);
lean_closure_set(v___f_6431_, 2, v___f_6425_);
lean_closure_set(v___f_6431_, 3, v___x_6430_);
lean_closure_set(v___f_6431_, 4, v_fst_6344_);
lean_closure_set(v___f_6431_, 5, v___x_6403_);
lean_closure_set(v___f_6431_, 6, v___x_6381_);
lean_closure_set(v___f_6431_, 7, v___x_6428_);
v___y_6316_ = v___f_6431_;
goto v___jp_6315_;
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
v___jp_6315_:
{
lean_object* v___x_6317_; 
lean_inc(v___y_6313_);
lean_inc_ref(v___y_6312_);
lean_inc(v___y_6311_);
lean_inc_ref(v___y_6310_);
v___x_6317_ = lean_apply_5(v___y_6316_, v___y_6310_, v___y_6311_, v___y_6312_, v___y_6313_, lean_box(0));
if (lean_obj_tag(v___x_6317_) == 0)
{
lean_object* v_a_6318_; lean_object* v___x_6320_; uint8_t v_isShared_6321_; uint8_t v_isSharedCheck_6330_; 
v_a_6318_ = lean_ctor_get(v___x_6317_, 0);
v_isSharedCheck_6330_ = !lean_is_exclusive(v___x_6317_);
if (v_isSharedCheck_6330_ == 0)
{
v___x_6320_ = v___x_6317_;
v_isShared_6321_ = v_isSharedCheck_6330_;
goto v_resetjp_6319_;
}
else
{
lean_inc(v_a_6318_);
lean_dec(v___x_6317_);
v___x_6320_ = lean_box(0);
v_isShared_6321_ = v_isSharedCheck_6330_;
goto v_resetjp_6319_;
}
v_resetjp_6319_:
{
if (lean_obj_tag(v_a_6318_) == 0)
{
lean_object* v_a_6322_; lean_object* v___x_6324_; 
lean_dec(v_a_6308_);
lean_dec(v_extraEqualities_6307_);
lean_dec_ref(v_onAlt_6306_);
v_a_6322_ = lean_ctor_get(v_a_6318_, 0);
lean_inc(v_a_6322_);
lean_dec_ref_known(v_a_6318_, 1);
if (v_isShared_6321_ == 0)
{
lean_ctor_set(v___x_6320_, 0, v_a_6322_);
v___x_6324_ = v___x_6320_;
goto v_reusejp_6323_;
}
else
{
lean_object* v_reuseFailAlloc_6325_; 
v_reuseFailAlloc_6325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6325_, 0, v_a_6322_);
v___x_6324_ = v_reuseFailAlloc_6325_;
goto v_reusejp_6323_;
}
v_reusejp_6323_:
{
return v___x_6324_;
}
}
else
{
lean_object* v_a_6326_; lean_object* v___x_6327_; lean_object* v___x_6328_; 
lean_del_object(v___x_6320_);
v_a_6326_ = lean_ctor_get(v_a_6318_, 0);
lean_inc(v_a_6326_);
lean_dec_ref_known(v_a_6318_, 1);
v___x_6327_ = lean_unsigned_to_nat(1u);
v___x_6328_ = lean_nat_add(v_a_6308_, v___x_6327_);
lean_dec(v_a_6308_);
v_a_6308_ = v___x_6328_;
v_b_6309_ = v_a_6326_;
goto _start;
}
}
}
else
{
lean_object* v_a_6331_; lean_object* v___x_6333_; uint8_t v_isShared_6334_; uint8_t v_isSharedCheck_6338_; 
lean_dec(v_a_6308_);
lean_dec(v_extraEqualities_6307_);
lean_dec_ref(v_onAlt_6306_);
v_a_6331_ = lean_ctor_get(v___x_6317_, 0);
v_isSharedCheck_6338_ = !lean_is_exclusive(v___x_6317_);
if (v_isSharedCheck_6338_ == 0)
{
v___x_6333_ = v___x_6317_;
v_isShared_6334_ = v_isSharedCheck_6338_;
goto v_resetjp_6332_;
}
else
{
lean_inc(v_a_6331_);
lean_dec(v___x_6317_);
v___x_6333_ = lean_box(0);
v_isShared_6334_ = v_isSharedCheck_6338_;
goto v_resetjp_6332_;
}
v_resetjp_6332_:
{
lean_object* v___x_6336_; 
if (v_isShared_6334_ == 0)
{
v___x_6336_ = v___x_6333_;
goto v_reusejp_6335_;
}
else
{
lean_object* v_reuseFailAlloc_6337_; 
v_reuseFailAlloc_6337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6337_, 0, v_a_6331_);
v___x_6336_ = v_reuseFailAlloc_6337_;
goto v_reusejp_6335_;
}
v_reusejp_6335_:
{
return v___x_6336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6453_, lean_object* v_onAlt_6454_, lean_object* v_extraEqualities_6455_, lean_object* v_a_6456_, lean_object* v_b_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_, lean_object* v___y_6462_){
_start:
{
lean_object* v_res_6463_; 
v_res_6463_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6453_, v_onAlt_6454_, v_extraEqualities_6455_, v_a_6456_, v_b_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_);
lean_dec(v___y_6461_);
lean_dec_ref(v___y_6460_);
lean_dec(v___y_6459_);
lean_dec_ref(v___y_6458_);
lean_dec(v_upperBound_6453_);
return v_res_6463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6464_, size_t v_sz_6465_, size_t v_i_6466_, lean_object* v_bs_6467_, lean_object* v___y_6468_, lean_object* v___y_6469_, lean_object* v___y_6470_, lean_object* v___y_6471_){
_start:
{
uint8_t v___x_6473_; 
v___x_6473_ = lean_usize_dec_lt(v_i_6466_, v_sz_6465_);
if (v___x_6473_ == 0)
{
lean_object* v___x_6474_; 
lean_dec_ref(v_onParams_6464_);
v___x_6474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6474_, 0, v_bs_6467_);
return v___x_6474_;
}
else
{
lean_object* v_v_6475_; lean_object* v___x_6476_; lean_object* v_bs_x27_6477_; lean_object* v___x_6478_; 
v_v_6475_ = lean_array_uget(v_bs_6467_, v_i_6466_);
v___x_6476_ = lean_unsigned_to_nat(0u);
v_bs_x27_6477_ = lean_array_uset(v_bs_6467_, v_i_6466_, v___x_6476_);
lean_inc_ref(v_onParams_6464_);
lean_inc(v___y_6471_);
lean_inc_ref(v___y_6470_);
lean_inc(v___y_6469_);
lean_inc_ref(v___y_6468_);
v___x_6478_ = lean_apply_6(v_onParams_6464_, v_v_6475_, v___y_6468_, v___y_6469_, v___y_6470_, v___y_6471_, lean_box(0));
if (lean_obj_tag(v___x_6478_) == 0)
{
lean_object* v_a_6479_; size_t v___x_6480_; size_t v___x_6481_; lean_object* v___x_6482_; 
v_a_6479_ = lean_ctor_get(v___x_6478_, 0);
lean_inc(v_a_6479_);
lean_dec_ref_known(v___x_6478_, 1);
v___x_6480_ = ((size_t)1ULL);
v___x_6481_ = lean_usize_add(v_i_6466_, v___x_6480_);
v___x_6482_ = lean_array_uset(v_bs_x27_6477_, v_i_6466_, v_a_6479_);
v_i_6466_ = v___x_6481_;
v_bs_6467_ = v___x_6482_;
goto _start;
}
else
{
lean_object* v_a_6484_; lean_object* v___x_6486_; uint8_t v_isShared_6487_; uint8_t v_isSharedCheck_6491_; 
lean_dec_ref(v_bs_x27_6477_);
lean_dec_ref(v_onParams_6464_);
v_a_6484_ = lean_ctor_get(v___x_6478_, 0);
v_isSharedCheck_6491_ = !lean_is_exclusive(v___x_6478_);
if (v_isSharedCheck_6491_ == 0)
{
v___x_6486_ = v___x_6478_;
v_isShared_6487_ = v_isSharedCheck_6491_;
goto v_resetjp_6485_;
}
else
{
lean_inc(v_a_6484_);
lean_dec(v___x_6478_);
v___x_6486_ = lean_box(0);
v_isShared_6487_ = v_isSharedCheck_6491_;
goto v_resetjp_6485_;
}
v_resetjp_6485_:
{
lean_object* v___x_6489_; 
if (v_isShared_6487_ == 0)
{
v___x_6489_ = v___x_6486_;
goto v_reusejp_6488_;
}
else
{
lean_object* v_reuseFailAlloc_6490_; 
v_reuseFailAlloc_6490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6490_, 0, v_a_6484_);
v___x_6489_ = v_reuseFailAlloc_6490_;
goto v_reusejp_6488_;
}
v_reusejp_6488_:
{
return v___x_6489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6492_, lean_object* v_sz_6493_, lean_object* v_i_6494_, lean_object* v_bs_6495_, lean_object* v___y_6496_, lean_object* v___y_6497_, lean_object* v___y_6498_, lean_object* v___y_6499_, lean_object* v___y_6500_){
_start:
{
size_t v_sz_boxed_6501_; size_t v_i_boxed_6502_; lean_object* v_res_6503_; 
v_sz_boxed_6501_ = lean_unbox_usize(v_sz_6493_);
lean_dec(v_sz_6493_);
v_i_boxed_6502_ = lean_unbox_usize(v_i_6494_);
lean_dec(v_i_6494_);
v_res_6503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6492_, v_sz_boxed_6501_, v_i_boxed_6502_, v_bs_6495_, v___y_6496_, v___y_6497_, v___y_6498_, v___y_6499_);
lean_dec(v___y_6499_);
lean_dec_ref(v___y_6498_);
lean_dec(v___y_6497_);
lean_dec_ref(v___y_6496_);
return v_res_6503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6504_, lean_object* v___y_6505_){
_start:
{
lean_object* v___x_6507_; lean_object* v_env_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; 
v___x_6507_ = lean_st_ref_get(v___y_6505_);
v_env_6508_ = lean_ctor_get(v___x_6507_, 0);
lean_inc_ref(v_env_6508_);
lean_dec(v___x_6507_);
v___x_6509_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6508_, v_declName_6504_);
v___x_6510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6510_, 0, v___x_6509_);
return v___x_6510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_){
_start:
{
lean_object* v_res_6514_; 
v_res_6514_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6511_, v___y_6512_);
lean_dec(v___y_6512_);
return v_res_6514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6517_, uint8_t v_useSplitter_6518_, uint8_t v_addEqualities_6519_, lean_object* v_onParams_6520_, lean_object* v_onMotive_6521_, lean_object* v_onAlt_6522_, lean_object* v_onRemaining_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_){
_start:
{
lean_object* v___x_6529_; lean_object* v_env_6530_; lean_object* v_toMatcherInfo_6531_; lean_object* v_matcherName_6532_; lean_object* v_matcherLevels_6533_; lean_object* v_params_6534_; lean_object* v_motive_6535_; lean_object* v_discrs_6536_; lean_object* v_alts_6537_; lean_object* v_remaining_6538_; lean_object* v___y_6540_; lean_object* v___y_6541_; lean_object* v___y_6542_; lean_object* v___y_6543_; lean_object* v___y_6544_; lean_object* v___y_6545_; lean_object* v___y_6546_; lean_object* v___y_6547_; lean_object* v___y_6548_; lean_object* v___y_6549_; lean_object* v___y_6550_; lean_object* v___y_6551_; lean_object* v___y_6552_; uint8_t v_isCasesOn_6637_; lean_object* v___y_6639_; lean_object* v___y_6640_; lean_object* v___y_6641_; lean_object* v___y_6642_; lean_object* v___y_6643_; lean_object* v___y_6644_; size_t v___y_6645_; lean_object* v_matcherLevels_6646_; lean_object* v___y_6647_; lean_object* v___y_6648_; lean_object* v___y_6649_; lean_object* v___y_6650_; lean_object* v_numDiscrEqs_6844_; lean_object* v___y_6845_; lean_object* v___y_6846_; lean_object* v___y_6847_; lean_object* v___y_6848_; 
v___x_6529_ = lean_st_ref_get(v___y_6527_);
v_env_6530_ = lean_ctor_get(v___x_6529_, 0);
lean_inc_ref(v_env_6530_);
lean_dec(v___x_6529_);
v_toMatcherInfo_6531_ = lean_ctor_get(v_matcherApp_6517_, 0);
lean_inc_ref(v_toMatcherInfo_6531_);
v_matcherName_6532_ = lean_ctor_get(v_matcherApp_6517_, 1);
lean_inc_n(v_matcherName_6532_, 2);
v_matcherLevels_6533_ = lean_ctor_get(v_matcherApp_6517_, 2);
v_params_6534_ = lean_ctor_get(v_matcherApp_6517_, 3);
v_motive_6535_ = lean_ctor_get(v_matcherApp_6517_, 4);
v_discrs_6536_ = lean_ctor_get(v_matcherApp_6517_, 5);
v_alts_6537_ = lean_ctor_get(v_matcherApp_6517_, 6);
lean_inc_ref(v_alts_6537_);
v_remaining_6538_ = lean_ctor_get(v_matcherApp_6517_, 7);
lean_inc_ref(v_remaining_6538_);
v_isCasesOn_6637_ = l_Lean_isCasesOnRecursor(v_env_6530_, v_matcherName_6532_);
if (v_isCasesOn_6637_ == 0)
{
lean_object* v___x_6898_; lean_object* v_a_6899_; 
lean_inc(v_matcherName_6532_);
v___x_6898_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6532_, v___y_6527_);
v_a_6899_ = lean_ctor_get(v___x_6898_, 0);
lean_inc(v_a_6899_);
lean_dec_ref(v___x_6898_);
if (lean_obj_tag(v_a_6899_) == 0)
{
lean_object* v___x_6900_; lean_object* v___x_6901_; lean_object* v___x_6902_; lean_object* v___x_6903_; lean_object* v___x_6904_; lean_object* v___x_6905_; lean_object* v_a_6906_; lean_object* v___x_6908_; uint8_t v_isShared_6909_; uint8_t v_isSharedCheck_6913_; 
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
lean_dec_ref(v_onMotive_6521_);
lean_dec_ref(v_onParams_6520_);
lean_dec_ref(v_matcherApp_6517_);
v___x_6900_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6901_ = l_Lean_MessageData_ofName(v_matcherName_6532_);
v___x_6902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6902_, 0, v___x_6900_);
lean_ctor_set(v___x_6902_, 1, v___x_6901_);
v___x_6903_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6904_, 0, v___x_6902_);
lean_ctor_set(v___x_6904_, 1, v___x_6903_);
v___x_6905_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6904_, v___y_6524_, v___y_6525_, v___y_6526_, v___y_6527_);
v_a_6906_ = lean_ctor_get(v___x_6905_, 0);
v_isSharedCheck_6913_ = !lean_is_exclusive(v___x_6905_);
if (v_isSharedCheck_6913_ == 0)
{
v___x_6908_ = v___x_6905_;
v_isShared_6909_ = v_isSharedCheck_6913_;
goto v_resetjp_6907_;
}
else
{
lean_inc(v_a_6906_);
lean_dec(v___x_6905_);
v___x_6908_ = lean_box(0);
v_isShared_6909_ = v_isSharedCheck_6913_;
goto v_resetjp_6907_;
}
v_resetjp_6907_:
{
lean_object* v___x_6911_; 
if (v_isShared_6909_ == 0)
{
v___x_6911_ = v___x_6908_;
goto v_reusejp_6910_;
}
else
{
lean_object* v_reuseFailAlloc_6912_; 
v_reuseFailAlloc_6912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6912_, 0, v_a_6906_);
v___x_6911_ = v_reuseFailAlloc_6912_;
goto v_reusejp_6910_;
}
v_reusejp_6910_:
{
return v___x_6911_;
}
}
}
else
{
lean_object* v_val_6914_; lean_object* v___x_6915_; 
v_val_6914_ = lean_ctor_get(v_a_6899_, 0);
lean_inc(v_val_6914_);
lean_dec_ref_known(v_a_6899_, 1);
v___x_6915_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6914_);
lean_dec(v_val_6914_);
v_numDiscrEqs_6844_ = v___x_6915_;
v___y_6845_ = v___y_6524_;
v___y_6846_ = v___y_6525_;
v___y_6847_ = v___y_6526_;
v___y_6848_ = v___y_6527_;
goto v___jp_6843_;
}
}
else
{
lean_object* v___x_6916_; 
v___x_6916_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6844_ = v___x_6916_;
v___y_6845_ = v___y_6524_;
v___y_6846_ = v___y_6525_;
v___y_6847_ = v___y_6526_;
v___y_6848_ = v___y_6527_;
goto v___jp_6843_;
}
v___jp_6539_:
{
lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v_aux_6555_; lean_object* v_aux_6556_; lean_object* v_aux_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___f_6561_; uint8_t v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; 
lean_inc_ref(v___y_6544_);
v___x_6553_ = lean_array_to_list(v___y_6544_);
lean_inc(v_matcherName_6532_);
v___x_6554_ = l_Lean_mkConst(v_matcherName_6532_, v___x_6553_);
v_aux_6555_ = l_Lean_mkAppN(v___x_6554_, v___y_6550_);
lean_inc_ref(v___y_6551_);
v_aux_6556_ = l_Lean_Expr_app___override(v_aux_6555_, v___y_6551_);
v_aux_6557_ = l_Lean_mkAppN(v_aux_6556_, v___y_6546_);
v___x_6558_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6557_, 2);
v___x_6559_ = l_Lean_indentExpr(v_aux_6557_);
v___x_6560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6560_, 0, v___x_6558_);
lean_ctor_set(v___x_6560_, 1, v___x_6559_);
v___f_6561_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6561_, 0, v___x_6560_);
v___x_6562_ = 0;
v___x_6563_ = lean_box(v___x_6562_);
v___x_6564_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6564_, 0, v_aux_6557_);
lean_closure_set(v___x_6564_, 1, v___x_6563_);
v___x_6565_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6564_, v___f_6561_, v___y_6542_, v___y_6548_, v___y_6545_, v___y_6540_);
if (lean_obj_tag(v___x_6565_) == 0)
{
lean_object* v___x_6566_; lean_object* v___x_6567_; 
lean_dec_ref_known(v___x_6565_, 1);
v___x_6566_ = lean_array_get_size(v_alts_6537_);
v___x_6567_ = l_Lean_Meta_inferArgumentTypesN(v___x_6566_, v_aux_6557_, v___y_6542_, v___y_6548_, v___y_6545_, v___y_6540_);
if (lean_obj_tag(v___x_6567_) == 0)
{
lean_object* v_a_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; lean_object* v___x_6574_; lean_object* v___x_6575_; lean_object* v___x_6576_; lean_object* v___x_6577_; lean_object* v___x_6578_; 
v_a_6568_ = lean_ctor_get(v___x_6567_, 0);
lean_inc(v_a_6568_);
lean_dec_ref_known(v___x_6567_, 1);
v___x_6569_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6517_);
v___x_6570_ = lean_array_get_size(v___x_6569_);
v___x_6571_ = lean_array_get_size(v_a_6568_);
lean_inc_n(v___y_6543_, 3);
v___x_6572_ = l_Array_toSubarray___redArg(v_alts_6537_, v___y_6543_, v___x_6566_);
v___x_6573_ = l_Array_toSubarray___redArg(v___x_6569_, v___y_6543_, v___x_6570_);
v___x_6574_ = l_Array_toSubarray___redArg(v_a_6568_, v___y_6543_, v___x_6571_);
v___x_6575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6575_, 0, v___x_6573_);
lean_ctor_set(v___x_6575_, 1, v___x_6574_);
v___x_6576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6576_, 0, v___x_6572_);
lean_ctor_set(v___x_6576_, 1, v___x_6575_);
lean_inc_ref(v___y_6541_);
v___x_6577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6577_, 0, v___y_6541_);
lean_ctor_set(v___x_6577_, 1, v___x_6576_);
v___x_6578_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6566_, v_onAlt_6522_, v___y_6552_, v___y_6543_, v___x_6577_, v___y_6542_, v___y_6548_, v___y_6545_, v___y_6540_);
if (lean_obj_tag(v___x_6578_) == 0)
{
lean_object* v_a_6579_; lean_object* v_fst_6580_; lean_object* v___x_6581_; 
v_a_6579_ = lean_ctor_get(v___x_6578_, 0);
lean_inc(v_a_6579_);
lean_dec_ref_known(v___x_6578_, 1);
v_fst_6580_ = lean_ctor_get(v_a_6579_, 0);
lean_inc(v_fst_6580_);
lean_dec(v_a_6579_);
lean_inc(v___y_6540_);
lean_inc_ref(v___y_6545_);
lean_inc(v___y_6548_);
lean_inc_ref(v___y_6542_);
v___x_6581_ = lean_apply_6(v_onRemaining_6523_, v_remaining_6538_, v___y_6542_, v___y_6548_, v___y_6545_, v___y_6540_, lean_box(0));
if (lean_obj_tag(v___x_6581_) == 0)
{
lean_object* v_a_6582_; lean_object* v___x_6584_; uint8_t v_isShared_6585_; uint8_t v_isSharedCheck_6604_; 
v_a_6582_ = lean_ctor_get(v___x_6581_, 0);
v_isSharedCheck_6604_ = !lean_is_exclusive(v___x_6581_);
if (v_isSharedCheck_6604_ == 0)
{
v___x_6584_ = v___x_6581_;
v_isShared_6585_ = v_isSharedCheck_6604_;
goto v_resetjp_6583_;
}
else
{
lean_inc(v_a_6582_);
lean_dec(v___x_6581_);
v___x_6584_ = lean_box(0);
v_isShared_6585_ = v_isSharedCheck_6604_;
goto v_resetjp_6583_;
}
v_resetjp_6583_:
{
lean_object* v_numParams_6586_; lean_object* v_numDiscrs_6587_; lean_object* v_altInfos_6588_; lean_object* v_uElimPos_x3f_6589_; lean_object* v_overlaps_6590_; lean_object* v___x_6592_; uint8_t v_isShared_6593_; uint8_t v_isSharedCheck_6602_; 
v_numParams_6586_ = lean_ctor_get(v_toMatcherInfo_6531_, 0);
v_numDiscrs_6587_ = lean_ctor_get(v_toMatcherInfo_6531_, 1);
v_altInfos_6588_ = lean_ctor_get(v_toMatcherInfo_6531_, 2);
v_uElimPos_x3f_6589_ = lean_ctor_get(v_toMatcherInfo_6531_, 3);
v_overlaps_6590_ = lean_ctor_get(v_toMatcherInfo_6531_, 5);
v_isSharedCheck_6602_ = !lean_is_exclusive(v_toMatcherInfo_6531_);
if (v_isSharedCheck_6602_ == 0)
{
lean_object* v_unused_6603_; 
v_unused_6603_ = lean_ctor_get(v_toMatcherInfo_6531_, 4);
lean_dec(v_unused_6603_);
v___x_6592_ = v_toMatcherInfo_6531_;
v_isShared_6593_ = v_isSharedCheck_6602_;
goto v_resetjp_6591_;
}
else
{
lean_inc(v_overlaps_6590_);
lean_inc(v_uElimPos_x3f_6589_);
lean_inc(v_altInfos_6588_);
lean_inc(v_numDiscrs_6587_);
lean_inc(v_numParams_6586_);
lean_dec(v_toMatcherInfo_6531_);
v___x_6592_ = lean_box(0);
v_isShared_6593_ = v_isSharedCheck_6602_;
goto v_resetjp_6591_;
}
v_resetjp_6591_:
{
lean_object* v_remaining_x27_6594_; lean_object* v___x_6596_; 
v_remaining_x27_6594_ = l_Array_append___redArg(v___y_6547_, v_a_6582_);
lean_dec(v_a_6582_);
if (v_isShared_6593_ == 0)
{
lean_ctor_set(v___x_6592_, 4, v___y_6549_);
v___x_6596_ = v___x_6592_;
goto v_reusejp_6595_;
}
else
{
lean_object* v_reuseFailAlloc_6601_; 
v_reuseFailAlloc_6601_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6601_, 0, v_numParams_6586_);
lean_ctor_set(v_reuseFailAlloc_6601_, 1, v_numDiscrs_6587_);
lean_ctor_set(v_reuseFailAlloc_6601_, 2, v_altInfos_6588_);
lean_ctor_set(v_reuseFailAlloc_6601_, 3, v_uElimPos_x3f_6589_);
lean_ctor_set(v_reuseFailAlloc_6601_, 4, v___y_6549_);
lean_ctor_set(v_reuseFailAlloc_6601_, 5, v_overlaps_6590_);
v___x_6596_ = v_reuseFailAlloc_6601_;
goto v_reusejp_6595_;
}
v_reusejp_6595_:
{
lean_object* v___x_6597_; lean_object* v___x_6599_; 
v___x_6597_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6597_, 0, v___x_6596_);
lean_ctor_set(v___x_6597_, 1, v_matcherName_6532_);
lean_ctor_set(v___x_6597_, 2, v___y_6544_);
lean_ctor_set(v___x_6597_, 3, v___y_6550_);
lean_ctor_set(v___x_6597_, 4, v___y_6551_);
lean_ctor_set(v___x_6597_, 5, v___y_6546_);
lean_ctor_set(v___x_6597_, 6, v_fst_6580_);
lean_ctor_set(v___x_6597_, 7, v_remaining_x27_6594_);
if (v_isShared_6585_ == 0)
{
lean_ctor_set(v___x_6584_, 0, v___x_6597_);
v___x_6599_ = v___x_6584_;
goto v_reusejp_6598_;
}
else
{
lean_object* v_reuseFailAlloc_6600_; 
v_reuseFailAlloc_6600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6600_, 0, v___x_6597_);
v___x_6599_ = v_reuseFailAlloc_6600_;
goto v_reusejp_6598_;
}
v_reusejp_6598_:
{
return v___x_6599_;
}
}
}
}
}
else
{
lean_object* v_a_6605_; lean_object* v___x_6607_; uint8_t v_isShared_6608_; uint8_t v_isSharedCheck_6612_; 
lean_dec(v_fst_6580_);
lean_dec_ref(v___y_6551_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6549_);
lean_dec(v___y_6547_);
lean_dec_ref(v___y_6546_);
lean_dec_ref(v___y_6544_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
v_a_6605_ = lean_ctor_get(v___x_6581_, 0);
v_isSharedCheck_6612_ = !lean_is_exclusive(v___x_6581_);
if (v_isSharedCheck_6612_ == 0)
{
v___x_6607_ = v___x_6581_;
v_isShared_6608_ = v_isSharedCheck_6612_;
goto v_resetjp_6606_;
}
else
{
lean_inc(v_a_6605_);
lean_dec(v___x_6581_);
v___x_6607_ = lean_box(0);
v_isShared_6608_ = v_isSharedCheck_6612_;
goto v_resetjp_6606_;
}
v_resetjp_6606_:
{
lean_object* v___x_6610_; 
if (v_isShared_6608_ == 0)
{
v___x_6610_ = v___x_6607_;
goto v_reusejp_6609_;
}
else
{
lean_object* v_reuseFailAlloc_6611_; 
v_reuseFailAlloc_6611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6611_, 0, v_a_6605_);
v___x_6610_ = v_reuseFailAlloc_6611_;
goto v_reusejp_6609_;
}
v_reusejp_6609_:
{
return v___x_6610_;
}
}
}
}
else
{
lean_object* v_a_6613_; lean_object* v___x_6615_; uint8_t v_isShared_6616_; uint8_t v_isSharedCheck_6620_; 
lean_dec_ref(v___y_6551_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6549_);
lean_dec(v___y_6547_);
lean_dec_ref(v___y_6546_);
lean_dec_ref(v___y_6544_);
lean_dec_ref(v_remaining_6538_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
v_a_6613_ = lean_ctor_get(v___x_6578_, 0);
v_isSharedCheck_6620_ = !lean_is_exclusive(v___x_6578_);
if (v_isSharedCheck_6620_ == 0)
{
v___x_6615_ = v___x_6578_;
v_isShared_6616_ = v_isSharedCheck_6620_;
goto v_resetjp_6614_;
}
else
{
lean_inc(v_a_6613_);
lean_dec(v___x_6578_);
v___x_6615_ = lean_box(0);
v_isShared_6616_ = v_isSharedCheck_6620_;
goto v_resetjp_6614_;
}
v_resetjp_6614_:
{
lean_object* v___x_6618_; 
if (v_isShared_6616_ == 0)
{
v___x_6618_ = v___x_6615_;
goto v_reusejp_6617_;
}
else
{
lean_object* v_reuseFailAlloc_6619_; 
v_reuseFailAlloc_6619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6619_, 0, v_a_6613_);
v___x_6618_ = v_reuseFailAlloc_6619_;
goto v_reusejp_6617_;
}
v_reusejp_6617_:
{
return v___x_6618_;
}
}
}
}
else
{
lean_object* v_a_6621_; lean_object* v___x_6623_; uint8_t v_isShared_6624_; uint8_t v_isSharedCheck_6628_; 
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6549_);
lean_dec(v___y_6547_);
lean_dec_ref(v___y_6546_);
lean_dec_ref(v___y_6544_);
lean_dec(v___y_6543_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
lean_dec_ref(v_matcherApp_6517_);
v_a_6621_ = lean_ctor_get(v___x_6567_, 0);
v_isSharedCheck_6628_ = !lean_is_exclusive(v___x_6567_);
if (v_isSharedCheck_6628_ == 0)
{
v___x_6623_ = v___x_6567_;
v_isShared_6624_ = v_isSharedCheck_6628_;
goto v_resetjp_6622_;
}
else
{
lean_inc(v_a_6621_);
lean_dec(v___x_6567_);
v___x_6623_ = lean_box(0);
v_isShared_6624_ = v_isSharedCheck_6628_;
goto v_resetjp_6622_;
}
v_resetjp_6622_:
{
lean_object* v___x_6626_; 
if (v_isShared_6624_ == 0)
{
v___x_6626_ = v___x_6623_;
goto v_reusejp_6625_;
}
else
{
lean_object* v_reuseFailAlloc_6627_; 
v_reuseFailAlloc_6627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6627_, 0, v_a_6621_);
v___x_6626_ = v_reuseFailAlloc_6627_;
goto v_reusejp_6625_;
}
v_reusejp_6625_:
{
return v___x_6626_;
}
}
}
}
else
{
lean_object* v_a_6629_; lean_object* v___x_6631_; uint8_t v_isShared_6632_; uint8_t v_isSharedCheck_6636_; 
lean_dec_ref(v_aux_6557_);
lean_dec(v___y_6552_);
lean_dec_ref(v___y_6551_);
lean_dec_ref(v___y_6550_);
lean_dec_ref(v___y_6549_);
lean_dec(v___y_6547_);
lean_dec_ref(v___y_6546_);
lean_dec_ref(v___y_6544_);
lean_dec(v___y_6543_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
lean_dec_ref(v_matcherApp_6517_);
v_a_6629_ = lean_ctor_get(v___x_6565_, 0);
v_isSharedCheck_6636_ = !lean_is_exclusive(v___x_6565_);
if (v_isSharedCheck_6636_ == 0)
{
v___x_6631_ = v___x_6565_;
v_isShared_6632_ = v_isSharedCheck_6636_;
goto v_resetjp_6630_;
}
else
{
lean_inc(v_a_6629_);
lean_dec(v___x_6565_);
v___x_6631_ = lean_box(0);
v_isShared_6632_ = v_isSharedCheck_6636_;
goto v_resetjp_6630_;
}
v_resetjp_6630_:
{
lean_object* v___x_6634_; 
if (v_isShared_6632_ == 0)
{
v___x_6634_ = v___x_6631_;
goto v_reusejp_6633_;
}
else
{
lean_object* v_reuseFailAlloc_6635_; 
v_reuseFailAlloc_6635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6635_, 0, v_a_6629_);
v___x_6634_ = v_reuseFailAlloc_6635_;
goto v_reusejp_6633_;
}
v_reusejp_6633_:
{
return v___x_6634_;
}
}
}
}
v___jp_6638_:
{
lean_object* v___x_6651_; lean_object* v_remaining_x27_6652_; lean_object* v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; lean_object* v___x_6658_; size_t v_sz_6659_; lean_object* v___x_6660_; 
v___x_6651_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6652_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6653_ = l_Array_reverse___redArg(v___y_6640_);
v___x_6654_ = lean_array_get_size(v___x_6653_);
v___x_6655_ = l_Array_toSubarray___redArg(v___x_6653_, v___x_6651_, v___x_6654_);
lean_inc_ref(v___y_6639_);
v___x_6656_ = l_Array_reverse___redArg(v___y_6639_);
v___x_6657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6657_, 0, v___x_6651_);
lean_ctor_set(v___x_6657_, 1, v___x_6655_);
v___x_6658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6658_, 0, v_remaining_x27_6652_);
lean_ctor_set(v___x_6658_, 1, v___x_6657_);
v_sz_6659_ = lean_array_size(v___x_6656_);
v___x_6660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6656_, v_sz_6659_, v___y_6645_, v___x_6658_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
lean_dec_ref(v___x_6656_);
if (lean_obj_tag(v___x_6660_) == 0)
{
lean_object* v_a_6661_; lean_object* v_snd_6662_; 
v_a_6661_ = lean_ctor_get(v___x_6660_, 0);
lean_inc(v_a_6661_);
lean_dec_ref_known(v___x_6660_, 1);
v_snd_6662_ = lean_ctor_get(v_a_6661_, 1);
lean_inc(v_snd_6662_);
if (v_useSplitter_6518_ == 0)
{
lean_object* v_fst_6663_; lean_object* v_fst_6664_; 
lean_dec(v___y_6644_);
v_fst_6663_ = lean_ctor_get(v_a_6661_, 0);
lean_inc(v_fst_6663_);
lean_dec(v_a_6661_);
v_fst_6664_ = lean_ctor_get(v_snd_6662_, 0);
lean_inc(v_fst_6664_);
lean_dec(v_snd_6662_);
v___y_6540_ = v___y_6650_;
v___y_6541_ = v_remaining_x27_6652_;
v___y_6542_ = v___y_6647_;
v___y_6543_ = v___x_6651_;
v___y_6544_ = v_matcherLevels_6646_;
v___y_6545_ = v___y_6649_;
v___y_6546_ = v___y_6639_;
v___y_6547_ = v_fst_6663_;
v___y_6548_ = v___y_6648_;
v___y_6549_ = v___y_6641_;
v___y_6550_ = v___y_6643_;
v___y_6551_ = v___y_6642_;
v___y_6552_ = v_fst_6664_;
goto v___jp_6539_;
}
else
{
if (v_isCasesOn_6637_ == 0)
{
lean_object* v___x_6666_; uint8_t v_isShared_6667_; uint8_t v_isSharedCheck_6824_; 
v_isSharedCheck_6824_ = !lean_is_exclusive(v_matcherApp_6517_);
if (v_isSharedCheck_6824_ == 0)
{
lean_object* v_unused_6825_; lean_object* v_unused_6826_; lean_object* v_unused_6827_; lean_object* v_unused_6828_; lean_object* v_unused_6829_; lean_object* v_unused_6830_; lean_object* v_unused_6831_; lean_object* v_unused_6832_; 
v_unused_6825_ = lean_ctor_get(v_matcherApp_6517_, 7);
lean_dec(v_unused_6825_);
v_unused_6826_ = lean_ctor_get(v_matcherApp_6517_, 6);
lean_dec(v_unused_6826_);
v_unused_6827_ = lean_ctor_get(v_matcherApp_6517_, 5);
lean_dec(v_unused_6827_);
v_unused_6828_ = lean_ctor_get(v_matcherApp_6517_, 4);
lean_dec(v_unused_6828_);
v_unused_6829_ = lean_ctor_get(v_matcherApp_6517_, 3);
lean_dec(v_unused_6829_);
v_unused_6830_ = lean_ctor_get(v_matcherApp_6517_, 2);
lean_dec(v_unused_6830_);
v_unused_6831_ = lean_ctor_get(v_matcherApp_6517_, 1);
lean_dec(v_unused_6831_);
v_unused_6832_ = lean_ctor_get(v_matcherApp_6517_, 0);
lean_dec(v_unused_6832_);
v___x_6666_ = v_matcherApp_6517_;
v_isShared_6667_ = v_isSharedCheck_6824_;
goto v_resetjp_6665_;
}
else
{
lean_dec(v_matcherApp_6517_);
v___x_6666_ = lean_box(0);
v_isShared_6667_ = v_isSharedCheck_6824_;
goto v_resetjp_6665_;
}
v_resetjp_6665_:
{
lean_object* v_fst_6668_; lean_object* v___x_6670_; uint8_t v_isShared_6671_; uint8_t v_isSharedCheck_6822_; 
v_fst_6668_ = lean_ctor_get(v_a_6661_, 0);
v_isSharedCheck_6822_ = !lean_is_exclusive(v_a_6661_);
if (v_isSharedCheck_6822_ == 0)
{
lean_object* v_unused_6823_; 
v_unused_6823_ = lean_ctor_get(v_a_6661_, 1);
lean_dec(v_unused_6823_);
v___x_6670_ = v_a_6661_;
v_isShared_6671_ = v_isSharedCheck_6822_;
goto v_resetjp_6669_;
}
else
{
lean_inc(v_fst_6668_);
lean_dec(v_a_6661_);
v___x_6670_ = lean_box(0);
v_isShared_6671_ = v_isSharedCheck_6822_;
goto v_resetjp_6669_;
}
v_resetjp_6669_:
{
lean_object* v_fst_6672_; lean_object* v___x_6674_; uint8_t v_isShared_6675_; uint8_t v_isSharedCheck_6820_; 
v_fst_6672_ = lean_ctor_get(v_snd_6662_, 0);
v_isSharedCheck_6820_ = !lean_is_exclusive(v_snd_6662_);
if (v_isSharedCheck_6820_ == 0)
{
lean_object* v_unused_6821_; 
v_unused_6821_ = lean_ctor_get(v_snd_6662_, 1);
lean_dec(v_unused_6821_);
v___x_6674_ = v_snd_6662_;
v_isShared_6675_ = v_isSharedCheck_6820_;
goto v_resetjp_6673_;
}
else
{
lean_inc(v_fst_6672_);
lean_dec(v_snd_6662_);
v___x_6674_ = lean_box(0);
v_isShared_6675_ = v_isSharedCheck_6820_;
goto v_resetjp_6673_;
}
v_resetjp_6673_:
{
lean_object* v___x_6676_; lean_object* v___x_6677_; lean_object* v_aux1_6678_; lean_object* v_aux1_6679_; lean_object* v_aux1_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___f_6686_; uint8_t v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
lean_inc_ref(v_matcherLevels_6646_);
v___x_6676_ = lean_array_to_list(v_matcherLevels_6646_);
lean_inc(v___x_6676_);
lean_inc(v_matcherName_6532_);
v___x_6677_ = l_Lean_mkConst(v_matcherName_6532_, v___x_6676_);
v_aux1_6678_ = l_Lean_mkAppN(v___x_6677_, v___y_6643_);
lean_inc_ref(v___y_6642_);
v_aux1_6679_ = l_Lean_Expr_app___override(v_aux1_6678_, v___y_6642_);
v_aux1_6680_ = l_Lean_mkAppN(v_aux1_6679_, v___y_6639_);
v___x_6681_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6680_, 2);
v___x_6682_ = l_Lean_indentExpr(v_aux1_6680_);
v___x_6683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6683_, 0, v___x_6681_);
lean_ctor_set(v___x_6683_, 1, v___x_6682_);
v___x_6684_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6685_, 0, v___x_6683_);
lean_ctor_set(v___x_6685_, 1, v___x_6684_);
v___f_6686_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6686_, 0, v___x_6685_);
v___x_6687_ = 0;
v___x_6688_ = lean_box(v___x_6687_);
v___x_6689_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6689_, 0, v_aux1_6680_);
lean_closure_set(v___x_6689_, 1, v___x_6688_);
v___x_6690_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6689_, v___f_6686_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
if (lean_obj_tag(v___x_6690_) == 0)
{
lean_object* v___x_6691_; lean_object* v___x_6692_; 
lean_dec_ref_known(v___x_6690_, 1);
v___x_6691_ = lean_array_get_size(v_alts_6537_);
v___x_6692_ = l_Lean_Meta_inferArgumentTypesN(v___x_6691_, v_aux1_6680_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
if (lean_obj_tag(v___x_6692_) == 0)
{
lean_object* v_a_6693_; lean_object* v___x_6694_; 
v_a_6693_ = lean_ctor_get(v___x_6692_, 0);
lean_inc(v_a_6693_);
lean_dec_ref_known(v___x_6692_, 1);
lean_inc(v___y_6650_);
lean_inc_ref(v___y_6649_);
lean_inc(v___y_6648_);
lean_inc_ref(v___y_6647_);
v___x_6694_ = lean_get_match_equations_for(v_matcherName_6532_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
if (lean_obj_tag(v___x_6694_) == 0)
{
lean_object* v_a_6695_; lean_object* v_splitterName_6696_; lean_object* v_splitterMatchInfo_6697_; lean_object* v___x_6698_; lean_object* v_aux2_6699_; lean_object* v_aux2_6700_; lean_object* v_aux2_6701_; lean_object* v___x_6702_; lean_object* v___x_6703_; lean_object* v___x_6704_; lean_object* v___x_6705_; lean_object* v___f_6706_; lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; 
v_a_6695_ = lean_ctor_get(v___x_6694_, 0);
lean_inc(v_a_6695_);
lean_dec_ref_known(v___x_6694_, 1);
v_splitterName_6696_ = lean_ctor_get(v_a_6695_, 1);
lean_inc_n(v_splitterName_6696_, 2);
v_splitterMatchInfo_6697_ = lean_ctor_get(v_a_6695_, 2);
lean_inc_ref(v_splitterMatchInfo_6697_);
lean_dec(v_a_6695_);
v___x_6698_ = l_Lean_mkConst(v_splitterName_6696_, v___x_6676_);
v_aux2_6699_ = l_Lean_mkAppN(v___x_6698_, v___y_6643_);
lean_inc_ref(v___y_6642_);
v_aux2_6700_ = l_Lean_Expr_app___override(v_aux2_6699_, v___y_6642_);
v_aux2_6701_ = l_Lean_mkAppN(v_aux2_6700_, v___y_6639_);
v___x_6702_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6701_, 2);
v___x_6703_ = l_Lean_indentExpr(v_aux2_6701_);
v___x_6704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6704_, 0, v___x_6702_);
lean_ctor_set(v___x_6704_, 1, v___x_6703_);
v___x_6705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6705_, 0, v___x_6704_);
lean_ctor_set(v___x_6705_, 1, v___x_6684_);
v___f_6706_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6706_, 0, v___x_6705_);
v___x_6707_ = lean_box(v___x_6687_);
v___x_6708_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6708_, 0, v_aux2_6701_);
lean_closure_set(v___x_6708_, 1, v___x_6707_);
v___x_6709_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6708_, v___f_6706_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
if (lean_obj_tag(v___x_6709_) == 0)
{
lean_object* v___x_6710_; 
lean_dec_ref_known(v___x_6709_, 1);
v___x_6710_ = l_Lean_Meta_inferArgumentTypesN(v___x_6691_, v_aux2_6701_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
if (lean_obj_tag(v___x_6710_) == 0)
{
lean_object* v_a_6711_; lean_object* v_numParams_6712_; lean_object* v_numDiscrs_6713_; lean_object* v_altInfos_6714_; lean_object* v_uElimPos_x3f_6715_; lean_object* v_overlaps_6716_; lean_object* v_altInfos_6717_; lean_object* v___x_6719_; uint8_t v_isShared_6720_; uint8_t v_isSharedCheck_6774_; 
v_a_6711_ = lean_ctor_get(v___x_6710_, 0);
lean_inc(v_a_6711_);
lean_dec_ref_known(v___x_6710_, 1);
v_numParams_6712_ = lean_ctor_get(v_toMatcherInfo_6531_, 0);
lean_inc(v_numParams_6712_);
v_numDiscrs_6713_ = lean_ctor_get(v_toMatcherInfo_6531_, 1);
lean_inc(v_numDiscrs_6713_);
v_altInfos_6714_ = lean_ctor_get(v_toMatcherInfo_6531_, 2);
lean_inc_ref(v_altInfos_6714_);
v_uElimPos_x3f_6715_ = lean_ctor_get(v_toMatcherInfo_6531_, 3);
lean_inc(v_uElimPos_x3f_6715_);
v_overlaps_6716_ = lean_ctor_get(v_toMatcherInfo_6531_, 5);
lean_inc_ref(v_overlaps_6716_);
lean_dec_ref(v_toMatcherInfo_6531_);
v_altInfos_6717_ = lean_ctor_get(v_splitterMatchInfo_6697_, 2);
v_isSharedCheck_6774_ = !lean_is_exclusive(v_splitterMatchInfo_6697_);
if (v_isSharedCheck_6774_ == 0)
{
lean_object* v_unused_6775_; lean_object* v_unused_6776_; lean_object* v_unused_6777_; lean_object* v_unused_6778_; lean_object* v_unused_6779_; 
v_unused_6775_ = lean_ctor_get(v_splitterMatchInfo_6697_, 5);
lean_dec(v_unused_6775_);
v_unused_6776_ = lean_ctor_get(v_splitterMatchInfo_6697_, 4);
lean_dec(v_unused_6776_);
v_unused_6777_ = lean_ctor_get(v_splitterMatchInfo_6697_, 3);
lean_dec(v_unused_6777_);
v_unused_6778_ = lean_ctor_get(v_splitterMatchInfo_6697_, 1);
lean_dec(v_unused_6778_);
v_unused_6779_ = lean_ctor_get(v_splitterMatchInfo_6697_, 0);
lean_dec(v_unused_6779_);
v___x_6719_ = v_splitterMatchInfo_6697_;
v_isShared_6720_ = v_isSharedCheck_6774_;
goto v_resetjp_6718_;
}
else
{
lean_inc(v_altInfos_6717_);
lean_dec(v_splitterMatchInfo_6697_);
v___x_6719_ = lean_box(0);
v_isShared_6720_ = v_isSharedCheck_6774_;
goto v_resetjp_6718_;
}
v_resetjp_6718_:
{
lean_object* v___x_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; lean_object* v___x_6729_; lean_object* v___x_6731_; 
v___x_6721_ = lean_array_get_size(v_altInfos_6714_);
v___x_6722_ = lean_array_get_size(v_altInfos_6717_);
v___x_6723_ = lean_array_get_size(v_a_6693_);
v___x_6724_ = lean_array_get_size(v_a_6711_);
v___x_6725_ = l_Array_toSubarray___redArg(v_alts_6537_, v___x_6651_, v___x_6691_);
lean_inc_ref(v_altInfos_6714_);
v___x_6726_ = l_Array_toSubarray___redArg(v_altInfos_6714_, v___x_6651_, v___x_6721_);
v___x_6727_ = l_Array_toSubarray___redArg(v_altInfos_6717_, v___x_6651_, v___x_6722_);
v___x_6728_ = l_Array_toSubarray___redArg(v_a_6693_, v___x_6651_, v___x_6723_);
v___x_6729_ = l_Array_toSubarray___redArg(v_a_6711_, v___x_6651_, v___x_6724_);
if (v_isShared_6675_ == 0)
{
lean_ctor_set(v___x_6674_, 1, v___x_6729_);
lean_ctor_set(v___x_6674_, 0, v___x_6728_);
v___x_6731_ = v___x_6674_;
goto v_reusejp_6730_;
}
else
{
lean_object* v_reuseFailAlloc_6773_; 
v_reuseFailAlloc_6773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6773_, 0, v___x_6728_);
lean_ctor_set(v_reuseFailAlloc_6773_, 1, v___x_6729_);
v___x_6731_ = v_reuseFailAlloc_6773_;
goto v_reusejp_6730_;
}
v_reusejp_6730_:
{
lean_object* v___x_6733_; 
if (v_isShared_6671_ == 0)
{
lean_ctor_set(v___x_6670_, 1, v___x_6731_);
lean_ctor_set(v___x_6670_, 0, v___x_6727_);
v___x_6733_ = v___x_6670_;
goto v_reusejp_6732_;
}
else
{
lean_object* v_reuseFailAlloc_6772_; 
v_reuseFailAlloc_6772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6772_, 0, v___x_6727_);
lean_ctor_set(v_reuseFailAlloc_6772_, 1, v___x_6731_);
v___x_6733_ = v_reuseFailAlloc_6772_;
goto v_reusejp_6732_;
}
v_reusejp_6732_:
{
lean_object* v___x_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; lean_object* v___x_6737_; 
v___x_6734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6734_, 0, v___x_6726_);
lean_ctor_set(v___x_6734_, 1, v___x_6733_);
v___x_6735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6735_, 0, v___x_6725_);
lean_ctor_set(v___x_6735_, 1, v___x_6734_);
v___x_6736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6736_, 0, v_remaining_x27_6652_);
lean_ctor_set(v___x_6736_, 1, v___x_6735_);
v___x_6737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6691_, v_onAlt_6522_, v_useSplitter_6518_, v_fst_6672_, v___y_6644_, v___x_6651_, v___x_6736_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_);
if (lean_obj_tag(v___x_6737_) == 0)
{
lean_object* v_a_6738_; lean_object* v_fst_6739_; lean_object* v___x_6740_; 
v_a_6738_ = lean_ctor_get(v___x_6737_, 0);
lean_inc(v_a_6738_);
lean_dec_ref_known(v___x_6737_, 1);
v_fst_6739_ = lean_ctor_get(v_a_6738_, 0);
lean_inc(v_fst_6739_);
lean_dec(v_a_6738_);
lean_inc(v___y_6650_);
lean_inc_ref(v___y_6649_);
lean_inc(v___y_6648_);
lean_inc_ref(v___y_6647_);
v___x_6740_ = lean_apply_6(v_onRemaining_6523_, v_remaining_6538_, v___y_6647_, v___y_6648_, v___y_6649_, v___y_6650_, lean_box(0));
if (lean_obj_tag(v___x_6740_) == 0)
{
lean_object* v_a_6741_; lean_object* v___x_6743_; uint8_t v_isShared_6744_; uint8_t v_isSharedCheck_6755_; 
v_a_6741_ = lean_ctor_get(v___x_6740_, 0);
v_isSharedCheck_6755_ = !lean_is_exclusive(v___x_6740_);
if (v_isSharedCheck_6755_ == 0)
{
v___x_6743_ = v___x_6740_;
v_isShared_6744_ = v_isSharedCheck_6755_;
goto v_resetjp_6742_;
}
else
{
lean_inc(v_a_6741_);
lean_dec(v___x_6740_);
v___x_6743_ = lean_box(0);
v_isShared_6744_ = v_isSharedCheck_6755_;
goto v_resetjp_6742_;
}
v_resetjp_6742_:
{
lean_object* v_remaining_x27_6745_; lean_object* v___x_6747_; 
v_remaining_x27_6745_ = l_Array_append___redArg(v_fst_6668_, v_a_6741_);
lean_dec(v_a_6741_);
if (v_isShared_6720_ == 0)
{
lean_ctor_set(v___x_6719_, 5, v_overlaps_6716_);
lean_ctor_set(v___x_6719_, 4, v___y_6641_);
lean_ctor_set(v___x_6719_, 3, v_uElimPos_x3f_6715_);
lean_ctor_set(v___x_6719_, 2, v_altInfos_6714_);
lean_ctor_set(v___x_6719_, 1, v_numDiscrs_6713_);
lean_ctor_set(v___x_6719_, 0, v_numParams_6712_);
v___x_6747_ = v___x_6719_;
goto v_reusejp_6746_;
}
else
{
lean_object* v_reuseFailAlloc_6754_; 
v_reuseFailAlloc_6754_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6754_, 0, v_numParams_6712_);
lean_ctor_set(v_reuseFailAlloc_6754_, 1, v_numDiscrs_6713_);
lean_ctor_set(v_reuseFailAlloc_6754_, 2, v_altInfos_6714_);
lean_ctor_set(v_reuseFailAlloc_6754_, 3, v_uElimPos_x3f_6715_);
lean_ctor_set(v_reuseFailAlloc_6754_, 4, v___y_6641_);
lean_ctor_set(v_reuseFailAlloc_6754_, 5, v_overlaps_6716_);
v___x_6747_ = v_reuseFailAlloc_6754_;
goto v_reusejp_6746_;
}
v_reusejp_6746_:
{
lean_object* v___x_6749_; 
if (v_isShared_6667_ == 0)
{
lean_ctor_set(v___x_6666_, 7, v_remaining_x27_6745_);
lean_ctor_set(v___x_6666_, 6, v_fst_6739_);
lean_ctor_set(v___x_6666_, 5, v___y_6639_);
lean_ctor_set(v___x_6666_, 4, v___y_6642_);
lean_ctor_set(v___x_6666_, 3, v___y_6643_);
lean_ctor_set(v___x_6666_, 2, v_matcherLevels_6646_);
lean_ctor_set(v___x_6666_, 1, v_splitterName_6696_);
lean_ctor_set(v___x_6666_, 0, v___x_6747_);
v___x_6749_ = v___x_6666_;
goto v_reusejp_6748_;
}
else
{
lean_object* v_reuseFailAlloc_6753_; 
v_reuseFailAlloc_6753_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6753_, 0, v___x_6747_);
lean_ctor_set(v_reuseFailAlloc_6753_, 1, v_splitterName_6696_);
lean_ctor_set(v_reuseFailAlloc_6753_, 2, v_matcherLevels_6646_);
lean_ctor_set(v_reuseFailAlloc_6753_, 3, v___y_6643_);
lean_ctor_set(v_reuseFailAlloc_6753_, 4, v___y_6642_);
lean_ctor_set(v_reuseFailAlloc_6753_, 5, v___y_6639_);
lean_ctor_set(v_reuseFailAlloc_6753_, 6, v_fst_6739_);
lean_ctor_set(v_reuseFailAlloc_6753_, 7, v_remaining_x27_6745_);
v___x_6749_ = v_reuseFailAlloc_6753_;
goto v_reusejp_6748_;
}
v_reusejp_6748_:
{
lean_object* v___x_6751_; 
if (v_isShared_6744_ == 0)
{
lean_ctor_set(v___x_6743_, 0, v___x_6749_);
v___x_6751_ = v___x_6743_;
goto v_reusejp_6750_;
}
else
{
lean_object* v_reuseFailAlloc_6752_; 
v_reuseFailAlloc_6752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6752_, 0, v___x_6749_);
v___x_6751_ = v_reuseFailAlloc_6752_;
goto v_reusejp_6750_;
}
v_reusejp_6750_:
{
return v___x_6751_;
}
}
}
}
}
else
{
lean_object* v_a_6756_; lean_object* v___x_6758_; uint8_t v_isShared_6759_; uint8_t v_isSharedCheck_6763_; 
lean_dec(v_fst_6739_);
lean_del_object(v___x_6719_);
lean_dec_ref(v_overlaps_6716_);
lean_dec(v_uElimPos_x3f_6715_);
lean_dec_ref(v_altInfos_6714_);
lean_dec(v_numDiscrs_6713_);
lean_dec(v_numParams_6712_);
lean_dec(v_splitterName_6696_);
lean_dec(v_fst_6668_);
lean_del_object(v___x_6666_);
lean_dec_ref(v_matcherLevels_6646_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
v_a_6756_ = lean_ctor_get(v___x_6740_, 0);
v_isSharedCheck_6763_ = !lean_is_exclusive(v___x_6740_);
if (v_isSharedCheck_6763_ == 0)
{
v___x_6758_ = v___x_6740_;
v_isShared_6759_ = v_isSharedCheck_6763_;
goto v_resetjp_6757_;
}
else
{
lean_inc(v_a_6756_);
lean_dec(v___x_6740_);
v___x_6758_ = lean_box(0);
v_isShared_6759_ = v_isSharedCheck_6763_;
goto v_resetjp_6757_;
}
v_resetjp_6757_:
{
lean_object* v___x_6761_; 
if (v_isShared_6759_ == 0)
{
v___x_6761_ = v___x_6758_;
goto v_reusejp_6760_;
}
else
{
lean_object* v_reuseFailAlloc_6762_; 
v_reuseFailAlloc_6762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6762_, 0, v_a_6756_);
v___x_6761_ = v_reuseFailAlloc_6762_;
goto v_reusejp_6760_;
}
v_reusejp_6760_:
{
return v___x_6761_;
}
}
}
}
else
{
lean_object* v_a_6764_; lean_object* v___x_6766_; uint8_t v_isShared_6767_; uint8_t v_isSharedCheck_6771_; 
lean_del_object(v___x_6719_);
lean_dec_ref(v_overlaps_6716_);
lean_dec(v_uElimPos_x3f_6715_);
lean_dec_ref(v_altInfos_6714_);
lean_dec(v_numDiscrs_6713_);
lean_dec(v_numParams_6712_);
lean_dec(v_splitterName_6696_);
lean_dec(v_fst_6668_);
lean_del_object(v___x_6666_);
lean_dec_ref(v_matcherLevels_6646_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_onRemaining_6523_);
v_a_6764_ = lean_ctor_get(v___x_6737_, 0);
v_isSharedCheck_6771_ = !lean_is_exclusive(v___x_6737_);
if (v_isSharedCheck_6771_ == 0)
{
v___x_6766_ = v___x_6737_;
v_isShared_6767_ = v_isSharedCheck_6771_;
goto v_resetjp_6765_;
}
else
{
lean_inc(v_a_6764_);
lean_dec(v___x_6737_);
v___x_6766_ = lean_box(0);
v_isShared_6767_ = v_isSharedCheck_6771_;
goto v_resetjp_6765_;
}
v_resetjp_6765_:
{
lean_object* v___x_6769_; 
if (v_isShared_6767_ == 0)
{
v___x_6769_ = v___x_6766_;
goto v_reusejp_6768_;
}
else
{
lean_object* v_reuseFailAlloc_6770_; 
v_reuseFailAlloc_6770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6770_, 0, v_a_6764_);
v___x_6769_ = v_reuseFailAlloc_6770_;
goto v_reusejp_6768_;
}
v_reusejp_6768_:
{
return v___x_6769_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6780_; lean_object* v___x_6782_; uint8_t v_isShared_6783_; uint8_t v_isSharedCheck_6787_; 
lean_dec_ref(v_splitterMatchInfo_6697_);
lean_dec(v_splitterName_6696_);
lean_dec(v_a_6693_);
lean_del_object(v___x_6674_);
lean_dec(v_fst_6672_);
lean_del_object(v___x_6670_);
lean_dec(v_fst_6668_);
lean_del_object(v___x_6666_);
lean_dec_ref(v_matcherLevels_6646_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
v_a_6780_ = lean_ctor_get(v___x_6710_, 0);
v_isSharedCheck_6787_ = !lean_is_exclusive(v___x_6710_);
if (v_isSharedCheck_6787_ == 0)
{
v___x_6782_ = v___x_6710_;
v_isShared_6783_ = v_isSharedCheck_6787_;
goto v_resetjp_6781_;
}
else
{
lean_inc(v_a_6780_);
lean_dec(v___x_6710_);
v___x_6782_ = lean_box(0);
v_isShared_6783_ = v_isSharedCheck_6787_;
goto v_resetjp_6781_;
}
v_resetjp_6781_:
{
lean_object* v___x_6785_; 
if (v_isShared_6783_ == 0)
{
v___x_6785_ = v___x_6782_;
goto v_reusejp_6784_;
}
else
{
lean_object* v_reuseFailAlloc_6786_; 
v_reuseFailAlloc_6786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6786_, 0, v_a_6780_);
v___x_6785_ = v_reuseFailAlloc_6786_;
goto v_reusejp_6784_;
}
v_reusejp_6784_:
{
return v___x_6785_;
}
}
}
}
else
{
lean_object* v_a_6788_; lean_object* v___x_6790_; uint8_t v_isShared_6791_; uint8_t v_isSharedCheck_6795_; 
lean_dec_ref(v_aux2_6701_);
lean_dec_ref(v_splitterMatchInfo_6697_);
lean_dec(v_splitterName_6696_);
lean_dec(v_a_6693_);
lean_del_object(v___x_6674_);
lean_dec(v_fst_6672_);
lean_del_object(v___x_6670_);
lean_dec(v_fst_6668_);
lean_del_object(v___x_6666_);
lean_dec_ref(v_matcherLevels_6646_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
v_a_6788_ = lean_ctor_get(v___x_6709_, 0);
v_isSharedCheck_6795_ = !lean_is_exclusive(v___x_6709_);
if (v_isSharedCheck_6795_ == 0)
{
v___x_6790_ = v___x_6709_;
v_isShared_6791_ = v_isSharedCheck_6795_;
goto v_resetjp_6789_;
}
else
{
lean_inc(v_a_6788_);
lean_dec(v___x_6709_);
v___x_6790_ = lean_box(0);
v_isShared_6791_ = v_isSharedCheck_6795_;
goto v_resetjp_6789_;
}
v_resetjp_6789_:
{
lean_object* v___x_6793_; 
if (v_isShared_6791_ == 0)
{
v___x_6793_ = v___x_6790_;
goto v_reusejp_6792_;
}
else
{
lean_object* v_reuseFailAlloc_6794_; 
v_reuseFailAlloc_6794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6794_, 0, v_a_6788_);
v___x_6793_ = v_reuseFailAlloc_6794_;
goto v_reusejp_6792_;
}
v_reusejp_6792_:
{
return v___x_6793_;
}
}
}
}
else
{
lean_object* v_a_6796_; lean_object* v___x_6798_; uint8_t v_isShared_6799_; uint8_t v_isSharedCheck_6803_; 
lean_dec(v_a_6693_);
lean_dec(v___x_6676_);
lean_del_object(v___x_6674_);
lean_dec(v_fst_6672_);
lean_del_object(v___x_6670_);
lean_dec(v_fst_6668_);
lean_del_object(v___x_6666_);
lean_dec_ref(v_matcherLevels_6646_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
v_a_6796_ = lean_ctor_get(v___x_6694_, 0);
v_isSharedCheck_6803_ = !lean_is_exclusive(v___x_6694_);
if (v_isSharedCheck_6803_ == 0)
{
v___x_6798_ = v___x_6694_;
v_isShared_6799_ = v_isSharedCheck_6803_;
goto v_resetjp_6797_;
}
else
{
lean_inc(v_a_6796_);
lean_dec(v___x_6694_);
v___x_6798_ = lean_box(0);
v_isShared_6799_ = v_isSharedCheck_6803_;
goto v_resetjp_6797_;
}
v_resetjp_6797_:
{
lean_object* v___x_6801_; 
if (v_isShared_6799_ == 0)
{
v___x_6801_ = v___x_6798_;
goto v_reusejp_6800_;
}
else
{
lean_object* v_reuseFailAlloc_6802_; 
v_reuseFailAlloc_6802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6802_, 0, v_a_6796_);
v___x_6801_ = v_reuseFailAlloc_6802_;
goto v_reusejp_6800_;
}
v_reusejp_6800_:
{
return v___x_6801_;
}
}
}
}
else
{
lean_object* v_a_6804_; lean_object* v___x_6806_; uint8_t v_isShared_6807_; uint8_t v_isSharedCheck_6811_; 
lean_dec(v___x_6676_);
lean_del_object(v___x_6674_);
lean_dec(v_fst_6672_);
lean_del_object(v___x_6670_);
lean_dec(v_fst_6668_);
lean_del_object(v___x_6666_);
lean_dec_ref(v_matcherLevels_6646_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
v_a_6804_ = lean_ctor_get(v___x_6692_, 0);
v_isSharedCheck_6811_ = !lean_is_exclusive(v___x_6692_);
if (v_isSharedCheck_6811_ == 0)
{
v___x_6806_ = v___x_6692_;
v_isShared_6807_ = v_isSharedCheck_6811_;
goto v_resetjp_6805_;
}
else
{
lean_inc(v_a_6804_);
lean_dec(v___x_6692_);
v___x_6806_ = lean_box(0);
v_isShared_6807_ = v_isSharedCheck_6811_;
goto v_resetjp_6805_;
}
v_resetjp_6805_:
{
lean_object* v___x_6809_; 
if (v_isShared_6807_ == 0)
{
v___x_6809_ = v___x_6806_;
goto v_reusejp_6808_;
}
else
{
lean_object* v_reuseFailAlloc_6810_; 
v_reuseFailAlloc_6810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6810_, 0, v_a_6804_);
v___x_6809_ = v_reuseFailAlloc_6810_;
goto v_reusejp_6808_;
}
v_reusejp_6808_:
{
return v___x_6809_;
}
}
}
}
else
{
lean_object* v_a_6812_; lean_object* v___x_6814_; uint8_t v_isShared_6815_; uint8_t v_isSharedCheck_6819_; 
lean_dec_ref(v_aux1_6680_);
lean_dec(v___x_6676_);
lean_del_object(v___x_6674_);
lean_dec(v_fst_6672_);
lean_del_object(v___x_6670_);
lean_dec(v_fst_6668_);
lean_del_object(v___x_6666_);
lean_dec_ref(v_matcherLevels_6646_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
v_a_6812_ = lean_ctor_get(v___x_6690_, 0);
v_isSharedCheck_6819_ = !lean_is_exclusive(v___x_6690_);
if (v_isSharedCheck_6819_ == 0)
{
v___x_6814_ = v___x_6690_;
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
else
{
lean_inc(v_a_6812_);
lean_dec(v___x_6690_);
v___x_6814_ = lean_box(0);
v_isShared_6815_ = v_isSharedCheck_6819_;
goto v_resetjp_6813_;
}
v_resetjp_6813_:
{
lean_object* v___x_6817_; 
if (v_isShared_6815_ == 0)
{
v___x_6817_ = v___x_6814_;
goto v_reusejp_6816_;
}
else
{
lean_object* v_reuseFailAlloc_6818_; 
v_reuseFailAlloc_6818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6818_, 0, v_a_6812_);
v___x_6817_ = v_reuseFailAlloc_6818_;
goto v_reusejp_6816_;
}
v_reusejp_6816_:
{
return v___x_6817_;
}
}
}
}
}
}
}
else
{
lean_object* v_fst_6833_; lean_object* v_fst_6834_; 
lean_dec(v___y_6644_);
v_fst_6833_ = lean_ctor_get(v_a_6661_, 0);
lean_inc(v_fst_6833_);
lean_dec(v_a_6661_);
v_fst_6834_ = lean_ctor_get(v_snd_6662_, 0);
lean_inc(v_fst_6834_);
lean_dec(v_snd_6662_);
v___y_6540_ = v___y_6650_;
v___y_6541_ = v_remaining_x27_6652_;
v___y_6542_ = v___y_6647_;
v___y_6543_ = v___x_6651_;
v___y_6544_ = v_matcherLevels_6646_;
v___y_6545_ = v___y_6649_;
v___y_6546_ = v___y_6639_;
v___y_6547_ = v_fst_6833_;
v___y_6548_ = v___y_6648_;
v___y_6549_ = v___y_6641_;
v___y_6550_ = v___y_6643_;
v___y_6551_ = v___y_6642_;
v___y_6552_ = v_fst_6834_;
goto v___jp_6539_;
}
}
}
else
{
lean_object* v_a_6835_; lean_object* v___x_6837_; uint8_t v_isShared_6838_; uint8_t v_isSharedCheck_6842_; 
lean_dec_ref(v_matcherLevels_6646_);
lean_dec(v___y_6644_);
lean_dec_ref(v___y_6643_);
lean_dec_ref(v___y_6642_);
lean_dec_ref(v___y_6641_);
lean_dec_ref(v___y_6639_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
lean_dec_ref(v_matcherApp_6517_);
v_a_6835_ = lean_ctor_get(v___x_6660_, 0);
v_isSharedCheck_6842_ = !lean_is_exclusive(v___x_6660_);
if (v_isSharedCheck_6842_ == 0)
{
v___x_6837_ = v___x_6660_;
v_isShared_6838_ = v_isSharedCheck_6842_;
goto v_resetjp_6836_;
}
else
{
lean_inc(v_a_6835_);
lean_dec(v___x_6660_);
v___x_6837_ = lean_box(0);
v_isShared_6838_ = v_isSharedCheck_6842_;
goto v_resetjp_6836_;
}
v_resetjp_6836_:
{
lean_object* v___x_6840_; 
if (v_isShared_6838_ == 0)
{
v___x_6840_ = v___x_6837_;
goto v_reusejp_6839_;
}
else
{
lean_object* v_reuseFailAlloc_6841_; 
v_reuseFailAlloc_6841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6841_, 0, v_a_6835_);
v___x_6840_ = v_reuseFailAlloc_6841_;
goto v_reusejp_6839_;
}
v_reusejp_6839_:
{
return v___x_6840_;
}
}
}
}
v___jp_6843_:
{
size_t v_sz_6849_; size_t v___x_6850_; lean_object* v___x_6851_; 
v_sz_6849_ = lean_array_size(v_params_6534_);
v___x_6850_ = ((size_t)0ULL);
lean_inc_ref(v_params_6534_);
lean_inc_ref(v_onParams_6520_);
v___x_6851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6520_, v_sz_6849_, v___x_6850_, v_params_6534_, v___y_6845_, v___y_6846_, v___y_6847_, v___y_6848_);
if (lean_obj_tag(v___x_6851_) == 0)
{
lean_object* v_a_6852_; size_t v_sz_6853_; lean_object* v___x_6854_; 
v_a_6852_ = lean_ctor_get(v___x_6851_, 0);
lean_inc(v_a_6852_);
lean_dec_ref_known(v___x_6851_, 1);
v_sz_6853_ = lean_array_size(v_discrs_6536_);
lean_inc_ref(v_discrs_6536_);
v___x_6854_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6520_, v_sz_6853_, v___x_6850_, v_discrs_6536_, v___y_6845_, v___y_6846_, v___y_6847_, v___y_6848_);
if (lean_obj_tag(v___x_6854_) == 0)
{
lean_object* v_a_6855_; lean_object* v___x_6856_; lean_object* v___x_6857_; lean_object* v___f_6858_; uint8_t v___x_6859_; lean_object* v___x_6860_; 
v_a_6855_ = lean_ctor_get(v___x_6854_, 0);
lean_inc_n(v_a_6855_, 2);
lean_dec_ref_known(v___x_6854_, 1);
v___x_6856_ = lean_box(v_addEqualities_6519_);
v___x_6857_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6536_);
lean_inc_ref(v_toMatcherInfo_6531_);
v___f_6858_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6858_, 0, v_onMotive_6521_);
lean_closure_set(v___f_6858_, 1, v_toMatcherInfo_6531_);
lean_closure_set(v___f_6858_, 2, v_a_6855_);
lean_closure_set(v___f_6858_, 3, v___x_6856_);
lean_closure_set(v___f_6858_, 4, v___x_6857_);
lean_closure_set(v___f_6858_, 5, v_discrs_6536_);
v___x_6859_ = 0;
lean_inc_ref(v_motive_6535_);
v___x_6860_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6535_, v___f_6858_, v___x_6859_, v___y_6845_, v___y_6846_, v___y_6847_, v___y_6848_);
if (lean_obj_tag(v___x_6860_) == 0)
{
lean_object* v_a_6861_; lean_object* v_snd_6862_; lean_object* v_snd_6863_; lean_object* v_uElimPos_x3f_6864_; 
v_a_6861_ = lean_ctor_get(v___x_6860_, 0);
lean_inc(v_a_6861_);
lean_dec_ref_known(v___x_6860_, 1);
v_snd_6862_ = lean_ctor_get(v_a_6861_, 1);
v_snd_6863_ = lean_ctor_get(v_snd_6862_, 1);
lean_inc(v_snd_6863_);
v_uElimPos_x3f_6864_ = lean_ctor_get(v_toMatcherInfo_6531_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6864_) == 0)
{
lean_object* v_fst_6865_; lean_object* v_fst_6866_; lean_object* v_snd_6867_; 
v_fst_6865_ = lean_ctor_get(v_a_6861_, 0);
lean_inc(v_fst_6865_);
lean_dec(v_a_6861_);
v_fst_6866_ = lean_ctor_get(v_snd_6863_, 0);
lean_inc(v_fst_6866_);
v_snd_6867_ = lean_ctor_get(v_snd_6863_, 1);
lean_inc(v_snd_6867_);
lean_dec(v_snd_6863_);
lean_inc_ref(v_matcherLevels_6533_);
v___y_6639_ = v_a_6855_;
v___y_6640_ = v_fst_6866_;
v___y_6641_ = v_snd_6867_;
v___y_6642_ = v_fst_6865_;
v___y_6643_ = v_a_6852_;
v___y_6644_ = v_numDiscrEqs_6844_;
v___y_6645_ = v___x_6850_;
v_matcherLevels_6646_ = v_matcherLevels_6533_;
v___y_6647_ = v___y_6845_;
v___y_6648_ = v___y_6846_;
v___y_6649_ = v___y_6847_;
v___y_6650_ = v___y_6848_;
goto v___jp_6638_;
}
else
{
lean_object* v_fst_6868_; lean_object* v_fst_6869_; lean_object* v_fst_6870_; lean_object* v_snd_6871_; lean_object* v_val_6872_; lean_object* v___x_6873_; 
lean_inc(v_snd_6862_);
v_fst_6868_ = lean_ctor_get(v_a_6861_, 0);
lean_inc(v_fst_6868_);
lean_dec(v_a_6861_);
v_fst_6869_ = lean_ctor_get(v_snd_6862_, 0);
lean_inc(v_fst_6869_);
lean_dec(v_snd_6862_);
v_fst_6870_ = lean_ctor_get(v_snd_6863_, 0);
lean_inc(v_fst_6870_);
v_snd_6871_ = lean_ctor_get(v_snd_6863_, 1);
lean_inc(v_snd_6871_);
lean_dec(v_snd_6863_);
v_val_6872_ = lean_ctor_get(v_uElimPos_x3f_6864_, 0);
lean_inc_ref(v_matcherLevels_6533_);
v___x_6873_ = lean_array_set(v_matcherLevels_6533_, v_val_6872_, v_fst_6869_);
v___y_6639_ = v_a_6855_;
v___y_6640_ = v_fst_6870_;
v___y_6641_ = v_snd_6871_;
v___y_6642_ = v_fst_6868_;
v___y_6643_ = v_a_6852_;
v___y_6644_ = v_numDiscrEqs_6844_;
v___y_6645_ = v___x_6850_;
v_matcherLevels_6646_ = v___x_6873_;
v___y_6647_ = v___y_6845_;
v___y_6648_ = v___y_6846_;
v___y_6649_ = v___y_6847_;
v___y_6650_ = v___y_6848_;
goto v___jp_6638_;
}
}
else
{
lean_object* v_a_6874_; lean_object* v___x_6876_; uint8_t v_isShared_6877_; uint8_t v_isSharedCheck_6881_; 
lean_dec(v_a_6855_);
lean_dec(v_a_6852_);
lean_dec(v_numDiscrEqs_6844_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
lean_dec_ref(v_matcherApp_6517_);
v_a_6874_ = lean_ctor_get(v___x_6860_, 0);
v_isSharedCheck_6881_ = !lean_is_exclusive(v___x_6860_);
if (v_isSharedCheck_6881_ == 0)
{
v___x_6876_ = v___x_6860_;
v_isShared_6877_ = v_isSharedCheck_6881_;
goto v_resetjp_6875_;
}
else
{
lean_inc(v_a_6874_);
lean_dec(v___x_6860_);
v___x_6876_ = lean_box(0);
v_isShared_6877_ = v_isSharedCheck_6881_;
goto v_resetjp_6875_;
}
v_resetjp_6875_:
{
lean_object* v___x_6879_; 
if (v_isShared_6877_ == 0)
{
v___x_6879_ = v___x_6876_;
goto v_reusejp_6878_;
}
else
{
lean_object* v_reuseFailAlloc_6880_; 
v_reuseFailAlloc_6880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6880_, 0, v_a_6874_);
v___x_6879_ = v_reuseFailAlloc_6880_;
goto v_reusejp_6878_;
}
v_reusejp_6878_:
{
return v___x_6879_;
}
}
}
}
else
{
lean_object* v_a_6882_; lean_object* v___x_6884_; uint8_t v_isShared_6885_; uint8_t v_isSharedCheck_6889_; 
lean_dec(v_a_6852_);
lean_dec(v_numDiscrEqs_6844_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
lean_dec_ref(v_onMotive_6521_);
lean_dec_ref(v_matcherApp_6517_);
v_a_6882_ = lean_ctor_get(v___x_6854_, 0);
v_isSharedCheck_6889_ = !lean_is_exclusive(v___x_6854_);
if (v_isSharedCheck_6889_ == 0)
{
v___x_6884_ = v___x_6854_;
v_isShared_6885_ = v_isSharedCheck_6889_;
goto v_resetjp_6883_;
}
else
{
lean_inc(v_a_6882_);
lean_dec(v___x_6854_);
v___x_6884_ = lean_box(0);
v_isShared_6885_ = v_isSharedCheck_6889_;
goto v_resetjp_6883_;
}
v_resetjp_6883_:
{
lean_object* v___x_6887_; 
if (v_isShared_6885_ == 0)
{
v___x_6887_ = v___x_6884_;
goto v_reusejp_6886_;
}
else
{
lean_object* v_reuseFailAlloc_6888_; 
v_reuseFailAlloc_6888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6888_, 0, v_a_6882_);
v___x_6887_ = v_reuseFailAlloc_6888_;
goto v_reusejp_6886_;
}
v_reusejp_6886_:
{
return v___x_6887_;
}
}
}
}
else
{
lean_object* v_a_6890_; lean_object* v___x_6892_; uint8_t v_isShared_6893_; uint8_t v_isSharedCheck_6897_; 
lean_dec(v_numDiscrEqs_6844_);
lean_dec_ref(v_remaining_6538_);
lean_dec_ref(v_alts_6537_);
lean_dec(v_matcherName_6532_);
lean_dec_ref(v_toMatcherInfo_6531_);
lean_dec_ref(v_onRemaining_6523_);
lean_dec_ref(v_onAlt_6522_);
lean_dec_ref(v_onMotive_6521_);
lean_dec_ref(v_onParams_6520_);
lean_dec_ref(v_matcherApp_6517_);
v_a_6890_ = lean_ctor_get(v___x_6851_, 0);
v_isSharedCheck_6897_ = !lean_is_exclusive(v___x_6851_);
if (v_isSharedCheck_6897_ == 0)
{
v___x_6892_ = v___x_6851_;
v_isShared_6893_ = v_isSharedCheck_6897_;
goto v_resetjp_6891_;
}
else
{
lean_inc(v_a_6890_);
lean_dec(v___x_6851_);
v___x_6892_ = lean_box(0);
v_isShared_6893_ = v_isSharedCheck_6897_;
goto v_resetjp_6891_;
}
v_resetjp_6891_:
{
lean_object* v___x_6895_; 
if (v_isShared_6893_ == 0)
{
v___x_6895_ = v___x_6892_;
goto v_reusejp_6894_;
}
else
{
lean_object* v_reuseFailAlloc_6896_; 
v_reuseFailAlloc_6896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6896_, 0, v_a_6890_);
v___x_6895_ = v_reuseFailAlloc_6896_;
goto v_reusejp_6894_;
}
v_reusejp_6894_:
{
return v___x_6895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6917_, lean_object* v_useSplitter_6918_, lean_object* v_addEqualities_6919_, lean_object* v_onParams_6920_, lean_object* v_onMotive_6921_, lean_object* v_onAlt_6922_, lean_object* v_onRemaining_6923_, lean_object* v___y_6924_, lean_object* v___y_6925_, lean_object* v___y_6926_, lean_object* v___y_6927_, lean_object* v___y_6928_){
_start:
{
uint8_t v_useSplitter_boxed_6929_; uint8_t v_addEqualities_boxed_6930_; lean_object* v_res_6931_; 
v_useSplitter_boxed_6929_ = lean_unbox(v_useSplitter_6918_);
v_addEqualities_boxed_6930_ = lean_unbox(v_addEqualities_6919_);
v_res_6931_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6917_, v_useSplitter_boxed_6929_, v_addEqualities_boxed_6930_, v_onParams_6920_, v_onMotive_6921_, v_onAlt_6922_, v_onRemaining_6923_, v___y_6924_, v___y_6925_, v___y_6926_, v___y_6927_);
lean_dec(v___y_6927_);
lean_dec_ref(v___y_6926_);
lean_dec(v___y_6925_);
lean_dec_ref(v___y_6924_);
return v_res_6931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6937_, lean_object* v_a_6938_, lean_object* v_a_6939_, lean_object* v_a_6940_, lean_object* v_a_6941_){
_start:
{
lean_object* v_toMatcherInfo_6943_; lean_object* v_matcherName_6944_; lean_object* v_matcherLevels_6945_; lean_object* v_params_6946_; lean_object* v_alts_6947_; lean_object* v_remaining_6948_; lean_object* v___f_6949_; lean_object* v___f_6950_; lean_object* v_nExtra_6951_; uint8_t v___x_6952_; lean_object* v___f_6953_; uint8_t v___x_6954_; lean_object* v___x_6955_; lean_object* v___x_6956_; lean_object* v___f_6957_; lean_object* v___x_6958_; 
v_toMatcherInfo_6943_ = lean_ctor_get(v_matcherApp_6937_, 0);
v_matcherName_6944_ = lean_ctor_get(v_matcherApp_6937_, 1);
v_matcherLevels_6945_ = lean_ctor_get(v_matcherApp_6937_, 2);
v_params_6946_ = lean_ctor_get(v_matcherApp_6937_, 3);
v_alts_6947_ = lean_ctor_get(v_matcherApp_6937_, 6);
v_remaining_6948_ = lean_ctor_get(v_matcherApp_6937_, 7);
v___f_6949_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6950_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6951_ = lean_array_get_size(v_remaining_6948_);
v___x_6952_ = 1;
v___f_6953_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6954_ = 0;
v___x_6955_ = lean_box(v___x_6954_);
v___x_6956_ = lean_box(v___x_6952_);
lean_inc_ref(v_matcherLevels_6945_);
lean_inc_ref(v_params_6946_);
lean_inc(v_matcherName_6944_);
lean_inc_ref(v_toMatcherInfo_6943_);
lean_inc_ref(v_alts_6947_);
v___f_6957_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6957_, 0, v_nExtra_6951_);
lean_closure_set(v___f_6957_, 1, v___x_6955_);
lean_closure_set(v___f_6957_, 2, v___x_6956_);
lean_closure_set(v___f_6957_, 3, v_alts_6947_);
lean_closure_set(v___f_6957_, 4, v_toMatcherInfo_6943_);
lean_closure_set(v___f_6957_, 5, v_matcherName_6944_);
lean_closure_set(v___f_6957_, 6, v_params_6946_);
lean_closure_set(v___f_6957_, 7, v_matcherLevels_6945_);
v___x_6958_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6937_, v___x_6952_, v___x_6954_, v___f_6949_, v___f_6957_, v___f_6953_, v___f_6950_, v_a_6938_, v_a_6939_, v_a_6940_, v_a_6941_);
return v___x_6958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6959_, lean_object* v_a_6960_, lean_object* v_a_6961_, lean_object* v_a_6962_, lean_object* v_a_6963_, lean_object* v_a_6964_){
_start:
{
lean_object* v_res_6965_; 
v_res_6965_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6959_, v_a_6960_, v_a_6961_, v_a_6962_, v_a_6963_);
lean_dec(v_a_6963_);
lean_dec_ref(v_a_6962_);
lean_dec(v_a_6961_);
lean_dec_ref(v_a_6960_);
return v_res_6965_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6966_, lean_object* v_termAlt_6967_, lean_object* v_inst_6968_, lean_object* v_R_6969_, lean_object* v_a_6970_, lean_object* v_b_6971_, lean_object* v_c_6972_, lean_object* v___y_6973_, lean_object* v___y_6974_, lean_object* v___y_6975_, lean_object* v___y_6976_){
_start:
{
lean_object* v___x_6978_; 
v___x_6978_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6966_, v_termAlt_6967_, v_a_6970_, v_b_6971_, v___y_6973_, v___y_6974_, v___y_6975_, v___y_6976_);
return v___x_6978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6979_, lean_object* v_termAlt_6980_, lean_object* v_inst_6981_, lean_object* v_R_6982_, lean_object* v_a_6983_, lean_object* v_b_6984_, lean_object* v_c_6985_, lean_object* v___y_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_, lean_object* v___y_6989_, lean_object* v___y_6990_){
_start:
{
lean_object* v_res_6991_; 
v_res_6991_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6979_, v_termAlt_6980_, v_inst_6981_, v_R_6982_, v_a_6983_, v_b_6984_, v_c_6985_, v___y_6986_, v___y_6987_, v___y_6988_, v___y_6989_);
lean_dec(v___y_6989_);
lean_dec_ref(v___y_6988_);
lean_dec(v___y_6987_);
lean_dec_ref(v___y_6986_);
return v_res_6991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6992_, lean_object* v_fvars_6993_, lean_object* v_names_6994_, lean_object* v_k_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_){
_start:
{
lean_object* v___x_7001_; 
v___x_7001_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6993_, v_names_6994_, v_k_6995_, v___y_6996_, v___y_6997_, v___y_6998_, v___y_6999_);
return v___x_7001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_7002_, lean_object* v_fvars_7003_, lean_object* v_names_7004_, lean_object* v_k_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_, lean_object* v___y_7009_, lean_object* v___y_7010_){
_start:
{
lean_object* v_res_7011_; 
v_res_7011_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_7002_, v_fvars_7003_, v_names_7004_, v_k_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_);
lean_dec(v___y_7009_);
lean_dec_ref(v___y_7008_);
lean_dec(v___y_7007_);
lean_dec_ref(v___y_7006_);
lean_dec_ref(v_names_7004_);
lean_dec_ref(v_fvars_7003_);
return v_res_7011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7012_, lean_object* v_origAltType_7013_, lean_object* v_altInfo_7014_, lean_object* v_k_7015_, lean_object* v___y_7016_, lean_object* v___y_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_){
_start:
{
lean_object* v___x_7021_; 
v___x_7021_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7013_, v_altInfo_7014_, v_k_7015_, v___y_7016_, v___y_7017_, v___y_7018_, v___y_7019_);
return v___x_7021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7022_, lean_object* v_origAltType_7023_, lean_object* v_altInfo_7024_, lean_object* v_k_7025_, lean_object* v___y_7026_, lean_object* v___y_7027_, lean_object* v___y_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_){
_start:
{
lean_object* v_res_7031_; 
v_res_7031_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7022_, v_origAltType_7023_, v_altInfo_7024_, v_k_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_);
lean_dec(v___y_7029_);
lean_dec_ref(v___y_7028_);
lean_dec(v___y_7027_);
lean_dec_ref(v___y_7026_);
return v_res_7031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7032_, lean_object* v___y_7033_, lean_object* v___y_7034_, lean_object* v___y_7035_, lean_object* v___y_7036_){
_start:
{
lean_object* v___x_7038_; 
v___x_7038_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7032_, v___y_7036_);
return v___x_7038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_, lean_object* v___y_7042_, lean_object* v___y_7043_, lean_object* v___y_7044_){
_start:
{
lean_object* v_res_7045_; 
v_res_7045_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7039_, v___y_7040_, v___y_7041_, v___y_7042_, v___y_7043_);
lean_dec(v___y_7043_);
lean_dec_ref(v___y_7042_);
lean_dec(v___y_7041_);
lean_dec_ref(v___y_7040_);
return v_res_7045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7046_, size_t v_i_7047_, lean_object* v_bs_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_, lean_object* v___y_7051_, lean_object* v___y_7052_){
_start:
{
lean_object* v___x_7054_; 
v___x_7054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7046_, v_i_7047_, v_bs_7048_, v___y_7049_, v___y_7051_, v___y_7052_);
return v___x_7054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7055_, lean_object* v_i_7056_, lean_object* v_bs_7057_, lean_object* v___y_7058_, lean_object* v___y_7059_, lean_object* v___y_7060_, lean_object* v___y_7061_, lean_object* v___y_7062_){
_start:
{
size_t v_sz_boxed_7063_; size_t v_i_boxed_7064_; lean_object* v_res_7065_; 
v_sz_boxed_7063_ = lean_unbox_usize(v_sz_7055_);
lean_dec(v_sz_7055_);
v_i_boxed_7064_ = lean_unbox_usize(v_i_7056_);
lean_dec(v_i_7056_);
v_res_7065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7063_, v_i_boxed_7064_, v_bs_7057_, v___y_7058_, v___y_7059_, v___y_7060_, v___y_7061_);
lean_dec(v___y_7061_);
lean_dec_ref(v___y_7060_);
lean_dec(v___y_7059_);
lean_dec_ref(v___y_7058_);
return v_res_7065_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7066_, lean_object* v_onAlt_7067_, lean_object* v_extraEqualities_7068_, lean_object* v_inst_7069_, lean_object* v_R_7070_, lean_object* v_a_7071_, lean_object* v_b_7072_, lean_object* v_c_7073_, lean_object* v___y_7074_, lean_object* v___y_7075_, lean_object* v___y_7076_, lean_object* v___y_7077_){
_start:
{
lean_object* v___x_7079_; 
v___x_7079_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7066_, v_onAlt_7067_, v_extraEqualities_7068_, v_a_7071_, v_b_7072_, v___y_7074_, v___y_7075_, v___y_7076_, v___y_7077_);
return v___x_7079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7080_, lean_object* v_onAlt_7081_, lean_object* v_extraEqualities_7082_, lean_object* v_inst_7083_, lean_object* v_R_7084_, lean_object* v_a_7085_, lean_object* v_b_7086_, lean_object* v_c_7087_, lean_object* v___y_7088_, lean_object* v___y_7089_, lean_object* v___y_7090_, lean_object* v___y_7091_, lean_object* v___y_7092_){
_start:
{
lean_object* v_res_7093_; 
v_res_7093_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7080_, v_onAlt_7081_, v_extraEqualities_7082_, v_inst_7083_, v_R_7084_, v_a_7085_, v_b_7086_, v_c_7087_, v___y_7088_, v___y_7089_, v___y_7090_, v___y_7091_);
lean_dec(v___y_7091_);
lean_dec_ref(v___y_7090_);
lean_dec(v___y_7089_);
lean_dec_ref(v___y_7088_);
lean_dec(v_upperBound_7080_);
return v_res_7093_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7094_, lean_object* v_onAlt_7095_, uint8_t v_useSplitter_7096_, lean_object* v_extraEqualities_7097_, lean_object* v_numDiscrEqs_7098_, lean_object* v_inst_7099_, lean_object* v_R_7100_, lean_object* v_a_7101_, lean_object* v_b_7102_, lean_object* v_c_7103_, lean_object* v___y_7104_, lean_object* v___y_7105_, lean_object* v___y_7106_, lean_object* v___y_7107_){
_start:
{
lean_object* v___x_7109_; 
v___x_7109_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7094_, v_onAlt_7095_, v_useSplitter_7096_, v_extraEqualities_7097_, v_numDiscrEqs_7098_, v_a_7101_, v_b_7102_, v___y_7104_, v___y_7105_, v___y_7106_, v___y_7107_);
return v___x_7109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7110_, lean_object* v_onAlt_7111_, lean_object* v_useSplitter_7112_, lean_object* v_extraEqualities_7113_, lean_object* v_numDiscrEqs_7114_, lean_object* v_inst_7115_, lean_object* v_R_7116_, lean_object* v_a_7117_, lean_object* v_b_7118_, lean_object* v_c_7119_, lean_object* v___y_7120_, lean_object* v___y_7121_, lean_object* v___y_7122_, lean_object* v___y_7123_, lean_object* v___y_7124_){
_start:
{
uint8_t v_useSplitter_boxed_7125_; lean_object* v_res_7126_; 
v_useSplitter_boxed_7125_ = lean_unbox(v_useSplitter_7112_);
v_res_7126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7110_, v_onAlt_7111_, v_useSplitter_boxed_7125_, v_extraEqualities_7113_, v_numDiscrEqs_7114_, v_inst_7115_, v_R_7116_, v_a_7117_, v_b_7118_, v_c_7119_, v___y_7120_, v___y_7121_, v___y_7122_, v___y_7123_);
lean_dec(v___y_7123_);
lean_dec_ref(v___y_7122_);
lean_dec(v___y_7121_);
lean_dec_ref(v___y_7120_);
lean_dec(v_upperBound_7110_);
return v_res_7126_;
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
