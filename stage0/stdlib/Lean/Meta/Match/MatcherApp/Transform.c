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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
lean_object* l_Subarray_empty(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "unexpected matcher application, insufficient number of parameters in alternative"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "unexpected matcher application, alternative must have "};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " parameters"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "failed to add argument to matcher application, argument type was not refined by `casesOn`"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1;
static const lean_string_object l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unexpected type at MatcherApp.addArg"};
static const lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "failed to transfer argument through matcher application, alt type must be telescope with #"};
static const lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0 = (const lean_object*)&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0_value;
static lean_once_cell_t l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7;
static const lean_string_object l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "assertion violation: altInfo.numOverlaps = 0\n      "};
static const lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__8 = (const lean_object*)&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__8_value;
static lean_once_cell_t l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed(lean_object**);
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
static lean_once_cell_t l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4 = (const lean_object*)&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(lean_object* v_type_19_, lean_object* v_maxFVars_x3f_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, uint8_t v_whnfType_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___f_29_; lean_object* v___x_30_; 
v___f_29_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_29_, 0, v_k_21_);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_19_, v_maxFVars_x3f_20_, v___f_29_, v_cleanupAnnotations_22_, v_whnfType_23_, v___y_24_, v___y_25_, v___y_26_, v___y_27_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___boxed(lean_object* v_type_47_, lean_object* v_maxFVars_x3f_48_, lean_object* v_k_49_, lean_object* v_cleanupAnnotations_50_, lean_object* v_whnfType_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; uint8_t v_whnfType_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_50_);
v_whnfType_boxed_58_ = lean_unbox(v_whnfType_51_);
v_res_59_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_type_47_, v_maxFVars_x3f_48_, v_k_49_, v_cleanupAnnotations_boxed_57_, v_whnfType_boxed_58_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(lean_object* v_00_u03b1_60_, lean_object* v_type_61_, lean_object* v_maxFVars_x3f_62_, lean_object* v_k_63_, uint8_t v_cleanupAnnotations_64_, uint8_t v_whnfType_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_type_61_, v_maxFVars_x3f_62_, v_k_63_, v_cleanupAnnotations_64_, v_whnfType_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___boxed(lean_object* v_00_u03b1_72_, lean_object* v_type_73_, lean_object* v_maxFVars_x3f_74_, lean_object* v_k_75_, lean_object* v_cleanupAnnotations_76_, lean_object* v_whnfType_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_83_; uint8_t v_whnfType_boxed_84_; lean_object* v_res_85_; 
v_cleanupAnnotations_boxed_83_ = lean_unbox(v_cleanupAnnotations_76_);
v_whnfType_boxed_84_ = lean_unbox(v_whnfType_77_);
v_res_85_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1(v_00_u03b1_72_, v_type_73_, v_maxFVars_x3f_74_, v_k_75_, v_cleanupAnnotations_boxed_83_, v_whnfType_boxed_84_, v___y_78_, v___y_79_, v___y_80_, v___y_81_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(lean_object* v_e_86_, lean_object* v_maxFVars_87_, lean_object* v_k_88_, uint8_t v_cleanupAnnotations_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___f_95_; uint8_t v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___f_95_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_95_, 0, v_k_88_);
v___x_96_ = 1;
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_98_, 0, v_maxFVars_87_);
v___x_99_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_86_, v___x_96_, v___x_97_, v___x_96_, v___x_97_, v___x_98_, v___f_95_, v_cleanupAnnotations_89_, v___y_90_, v___y_91_, v___y_92_, v___y_93_);
lean_dec_ref_known(v___x_98_, 1);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_107_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_107_ == 0)
{
v___x_102_ = v___x_99_;
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v___x_99_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_107_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_105_; 
if (v_isShared_103_ == 0)
{
v___x_105_ = v___x_102_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v_a_100_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
else
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_115_; 
v_a_108_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_115_ == 0)
{
v___x_110_ = v___x_99_;
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_99_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_115_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_113_; 
if (v_isShared_111_ == 0)
{
v___x_113_ = v___x_110_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_a_108_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg___boxed(lean_object* v_e_116_, lean_object* v_maxFVars_117_, lean_object* v_k_118_, lean_object* v_cleanupAnnotations_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_125_; lean_object* v_res_126_; 
v_cleanupAnnotations_boxed_125_ = lean_unbox(v_cleanupAnnotations_119_);
v_res_126_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(v_e_116_, v_maxFVars_117_, v_k_118_, v_cleanupAnnotations_boxed_125_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2(lean_object* v_00_u03b1_127_, lean_object* v_e_128_, lean_object* v_maxFVars_129_, lean_object* v_k_130_, uint8_t v_cleanupAnnotations_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(v_e_128_, v_maxFVars_129_, v_k_130_, v_cleanupAnnotations_131_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___boxed(lean_object* v_00_u03b1_138_, lean_object* v_e_139_, lean_object* v_maxFVars_140_, lean_object* v_k_141_, lean_object* v_cleanupAnnotations_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_148_; lean_object* v_res_149_; 
v_cleanupAnnotations_boxed_148_ = lean_unbox(v_cleanupAnnotations_142_);
v_res_149_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2(v_00_u03b1_138_, v_e_139_, v_maxFVars_140_, v_k_141_, v_cleanupAnnotations_boxed_148_, v___y_143_, v___y_144_, v___y_145_, v___y_146_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(lean_object* v_alt_150_, uint8_t v___x_151_, lean_object* v_xs_152_, uint8_t v_refined_153_, lean_object* v_unrefinedArgType_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
uint8_t v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; 
v___x_162_ = 0;
v___x_163_ = 1;
v___x_164_ = l_Lean_Meta_mkLambdaFVars(v_x_155_, v_alt_150_, v___x_162_, v___x_151_, v___x_162_, v___x_151_, v___x_163_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; uint8_t v_refined_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
if (v_refined_153_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_191_ = l_Lean_instInhabitedExpr;
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_array_get_borrowed(v___x_191_, v_x_155_, v___x_192_);
lean_inc(v___y_160_);
lean_inc_ref(v___y_159_);
lean_inc(v___y_158_);
lean_inc_ref(v___y_157_);
lean_inc(v___x_193_);
v___x_194_ = lean_infer_type(v___x_193_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v___x_196_ = l_Lean_Meta_isExprDefEq(v_unrefinedArgType_154_, v_a_195_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; uint8_t v___x_198_; uint8_t v___x_199_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v___x_198_ = lean_unbox(v_a_197_);
lean_dec(v_a_197_);
v___x_199_ = lean_bool_not(v___x_198_);
v_refined_167_ = v___x_199_;
v___y_168_ = v___y_157_;
v___y_169_ = v___y_158_;
v___y_170_ = v___y_159_;
v___y_171_ = v___y_160_;
goto v___jp_166_;
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_a_165_);
v_a_200_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_196_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec(v_a_165_);
lean_dec_ref(v_unrefinedArgType_154_);
v_a_208_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_194_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_194_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_dec_ref(v_unrefinedArgType_154_);
v_refined_167_ = v_refined_153_;
v___y_168_ = v___y_157_;
v___y_169_ = v___y_158_;
v___y_170_ = v___y_159_;
v___y_171_ = v___y_160_;
goto v___jp_166_;
}
v___jp_166_:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_Meta_mkLambdaFVars(v_xs_152_, v_a_165_, v___x_162_, v___x_151_, v___x_162_, v___x_151_, v___x_163_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_182_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_182_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_182_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_177_ = lean_box(v_refined_167_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v_a_173_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
v_a_183_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_172_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_172_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_unrefinedArgType_154_);
v_a_216_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_164_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_164_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed(lean_object* v_alt_224_, lean_object* v___x_225_, lean_object* v_xs_226_, lean_object* v_refined_227_, lean_object* v_unrefinedArgType_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
uint8_t v___x_4674__boxed_236_; uint8_t v_refined_boxed_237_; lean_object* v_res_238_; 
v___x_4674__boxed_236_ = lean_unbox(v___x_225_);
v_refined_boxed_237_ = lean_unbox(v_refined_227_);
v_res_238_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0(v_alt_224_, v___x_4674__boxed_236_, v_xs_226_, v_refined_boxed_237_, v_unrefinedArgType_228_, v_x_229_, v_x_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_x_230_);
lean_dec_ref(v_x_229_);
lean_dec_ref(v_xs_226_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(lean_object* v_msgData_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v___x_245_; lean_object* v_env_246_; lean_object* v___x_247_; lean_object* v_mctx_248_; lean_object* v_lctx_249_; lean_object* v_options_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_245_ = lean_st_ref_get(v___y_243_);
v_env_246_ = lean_ctor_get(v___x_245_, 0);
lean_inc_ref(v_env_246_);
lean_dec(v___x_245_);
v___x_247_ = lean_st_ref_get(v___y_241_);
v_mctx_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc_ref(v_mctx_248_);
lean_dec(v___x_247_);
v_lctx_249_ = lean_ctor_get(v___y_240_, 2);
v_options_250_ = lean_ctor_get(v___y_242_, 2);
lean_inc_ref(v_options_250_);
lean_inc_ref(v_lctx_249_);
v___x_251_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_251_, 0, v_env_246_);
lean_ctor_set(v___x_251_, 1, v_mctx_248_);
lean_ctor_set(v___x_251_, 2, v_lctx_249_);
lean_ctor_set(v___x_251_, 3, v_options_250_);
v___x_252_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_msgData_239_);
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0___boxed(lean_object* v_msgData_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msgData_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_ref_267_; lean_object* v___x_268_; lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_277_; 
v_ref_267_ = lean_ctor_get(v___y_264_, 5);
v___x_268_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_277_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_277_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_273_; lean_object* v___x_275_; 
lean_inc(v_ref_267_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_ref_267_);
lean_ctor_set(v___x_273_, 1, v_a_269_);
if (v_isShared_272_ == 0)
{
lean_ctor_set_tag(v___x_271_, 1);
lean_ctor_set(v___x_271_, 0, v___x_273_);
v___x_275_ = v___x_271_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_273_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg___boxed(lean_object* v_msg_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_);
lean_dec(v___y_282_);
lean_dec_ref(v___y_281_);
lean_dec(v___y_280_);
lean_dec_ref(v___y_279_);
return v_res_284_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__1));
v___x_289_ = l_Lean_stringToMessageData(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__3));
v___x_292_ = l_Lean_stringToMessageData(v___x_291_);
return v___x_292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__5));
v___x_295_ = l_Lean_stringToMessageData(v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(uint8_t v___x_296_, uint8_t v_refined_297_, lean_object* v_unrefinedArgType_298_, lean_object* v_binderType_299_, lean_object* v_numParams_300_, lean_object* v_xs_301_, lean_object* v_alt_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___f_310_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; lean_object* v___y_330_; lean_object* v___y_331_; lean_object* v___y_332_; lean_object* v___y_333_; lean_object* v___y_334_; uint8_t v___y_335_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_308_ = lean_box(v___x_296_);
v___x_309_ = lean_box(v_refined_297_);
lean_inc_ref(v_xs_301_);
v___f_310_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__0___boxed), 12, 5);
lean_closure_set(v___f_310_, 0, v_alt_302_);
lean_closure_set(v___f_310_, 1, v___x_308_);
lean_closure_set(v___f_310_, 2, v_xs_301_);
lean_closure_set(v___f_310_, 3, v___x_309_);
lean_closure_set(v___f_310_, 4, v_unrefinedArgType_298_);
v___x_343_ = lean_array_get_size(v_xs_301_);
v___x_344_ = lean_nat_dec_eq(v___x_343_, v_numParams_300_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_345_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__4);
v___x_346_ = l_Nat_reprFast(v_numParams_300_);
v___x_347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
v___x_348_ = l_Lean_MessageData_ofFormat(v___x_347_);
v___x_349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_345_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__6);
v___x_351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
v___x_352_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_351_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_dec_ref_known(v___x_352_, 1);
goto v___jp_338_;
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v___f_310_);
lean_dec_ref(v_xs_301_);
lean_dec_ref(v_binderType_299_);
v_a_353_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_352_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_352_);
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
else
{
lean_dec(v_numParams_300_);
goto v___jp_338_;
}
v___jp_311_:
{
if (lean_obj_tag(v___y_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v_a_317_ = lean_ctor_get(v___y_316_, 0);
lean_inc(v_a_317_);
lean_dec_ref_known(v___y_316_, 1);
v___x_318_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__0));
v___x_319_ = 0;
v___x_320_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_a_317_, v___x_318_, v___f_310_, v___x_319_, v___x_319_, v___y_315_, v___y_314_, v___y_313_, v___y_312_);
return v___x_320_;
}
else
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec_ref(v___f_310_);
v_a_321_ = lean_ctor_get(v___y_316_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v___y_316_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v___y_316_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___y_316_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_a_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
v___jp_329_:
{
if (v___y_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v___y_333_);
v___x_336_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_337_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_336_, v___y_334_, v___y_332_, v___y_331_, v___y_330_);
v___y_312_ = v___y_330_;
v___y_313_ = v___y_331_;
v___y_314_ = v___y_332_;
v___y_315_ = v___y_334_;
v___y_316_ = v___x_337_;
goto v___jp_311_;
}
else
{
v___y_312_ = v___y_330_;
v___y_313_ = v___y_331_;
v___y_314_ = v___y_332_;
v___y_315_ = v___y_334_;
v___y_316_ = v___y_333_;
goto v___jp_311_;
}
}
v___jp_338_:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_Meta_instantiateForall(v_binderType_299_, v_xs_301_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec_ref(v_xs_301_);
if (lean_obj_tag(v___x_339_) == 0)
{
v___y_312_ = v___y_306_;
v___y_313_ = v___y_305_;
v___y_314_ = v___y_304_;
v___y_315_ = v___y_303_;
v___y_316_ = v___x_339_;
goto v___jp_311_;
}
else
{
lean_object* v_a_340_; uint8_t v___x_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
v___x_341_ = l_Lean_Exception_isInterrupt(v_a_340_);
if (v___x_341_ == 0)
{
uint8_t v___x_342_; 
v___x_342_ = l_Lean_Exception_isRuntime(v_a_340_);
v___y_330_ = v___y_306_;
v___y_331_ = v___y_305_;
v___y_332_ = v___y_304_;
v___y_333_ = v___x_339_;
v___y_334_ = v___y_303_;
v___y_335_ = v___x_342_;
goto v___jp_329_;
}
else
{
lean_dec(v_a_340_);
v___y_330_ = v___y_306_;
v___y_331_ = v___y_305_;
v___y_332_ = v___y_304_;
v___y_333_ = v___x_339_;
v___y_334_ = v___y_303_;
v___y_335_ = v___x_341_;
goto v___jp_329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed(lean_object* v___x_361_, lean_object* v_refined_362_, lean_object* v_unrefinedArgType_363_, lean_object* v_binderType_364_, lean_object* v_numParams_365_, lean_object* v_xs_366_, lean_object* v_alt_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
uint8_t v___x_4900__boxed_373_; uint8_t v_refined_boxed_374_; lean_object* v_res_375_; 
v___x_4900__boxed_373_ = lean_unbox(v___x_361_);
v_refined_boxed_374_ = lean_unbox(v_refined_362_);
v_res_375_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1(v___x_4900__boxed_373_, v_refined_boxed_374_, v_unrefinedArgType_363_, v_binderType_364_, v_numParams_365_, v_xs_366_, v_alt_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_375_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__0));
v___x_378_ = l_Lean_stringToMessageData(v___x_377_);
return v___x_378_;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__2));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(lean_object* v_unrefinedArgType_382_, lean_object* v_typeNew_383_, lean_object* v_altNumParams_384_, lean_object* v_alts_385_, uint8_t v_refined_386_, lean_object* v_i_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = lean_array_get_size(v_alts_385_);
v___x_394_ = lean_nat_dec_lt(v_i_387_, v___x_393_);
if (v___x_394_ == 0)
{
lean_dec(v_i_387_);
lean_dec_ref(v_typeNew_383_);
lean_dec_ref(v_unrefinedArgType_382_);
if (v_refined_386_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec_ref(v_alts_385_);
v___x_395_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__1);
v___x_396_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_395_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
return v___x_396_;
}
else
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v_alts_385_);
return v___x_397_;
}
}
else
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_whnfD(v_typeNew_383_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
if (lean_obj_tag(v_a_399_) == 7)
{
lean_object* v_binderType_400_; lean_object* v_body_401_; lean_object* v___x_402_; lean_object* v_alt_403_; lean_object* v_numParams_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___f_407_; uint8_t v___x_408_; lean_object* v___x_409_; 
v_binderType_400_ = lean_ctor_get(v_a_399_, 1);
lean_inc_ref(v_binderType_400_);
v_body_401_ = lean_ctor_get(v_a_399_, 2);
lean_inc_ref(v_body_401_);
lean_dec_ref_known(v_a_399_, 3);
v___x_402_ = lean_unsigned_to_nat(0u);
v_alt_403_ = lean_array_fget_borrowed(v_alts_385_, v_i_387_);
v_numParams_404_ = lean_array_get_borrowed(v___x_402_, v_altNumParams_384_, v_i_387_);
v___x_405_ = lean_box(v___x_394_);
v___x_406_ = lean_box(v_refined_386_);
lean_inc_n(v_numParams_404_, 2);
lean_inc_ref(v_unrefinedArgType_382_);
v___f_407_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___boxed), 12, 5);
lean_closure_set(v___f_407_, 0, v___x_405_);
lean_closure_set(v___f_407_, 1, v___x_406_);
lean_closure_set(v___f_407_, 2, v_unrefinedArgType_382_);
lean_closure_set(v___f_407_, 3, v_binderType_400_);
lean_closure_set(v___f_407_, 4, v_numParams_404_);
v___x_408_ = 0;
lean_inc(v_alt_403_);
v___x_409_ = l_Lean_Meta_lambdaBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__2___redArg(v_alt_403_, v_numParams_404_, v___f_407_, v___x_408_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_a_410_; lean_object* v_fst_411_; lean_object* v_snd_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_a_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_a_410_);
lean_dec_ref_known(v___x_409_, 1);
v_fst_411_ = lean_ctor_get(v_a_410_, 0);
lean_inc(v_fst_411_);
v_snd_412_ = lean_ctor_get(v_a_410_, 1);
lean_inc(v_snd_412_);
lean_dec(v_a_410_);
v___x_413_ = lean_expr_instantiate1(v_body_401_, v_fst_411_);
lean_dec_ref(v_body_401_);
v___x_414_ = lean_array_fset(v_alts_385_, v_i_387_, v_fst_411_);
v___x_415_ = lean_unsigned_to_nat(1u);
v___x_416_ = lean_nat_add(v_i_387_, v___x_415_);
lean_dec(v_i_387_);
v___x_417_ = lean_unbox(v_snd_412_);
lean_dec(v_snd_412_);
v_typeNew_383_ = v___x_413_;
v_alts_385_ = v___x_414_;
v_refined_386_ = v___x_417_;
v_i_387_ = v___x_416_;
goto _start;
}
else
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_426_; 
lean_dec_ref(v_body_401_);
lean_dec(v_i_387_);
lean_dec_ref(v_alts_385_);
lean_dec_ref(v_unrefinedArgType_382_);
v_a_419_ = lean_ctor_get(v___x_409_, 0);
v_isSharedCheck_426_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_426_ == 0)
{
v___x_421_ = v___x_409_;
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_409_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_426_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
if (v_isShared_422_ == 0)
{
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_a_399_);
lean_dec(v_i_387_);
lean_dec_ref(v_alts_385_);
lean_dec_ref(v_unrefinedArgType_382_);
v___x_427_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___closed__3);
v___x_428_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_427_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
return v___x_428_;
}
}
else
{
lean_object* v_a_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_436_; 
lean_dec(v_i_387_);
lean_dec_ref(v_alts_385_);
lean_dec_ref(v_unrefinedArgType_382_);
v_a_429_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_436_ == 0)
{
v___x_431_ = v___x_398_;
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_a_429_);
lean_dec(v___x_398_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_436_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_434_; 
if (v_isShared_432_ == 0)
{
v___x_434_ = v___x_431_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_429_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___boxed(lean_object* v_unrefinedArgType_437_, lean_object* v_typeNew_438_, lean_object* v_altNumParams_439_, lean_object* v_alts_440_, lean_object* v_refined_441_, lean_object* v_i_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
uint8_t v_refined_boxed_448_; lean_object* v_res_449_; 
v_refined_boxed_448_ = lean_unbox(v_refined_441_);
v_res_449_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v_unrefinedArgType_437_, v_typeNew_438_, v_altNumParams_439_, v_alts_440_, v_refined_boxed_448_, v_i_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec_ref(v_altNumParams_439_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(lean_object* v_00_u03b1_450_, lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v_msg_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___boxed(lean_object* v_00_u03b1_458_, lean_object* v_msg_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0(v_00_u03b1_458_, v_msg_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(lean_object* v_e_466_, lean_object* v_k_467_, uint8_t v_cleanupAnnotations_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___f_474_; uint8_t v___x_475_; uint8_t v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___f_474_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_474_, 0, v_k_467_);
v___x_475_ = 1;
v___x_476_ = 0;
v___x_477_ = lean_box(0);
v___x_478_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_466_, v___x_475_, v___x_476_, v___x_475_, v___x_476_, v___x_477_, v___f_474_, v_cleanupAnnotations_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_486_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_486_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_486_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_484_; 
if (v_isShared_482_ == 0)
{
v___x_484_ = v___x_481_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
v___x_484_ = v_reuseFailAlloc_485_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
return v___x_484_;
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_478_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_478_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg___boxed(lean_object* v_e_495_, lean_object* v_k_496_, lean_object* v_cleanupAnnotations_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_503_; lean_object* v_res_504_; 
v_cleanupAnnotations_boxed_503_ = lean_unbox(v_cleanupAnnotations_497_);
v_res_504_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_495_, v_k_496_, v_cleanupAnnotations_boxed_503_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(lean_object* v_00_u03b1_505_, lean_object* v_e_506_, lean_object* v_k_507_, uint8_t v_cleanupAnnotations_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_e_506_, v_k_507_, v_cleanupAnnotations_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___boxed(lean_object* v_00_u03b1_515_, lean_object* v_e_516_, lean_object* v_k_517_, lean_object* v_cleanupAnnotations_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_524_; lean_object* v_res_525_; 
v_cleanupAnnotations_boxed_524_ = lean_unbox(v_cleanupAnnotations_518_);
v_res_525_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1(v_00_u03b1_515_, v_e_516_, v_k_517_, v_cleanupAnnotations_boxed_524_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(lean_object* v___x_526_, lean_object* v_motiveArgs_527_, lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
lean_object* v_zero_530_; uint8_t v_isZero_531_; 
v_zero_530_ = lean_unsigned_to_nat(0u);
v_isZero_531_ = lean_nat_dec_eq(v_x_528_, v_zero_530_);
if (v_isZero_531_ == 1)
{
lean_dec(v_x_528_);
return v_x_529_;
}
else
{
lean_object* v_one_532_; lean_object* v_n_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v_one_532_ = lean_unsigned_to_nat(1u);
v_n_533_ = lean_nat_sub(v_x_528_, v_one_532_);
lean_dec(v_x_528_);
v___x_534_ = lean_array_fget_borrowed(v___x_526_, v_n_533_);
v___x_535_ = l_Lean_Expr_isFVar(v___x_534_);
if (v___x_535_ == 0)
{
v_x_528_ = v_n_533_;
goto _start;
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_537_ = l_Lean_instInhabitedExpr;
v___x_538_ = lean_array_get_borrowed(v___x_537_, v_motiveArgs_527_, v_n_533_);
lean_inc(v___x_534_);
v___x_539_ = l_Lean_Expr_replaceFVar(v_x_529_, v___x_534_, v___x_538_);
lean_dec_ref(v_x_529_);
v_x_528_ = v_n_533_;
v_x_529_ = v___x_539_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0___boxed(lean_object* v___x_541_, lean_object* v_motiveArgs_542_, lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_541_, v_motiveArgs_542_, v_x_543_, v_x_544_);
lean_dec_ref(v_motiveArgs_542_);
lean_dec_ref(v___x_541_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(lean_object* v___x_546_, lean_object* v_motiveArgs_547_, lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v_zero_550_; uint8_t v_isZero_551_; 
v_zero_550_ = lean_unsigned_to_nat(0u);
v_isZero_551_ = lean_nat_dec_eq(v_x_548_, v_zero_550_);
if (v_isZero_551_ == 1)
{
return v_x_549_;
}
else
{
lean_object* v_one_552_; lean_object* v_n_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_one_552_ = lean_unsigned_to_nat(1u);
v_n_553_ = lean_nat_sub(v_x_548_, v_one_552_);
v___x_554_ = lean_array_fget_borrowed(v___x_546_, v_n_553_);
v___x_555_ = l_Lean_Expr_isFVar(v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_546_, v_motiveArgs_547_, v_n_553_, v_x_549_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_557_ = l_Lean_instInhabitedExpr;
v___x_558_ = lean_array_get_borrowed(v___x_557_, v_motiveArgs_547_, v_n_553_);
lean_inc(v___x_554_);
v___x_559_ = l_Lean_Expr_replaceFVar(v_x_549_, v___x_554_, v___x_558_);
lean_dec_ref(v_x_549_);
v___x_560_ = l_Nat_foldRev___at___00Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0_spec__0(v___x_546_, v_motiveArgs_547_, v_n_553_, v___x_559_);
return v___x_560_;
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0___boxed(lean_object* v___x_561_, lean_object* v_motiveArgs_562_, lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v___x_561_, v_motiveArgs_562_, v_x_563_, v_x_564_);
lean_dec(v_x_563_);
lean_dec_ref(v_motiveArgs_562_);
lean_dec_ref(v___x_561_);
return v_res_565_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__2));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_MatcherApp_addArg___lam__0___closed__4));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0(lean_object* v_matcherApp_575_, lean_object* v_e_576_, lean_object* v_discrs_577_, lean_object* v_toMatcherInfo_578_, lean_object* v_params_579_, lean_object* v_remaining_580_, lean_object* v_matcherName_581_, lean_object* v_alts_582_, lean_object* v_matcherLevels_583_, lean_object* v_motiveArgs_584_, lean_object* v_motiveBody_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v_matcherLevels_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = lean_array_get_size(v_motiveArgs_584_);
v___x_736_ = lean_array_get_size(v_discrs_577_);
v___x_737_ = lean_nat_dec_eq(v___x_735_, v___x_736_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v_motiveBody_585_);
lean_dec_ref(v_matcherLevels_583_);
lean_dec_ref(v_alts_582_);
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_578_);
lean_dec_ref(v_discrs_577_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v___x_738_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_739_ = l_Nat_reprFast(v___x_736_);
v___x_740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
v___x_741_ = l_Lean_MessageData_ofFormat(v___x_740_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_738_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_744_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
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
else
{
v___y_695_ = v___y_586_;
v___y_696_ = v___y_587_;
v___y_697_ = v___y_588_;
v___y_698_ = v___y_589_;
goto v___jp_694_;
}
v___jp_591_:
{
lean_object* v___x_607_; 
lean_inc(v___y_606_);
lean_inc_ref(v___y_605_);
lean_inc(v___y_604_);
lean_inc_ref(v___y_603_);
v___x_607_ = lean_infer_type(v___y_595_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_a_608_);
lean_dec_ref_known(v___x_607_, 1);
v___x_609_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_575_);
v___x_610_ = lean_unsigned_to_nat(0u);
v___x_611_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts(v___y_600_, v_a_608_, v___x_609_, v___y_601_, v___y_598_, v___x_610_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
lean_dec_ref(v___x_609_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_624_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_624_ == 0)
{
v___x_614_ = v___x_611_;
v_isShared_615_ = v_isSharedCheck_624_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_611_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_624_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_mk_empty_array_with_capacity(v___x_616_);
v___x_618_ = lean_array_push(v___x_617_, v_e_576_);
v___x_619_ = l_Array_append___redArg(v___x_618_, v___y_594_);
v___x_620_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_620_, 0, v___y_602_);
lean_ctor_set(v___x_620_, 1, v___y_599_);
lean_ctor_set(v___x_620_, 2, v___y_596_);
lean_ctor_set(v___x_620_, 3, v___y_593_);
lean_ctor_set(v___x_620_, 4, v___y_597_);
lean_ctor_set(v___x_620_, 5, v___y_592_);
lean_ctor_set(v___x_620_, 6, v_a_612_);
lean_ctor_set(v___x_620_, 7, v___x_619_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_620_);
v___x_622_ = v___x_614_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_620_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec_ref(v___y_602_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_e_576_);
v_a_625_ = lean_ctor_get(v___x_611_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_611_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_611_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_611_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
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
else
{
lean_object* v_a_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
lean_dec_ref(v___y_602_);
lean_dec_ref(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v_a_633_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_640_ == 0)
{
v___x_635_ = v___x_607_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_a_633_);
lean_dec(v___x_607_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_a_633_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
v___jp_641_:
{
uint8_t v___x_655_; uint8_t v___x_656_; uint8_t v___x_657_; lean_object* v___x_658_; 
v___x_655_ = 0;
v___x_656_ = 1;
v___x_657_ = 1;
v___x_658_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_584_, v___y_645_, v___x_655_, v___x_656_, v___x_655_, v___x_656_, v___x_657_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc_n(v_a_659_, 2);
lean_dec_ref_known(v___x_658_, 1);
lean_inc_ref(v_matcherLevels_650_);
v___x_660_ = lean_array_to_list(v_matcherLevels_650_);
lean_inc(v___y_647_);
v___x_661_ = l_Lean_mkConst(v___y_647_, v___x_660_);
v___x_662_ = l_Lean_mkAppN(v___x_661_, v___y_643_);
v___x_663_ = l_Lean_Expr_app___override(v___x_662_, v_a_659_);
v___x_664_ = l_Lean_mkAppN(v___x_663_, v___y_642_);
lean_inc_ref(v___x_664_);
v___x_665_ = l_Lean_Meta_isTypeCorrect(v___x_664_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; uint8_t v___x_667_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v___x_664_);
lean_dec(v_a_659_);
lean_dec_ref(v_matcherLevels_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v___x_668_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__1);
v___x_669_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_668_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
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
v___y_592_ = v___y_642_;
v___y_593_ = v___y_643_;
v___y_594_ = v___y_644_;
v___y_595_ = v___x_664_;
v___y_596_ = v_matcherLevels_650_;
v___y_597_ = v_a_659_;
v___y_598_ = v___x_655_;
v___y_599_ = v___y_647_;
v___y_600_ = v___y_646_;
v___y_601_ = v___y_648_;
v___y_602_ = v___y_649_;
v___y_603_ = v___y_651_;
v___y_604_ = v___y_652_;
v___y_605_ = v___y_653_;
v___y_606_ = v___y_654_;
goto v___jp_591_;
}
}
else
{
lean_object* v_a_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_685_; 
lean_dec_ref(v___x_664_);
lean_dec(v_a_659_);
lean_dec_ref(v_matcherLevels_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v_a_678_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_685_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_685_ == 0)
{
v___x_680_ = v___x_665_;
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_a_678_);
lean_dec(v___x_665_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_685_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_a_678_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
else
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
lean_dec_ref(v_matcherLevels_650_);
lean_dec_ref(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v_a_686_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_658_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_658_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
v___jp_694_:
{
lean_object* v___x_699_; 
lean_inc(v___y_698_);
lean_inc_ref(v___y_697_);
lean_inc(v___y_696_);
lean_inc_ref(v___y_695_);
lean_inc_ref(v_e_576_);
v___x_699_ = lean_infer_type(v_e_576_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc_n(v_a_700_, 2);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = lean_array_get_size(v_discrs_577_);
v___x_702_ = l_Nat_foldRev___at___00Lean_Meta_MatcherApp_addArg_spec__0(v_discrs_577_, v_motiveArgs_584_, v___x_701_, v_a_700_);
v___x_703_ = l_Lean_mkArrow(v___x_702_, v_motiveBody_585_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_uElimPos_x3f_704_; 
v_uElimPos_x3f_704_ = lean_ctor_get(v_toMatcherInfo_578_, 3);
if (lean_obj_tag(v_uElimPos_x3f_704_) == 0)
{
lean_object* v_a_705_; 
v_a_705_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_703_, 1);
v___y_642_ = v_discrs_577_;
v___y_643_ = v_params_579_;
v___y_644_ = v_remaining_580_;
v___y_645_ = v_a_705_;
v___y_646_ = v_a_700_;
v___y_647_ = v_matcherName_581_;
v___y_648_ = v_alts_582_;
v___y_649_ = v_toMatcherInfo_578_;
v_matcherLevels_650_ = v_matcherLevels_583_;
v___y_651_ = v___y_695_;
v___y_652_ = v___y_696_;
v___y_653_ = v___y_697_;
v___y_654_ = v___y_698_;
goto v___jp_641_;
}
else
{
lean_object* v_a_706_; lean_object* v_val_707_; lean_object* v___x_708_; 
v_a_706_ = lean_ctor_get(v___x_703_, 0);
lean_inc_n(v_a_706_, 2);
lean_dec_ref_known(v___x_703_, 1);
v_val_707_ = lean_ctor_get(v_uElimPos_x3f_704_, 0);
v___x_708_ = l_Lean_Meta_getLevel(v_a_706_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_array_set(v_matcherLevels_583_, v_val_707_, v_a_709_);
v___y_642_ = v_discrs_577_;
v___y_643_ = v_params_579_;
v___y_644_ = v_remaining_580_;
v___y_645_ = v_a_706_;
v___y_646_ = v_a_700_;
v___y_647_ = v_matcherName_581_;
v___y_648_ = v_alts_582_;
v___y_649_ = v_toMatcherInfo_578_;
v_matcherLevels_650_ = v___x_710_;
v___y_651_ = v___y_695_;
v___y_652_ = v___y_696_;
v___y_653_ = v___y_697_;
v___y_654_ = v___y_698_;
goto v___jp_641_;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_a_706_);
lean_dec(v_a_700_);
lean_dec_ref(v_matcherLevels_583_);
lean_dec_ref(v_alts_582_);
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_578_);
lean_dec_ref(v_discrs_577_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v_a_711_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_708_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_708_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_700_);
lean_dec_ref(v_matcherLevels_583_);
lean_dec_ref(v_alts_582_);
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_578_);
lean_dec_ref(v_discrs_577_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v_a_719_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_703_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_703_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_motiveBody_585_);
lean_dec_ref(v_matcherLevels_583_);
lean_dec_ref(v_alts_582_);
lean_dec(v_matcherName_581_);
lean_dec_ref(v_params_579_);
lean_dec_ref(v_toMatcherInfo_578_);
lean_dec_ref(v_discrs_577_);
lean_dec_ref(v_e_576_);
lean_dec_ref(v_matcherApp_575_);
v_a_727_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_699_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_699_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___lam__0___boxed(lean_object* v_matcherApp_754_, lean_object* v_e_755_, lean_object* v_discrs_756_, lean_object* v_toMatcherInfo_757_, lean_object* v_params_758_, lean_object* v_remaining_759_, lean_object* v_matcherName_760_, lean_object* v_alts_761_, lean_object* v_matcherLevels_762_, lean_object* v_motiveArgs_763_, lean_object* v_motiveBody_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_MatcherApp_addArg___lam__0(v_matcherApp_754_, v_e_755_, v_discrs_756_, v_toMatcherInfo_757_, v_params_758_, v_remaining_759_, v_matcherName_760_, v_alts_761_, v_matcherLevels_762_, v_motiveArgs_763_, v_motiveBody_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec_ref(v_motiveArgs_763_);
lean_dec_ref(v_remaining_759_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg(lean_object* v_matcherApp_771_, lean_object* v_e_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_toMatcherInfo_778_; lean_object* v_matcherName_779_; lean_object* v_matcherLevels_780_; lean_object* v_params_781_; lean_object* v_motive_782_; lean_object* v_discrs_783_; lean_object* v_alts_784_; lean_object* v_remaining_785_; lean_object* v___f_786_; uint8_t v___x_787_; lean_object* v___x_788_; 
v_toMatcherInfo_778_ = lean_ctor_get(v_matcherApp_771_, 0);
lean_inc_ref(v_toMatcherInfo_778_);
v_matcherName_779_ = lean_ctor_get(v_matcherApp_771_, 1);
lean_inc(v_matcherName_779_);
v_matcherLevels_780_ = lean_ctor_get(v_matcherApp_771_, 2);
lean_inc_ref(v_matcherLevels_780_);
v_params_781_ = lean_ctor_get(v_matcherApp_771_, 3);
lean_inc_ref(v_params_781_);
v_motive_782_ = lean_ctor_get(v_matcherApp_771_, 4);
lean_inc_ref(v_motive_782_);
v_discrs_783_ = lean_ctor_get(v_matcherApp_771_, 5);
lean_inc_ref(v_discrs_783_);
v_alts_784_ = lean_ctor_get(v_matcherApp_771_, 6);
lean_inc_ref(v_alts_784_);
v_remaining_785_ = lean_ctor_get(v_matcherApp_771_, 7);
lean_inc_ref(v_remaining_785_);
v___f_786_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_addArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_786_, 0, v_matcherApp_771_);
lean_closure_set(v___f_786_, 1, v_e_772_);
lean_closure_set(v___f_786_, 2, v_discrs_783_);
lean_closure_set(v___f_786_, 3, v_toMatcherInfo_778_);
lean_closure_set(v___f_786_, 4, v_params_781_);
lean_closure_set(v___f_786_, 5, v_remaining_785_);
lean_closure_set(v___f_786_, 6, v_matcherName_779_);
lean_closure_set(v___f_786_, 7, v_alts_784_);
lean_closure_set(v___f_786_, 8, v_matcherLevels_780_);
v___x_787_ = 0;
v___x_788_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_782_, v___f_786_, v___x_787_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg___boxed(lean_object* v_matcherApp_789_, lean_object* v_e_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_789_, v_e_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec_ref(v_a_791_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f(lean_object* v_matcherApp_797_, lean_object* v_e_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = l_Lean_Meta_MatcherApp_addArg(v_matcherApp_797_, v_e_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_813_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_807_ = v___x_804_;
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_804_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_813_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v_a_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 0, v___x_809_);
v___x_811_ = v___x_807_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_829_; 
v_a_814_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_829_ == 0)
{
v___x_816_ = v___x_804_;
v_isShared_817_ = v_isSharedCheck_829_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_804_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_829_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
uint8_t v___y_819_; uint8_t v___x_827_; 
v___x_827_ = l_Lean_Exception_isInterrupt(v_a_814_);
if (v___x_827_ == 0)
{
uint8_t v___x_828_; 
lean_inc(v_a_814_);
v___x_828_ = l_Lean_Exception_isRuntime(v_a_814_);
v___y_819_ = v___x_828_;
goto v___jp_818_;
}
else
{
v___y_819_ = v___x_827_;
goto v___jp_818_;
}
v___jp_818_:
{
if (v___y_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_822_; 
lean_dec(v_a_814_);
v___x_820_ = lean_box(0);
if (v_isShared_817_ == 0)
{
lean_ctor_set_tag(v___x_816_, 0);
lean_ctor_set(v___x_816_, 0, v___x_820_);
v___x_822_ = v___x_816_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
else
{
lean_object* v___x_825_; 
if (v_isShared_817_ == 0)
{
v___x_825_ = v___x_816_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_814_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_addArg_x3f___boxed(lean_object* v_matcherApp_830_, lean_object* v_e_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Meta_MatcherApp_addArg_x3f(v_matcherApp_830_, v_e_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(lean_object* v_type_838_, lean_object* v_k_839_, uint8_t v_cleanupAnnotations_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v___f_846_; uint8_t v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___f_846_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_846_, 0, v_k_839_);
v___x_847_ = 0;
v___x_848_ = lean_box(0);
v___x_849_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_847_, v___x_848_, v_type_838_, v___f_846_, v_cleanupAnnotations_840_, v___x_847_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
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
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
v_a_858_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_849_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_849_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg___boxed(lean_object* v_type_866_, lean_object* v_k_867_, lean_object* v_cleanupAnnotations_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_874_; lean_object* v_res_875_; 
v_cleanupAnnotations_boxed_874_ = lean_unbox(v_cleanupAnnotations_868_);
v_res_875_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_type_866_, v_k_867_, v_cleanupAnnotations_boxed_874_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(lean_object* v_00_u03b1_876_, lean_object* v_type_877_, lean_object* v_k_878_, uint8_t v_cleanupAnnotations_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_type_877_, v_k_878_, v_cleanupAnnotations_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___boxed(lean_object* v_00_u03b1_886_, lean_object* v_type_887_, lean_object* v_k_888_, lean_object* v_cleanupAnnotations_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_895_; lean_object* v_res_896_; 
v_cleanupAnnotations_boxed_895_ = lean_unbox(v_cleanupAnnotations_889_);
v_res_896_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3(v_00_u03b1_886_, v_type_887_, v_k_888_, v_cleanupAnnotations_boxed_895_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(size_t v_sz_897_, size_t v_i_898_, lean_object* v_bs_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v___x_905_; 
v___x_905_ = lean_usize_dec_lt(v_i_898_, v_sz_897_);
if (v___x_905_ == 0)
{
lean_object* v___x_906_; 
v___x_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_906_, 0, v_bs_899_);
return v___x_906_;
}
else
{
lean_object* v_v_907_; lean_object* v___x_908_; 
v_v_907_ = lean_array_uget_borrowed(v_bs_899_, v_i_898_);
lean_inc(v___y_903_);
lean_inc_ref(v___y_902_);
lean_inc(v___y_901_);
lean_inc_ref(v___y_900_);
lean_inc(v_v_907_);
v___x_908_ = lean_infer_type(v_v_907_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; lean_object* v_bs_x27_911_; size_t v___x_912_; size_t v___x_913_; lean_object* v___x_914_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = lean_unsigned_to_nat(0u);
v_bs_x27_911_ = lean_array_uset(v_bs_899_, v_i_898_, v___x_910_);
v___x_912_ = ((size_t)1ULL);
v___x_913_ = lean_usize_add(v_i_898_, v___x_912_);
v___x_914_ = lean_array_uset(v_bs_x27_911_, v_i_898_, v_a_909_);
v_i_898_ = v___x_913_;
v_bs_899_ = v___x_914_;
goto _start;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec_ref(v_bs_899_);
v_a_916_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_908_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_908_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1___boxed(lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_bs_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
size_t v_sz_boxed_932_; size_t v_i_boxed_933_; lean_object* v_res_934_; 
v_sz_boxed_932_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_933_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_934_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_sz_boxed_932_, v_i_boxed_933_, v_bs_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
return v_res_934_;
}
}
static lean_object* _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__0));
v___x_937_ = l_Lean_stringToMessageData(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(uint8_t v___x_938_, uint8_t v___x_939_, uint8_t v___x_940_, lean_object* v_a_941_, lean_object* v_fvs_942_, lean_object* v_body_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = lean_array_get_size(v_fvs_942_);
v___x_958_ = lean_nat_dec_eq(v___x_957_, v_a_941_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v___x_959_ = lean_obj_once(&l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1, &l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1_once, _init_l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___closed__1);
v___x_960_ = l_Nat_reprFast(v_a_941_);
v___x_961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
v___x_962_ = l_Lean_MessageData_ofFormat(v___x_961_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_959_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_963_);
lean_ctor_set(v___x_965_, 1, v___x_964_);
v___x_966_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_965_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
lean_dec(v_a_941_);
goto v___jp_949_;
}
v___jp_949_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_950_ = lean_unsigned_to_nat(2u);
v___x_951_ = l_Lean_Expr_getAppNumArgs(v_body_943_);
v___x_952_ = lean_nat_sub(v___x_951_, v___x_950_);
lean_dec(v___x_951_);
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_sub(v___x_952_, v___x_953_);
lean_dec(v___x_952_);
v___x_955_ = l_Lean_Expr_getRevArg_x21(v_body_943_, v___x_954_);
v___x_956_ = l_Lean_Meta_mkLambdaFVars(v_fvs_942_, v___x_955_, v___x_938_, v___x_939_, v___x_938_, v___x_939_, v___x_940_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed(lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v_a_978_, lean_object* v_fvs_979_, lean_object* v_body_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
uint8_t v___x_4262__boxed_986_; uint8_t v___x_4263__boxed_987_; uint8_t v___x_4264__boxed_988_; lean_object* v_res_989_; 
v___x_4262__boxed_986_ = lean_unbox(v___x_975_);
v___x_4263__boxed_987_ = lean_unbox(v___x_976_);
v___x_4264__boxed_988_ = lean_unbox(v___x_977_);
v_res_989_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0(v___x_4262__boxed_986_, v___x_4263__boxed_987_, v___x_4264__boxed_988_, v_a_978_, v_fvs_979_, v_body_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec_ref(v_body_980_);
lean_dec_ref(v_fvs_979_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(lean_object* v_as_990_, lean_object* v_bs_991_, lean_object* v_i_992_, lean_object* v_cs_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_array_get_size(v_as_990_);
v___x_1000_ = lean_nat_dec_lt(v_i_992_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; 
lean_dec(v_i_992_);
v___x_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1001_, 0, v_cs_993_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; uint8_t v___x_1003_; 
v___x_1002_ = lean_array_get_size(v_bs_991_);
v___x_1003_ = lean_nat_dec_lt(v_i_992_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_object* v___x_1004_; 
lean_dec(v_i_992_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v_cs_993_);
return v___x_1004_;
}
else
{
uint8_t v___x_1005_; uint8_t v___x_1006_; lean_object* v_a_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___f_1011_; lean_object* v_b_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1005_ = 0;
v___x_1006_ = 1;
v_a_1007_ = lean_array_fget_borrowed(v_as_990_, v_i_992_);
v___x_1008_ = lean_box(v___x_1005_);
v___x_1009_ = lean_box(v___x_1003_);
v___x_1010_ = lean_box(v___x_1006_);
lean_inc_n(v_a_1007_, 2);
v___f_1011_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___lam__0___boxed), 11, 4);
lean_closure_set(v___f_1011_, 0, v___x_1008_);
lean_closure_set(v___f_1011_, 1, v___x_1009_);
lean_closure_set(v___f_1011_, 2, v___x_1010_);
lean_closure_set(v___f_1011_, 3, v_a_1007_);
v_b_1012_ = lean_array_fget_borrowed(v_bs_991_, v_i_992_);
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v_a_1007_);
lean_inc(v_b_1012_);
v___x_1014_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_b_1012_, v___x_1013_, v___f_1011_, v___x_1005_, v___x_1005_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v_a_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_nat_add(v_i_992_, v___x_1016_);
lean_dec(v_i_992_);
v___x_1018_ = lean_array_push(v_cs_993_, v_a_1015_);
v_i_992_ = v___x_1017_;
v_cs_993_ = v___x_1018_;
goto _start;
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_dec_ref(v_cs_993_);
lean_dec(v_i_992_);
v_a_1020_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1014_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1014_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2___boxed(lean_object* v_as_1028_, lean_object* v_bs_1029_, lean_object* v_i_1030_, lean_object* v_cs_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v_as_1028_, v_bs_1029_, v_i_1030_, v_cs_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_bs_1029_);
lean_dec_ref(v_as_1028_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0(lean_object* v_matcherApp_1040_, lean_object* v_altAuxs_1041_, lean_object* v_x_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
size_t v_sz_1048_; size_t v___x_1049_; lean_object* v___x_1050_; 
v_sz_1048_ = lean_array_size(v_altAuxs_1041_);
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_refineThrough_spec__1(v_sz_1048_, v___x_1049_, v_altAuxs_1041_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_1040_);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_1055_ = l_Array_zipWithMAux___at___00Lean_Meta_MatcherApp_refineThrough_spec__2(v___x_1052_, v_a_1051_, v___x_1053_, v___x_1054_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v_a_1051_);
lean_dec_ref(v___x_1052_);
return v___x_1055_;
}
else
{
lean_dec_ref(v_matcherApp_1040_);
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed(lean_object* v_matcherApp_1056_, lean_object* v_altAuxs_1057_, lean_object* v_x_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Meta_MatcherApp_refineThrough___lam__0(v_matcherApp_1056_, v_altAuxs_1057_, v_x_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v_x_1058_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(lean_object* v___x_1065_, lean_object* v_motiveArgs_1066_, lean_object* v_i_1067_, lean_object* v_a_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_zero_1074_; uint8_t v_isZero_1075_; 
v_zero_1074_ = lean_unsigned_to_nat(0u);
v_isZero_1075_ = lean_nat_dec_eq(v_i_1067_, v_zero_1074_);
if (v_isZero_1075_ == 1)
{
lean_object* v___x_1076_; 
lean_dec(v_i_1067_);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v_a_1068_);
return v___x_1076_;
}
else
{
lean_object* v_one_1077_; lean_object* v_n_1078_; lean_object* v_discr_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v_one_1077_ = lean_unsigned_to_nat(1u);
v_n_1078_ = lean_nat_sub(v_i_1067_, v_one_1077_);
lean_dec(v_i_1067_);
v_discr_1079_ = lean_array_fget_borrowed(v___x_1065_, v_n_1078_);
v___x_1080_ = lean_box(0);
lean_inc(v_discr_1079_);
v___x_1081_ = l_Lean_Meta_kabstract(v_a_1068_, v_discr_1079_, v___x_1080_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v_motiveArg_1084_; lean_object* v___x_1085_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = l_Lean_instInhabitedExpr;
v_motiveArg_1084_ = lean_array_get_borrowed(v___x_1083_, v_motiveArgs_1066_, v_n_1078_);
v___x_1085_ = lean_expr_instantiate1(v_a_1082_, v_motiveArg_1084_);
lean_dec(v_a_1082_);
v_i_1067_ = v_n_1078_;
v_a_1068_ = v___x_1085_;
goto _start;
}
else
{
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1087_; 
v_a_1087_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1081_, 1);
v_i_1067_ = v_n_1078_;
v_a_1068_ = v_a_1087_;
goto _start;
}
else
{
lean_dec(v_n_1078_);
return v___x_1081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg___boxed(lean_object* v___x_1089_, lean_object* v_motiveArgs_1090_, lean_object* v_i_1091_, lean_object* v_a_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v___x_1089_, v_motiveArgs_1090_, v_i_1091_, v_a_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec_ref(v_motiveArgs_1090_);
lean_dec_ref(v___x_1089_);
return v_res_1098_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__0));
v___x_1101_ = l_Lean_stringToMessageData(v___x_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__2));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1(lean_object* v___f_1105_, lean_object* v_discrs_1106_, lean_object* v_e_1107_, lean_object* v_toMatcherInfo_1108_, lean_object* v_params_1109_, lean_object* v_matcherName_1110_, lean_object* v_matcherLevels_1111_, lean_object* v_motiveArgs_1112_, lean_object* v___motiveBody_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v___y_1120_; lean_object* v___y_1121_; uint8_t v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v_matcherLevels_1143_; lean_object* v___y_1144_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1218_ = lean_array_get_size(v_motiveArgs_1112_);
v___x_1219_ = lean_array_get_size(v_discrs_1106_);
v___x_1220_ = lean_nat_dec_eq(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v_matcherLevels_1111_);
lean_dec(v_matcherName_1110_);
lean_dec_ref(v_e_1107_);
lean_dec_ref(v___f_1105_);
v___x_1221_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__3);
v___x_1222_ = l_Nat_reprFast(v___x_1219_);
v___x_1223_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
v___x_1224_ = l_Lean_MessageData_ofFormat(v___x_1223_);
v___x_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1221_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_1227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1225_);
lean_ctor_set(v___x_1227_, 1, v___x_1226_);
v___x_1228_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1227_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
else
{
v___y_1188_ = v___y_1114_;
v___y_1189_ = v___y_1115_;
v___y_1190_ = v___y_1116_;
v___y_1191_ = v___y_1117_;
goto v___jp_1187_;
}
v___jp_1119_:
{
lean_object* v___x_1127_; 
lean_inc(v___y_1126_);
lean_inc_ref(v___y_1125_);
lean_inc(v___y_1124_);
lean_inc_ref(v___y_1123_);
v___x_1127_ = lean_infer_type(v___y_1121_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1129_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_MatcherApp_refineThrough_spec__3___redArg(v_a_1128_, v___y_1120_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1129_;
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v___y_1120_);
v_a_1130_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1127_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1127_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
v___jp_1138_:
{
uint8_t v___x_1148_; uint8_t v___x_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; 
v___x_1148_ = 0;
v___x_1149_ = 1;
v___x_1150_ = 1;
v___x_1151_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_1112_, v___y_1142_, v___x_1148_, v___x_1149_, v___x_1148_, v___x_1149_, v___x_1150_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = lean_array_to_list(v_matcherLevels_1143_);
v___x_1154_ = l_Lean_mkConst(v___y_1140_, v___x_1153_);
v___x_1155_ = l_Lean_mkAppN(v___x_1154_, v___y_1139_);
v___x_1156_ = l_Lean_Expr_app___override(v___x_1155_, v_a_1152_);
v___x_1157_ = l_Lean_mkAppN(v___x_1156_, v___y_1141_);
lean_inc_ref(v___x_1157_);
v___x_1158_ = l_Lean_Meta_isTypeCorrect(v___x_1157_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; uint8_t v___x_1160_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
v___x_1160_ = lean_unbox(v_a_1159_);
lean_dec(v_a_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v___x_1157_);
lean_dec_ref(v___f_1105_);
v___x_1161_ = lean_obj_once(&l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1, &l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1_once, _init_l_Lean_Meta_MatcherApp_refineThrough___lam__1___closed__1);
v___x_1162_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_1161_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
else
{
v___y_1120_ = v___f_1105_;
v___y_1121_ = v___x_1157_;
v___y_1122_ = v___x_1148_;
v___y_1123_ = v___y_1144_;
v___y_1124_ = v___y_1145_;
v___y_1125_ = v___y_1146_;
v___y_1126_ = v___y_1147_;
goto v___jp_1119_;
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_dec_ref(v___x_1157_);
lean_dec_ref(v___f_1105_);
v_a_1171_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1158_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1158_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
else
{
lean_object* v_a_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1186_; 
lean_dec_ref(v_matcherLevels_1143_);
lean_dec(v___y_1140_);
lean_dec_ref(v___f_1105_);
v_a_1179_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1186_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1181_ = v___x_1151_;
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_a_1179_);
lean_dec(v___x_1151_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1186_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1184_; 
if (v_isShared_1182_ == 0)
{
v___x_1184_ = v___x_1181_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_a_1179_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
v___jp_1187_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_array_get_size(v_discrs_1106_);
v___x_1193_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v_discrs_1106_, v_motiveArgs_1112_, v___x_1192_, v_e_1107_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc_n(v_a_1194_, 2);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = l_Lean_Meta_mkEq(v_a_1194_, v_a_1194_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_uElimPos_x3f_1196_; 
v_uElimPos_x3f_1196_ = lean_ctor_get(v_toMatcherInfo_1108_, 3);
if (lean_obj_tag(v_uElimPos_x3f_1196_) == 0)
{
lean_object* v_a_1197_; 
v_a_1197_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1195_, 1);
v___y_1139_ = v_params_1109_;
v___y_1140_ = v_matcherName_1110_;
v___y_1141_ = v_discrs_1106_;
v___y_1142_ = v_a_1197_;
v_matcherLevels_1143_ = v_matcherLevels_1111_;
v___y_1144_ = v___y_1188_;
v___y_1145_ = v___y_1189_;
v___y_1146_ = v___y_1190_;
v___y_1147_ = v___y_1191_;
goto v___jp_1138_;
}
else
{
lean_object* v_a_1198_; lean_object* v_val_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_a_1198_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1195_, 1);
v_val_1199_ = lean_ctor_get(v_uElimPos_x3f_1196_, 0);
v___x_1200_ = lean_box(0);
v___x_1201_ = lean_array_set(v_matcherLevels_1111_, v_val_1199_, v___x_1200_);
v___y_1139_ = v_params_1109_;
v___y_1140_ = v_matcherName_1110_;
v___y_1141_ = v_discrs_1106_;
v___y_1142_ = v_a_1198_;
v_matcherLevels_1143_ = v___x_1201_;
v___y_1144_ = v___y_1188_;
v___y_1145_ = v___y_1189_;
v___y_1146_ = v___y_1190_;
v___y_1147_ = v___y_1191_;
goto v___jp_1138_;
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec_ref(v_matcherLevels_1111_);
lean_dec(v_matcherName_1110_);
lean_dec_ref(v___f_1105_);
v_a_1202_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1195_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1195_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v_matcherLevels_1111_);
lean_dec(v_matcherName_1110_);
lean_dec_ref(v___f_1105_);
v_a_1210_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1193_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1193_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed(lean_object* v___f_1237_, lean_object* v_discrs_1238_, lean_object* v_e_1239_, lean_object* v_toMatcherInfo_1240_, lean_object* v_params_1241_, lean_object* v_matcherName_1242_, lean_object* v_matcherLevels_1243_, lean_object* v_motiveArgs_1244_, lean_object* v___motiveBody_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Meta_MatcherApp_refineThrough___lam__1(v___f_1237_, v_discrs_1238_, v_e_1239_, v_toMatcherInfo_1240_, v_params_1241_, v_matcherName_1242_, v_matcherLevels_1243_, v_motiveArgs_1244_, v___motiveBody_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec_ref(v___motiveBody_1245_);
lean_dec_ref(v_motiveArgs_1244_);
lean_dec_ref(v_params_1241_);
lean_dec_ref(v_toMatcherInfo_1240_);
lean_dec_ref(v_discrs_1238_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough(lean_object* v_matcherApp_1252_, lean_object* v_e_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_toMatcherInfo_1259_; lean_object* v_matcherName_1260_; lean_object* v_matcherLevels_1261_; lean_object* v_params_1262_; lean_object* v_motive_1263_; lean_object* v_discrs_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; uint8_t v___x_1267_; lean_object* v___x_1268_; 
v_toMatcherInfo_1259_ = lean_ctor_get(v_matcherApp_1252_, 0);
lean_inc_ref(v_toMatcherInfo_1259_);
v_matcherName_1260_ = lean_ctor_get(v_matcherApp_1252_, 1);
lean_inc(v_matcherName_1260_);
v_matcherLevels_1261_ = lean_ctor_get(v_matcherApp_1252_, 2);
lean_inc_ref(v_matcherLevels_1261_);
v_params_1262_ = lean_ctor_get(v_matcherApp_1252_, 3);
lean_inc_ref(v_params_1262_);
v_motive_1263_ = lean_ctor_get(v_matcherApp_1252_, 4);
lean_inc_ref(v_motive_1263_);
v_discrs_1264_ = lean_ctor_get(v_matcherApp_1252_, 5);
lean_inc_ref(v_discrs_1264_);
v___f_1265_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1265_, 0, v_matcherApp_1252_);
v___f_1266_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_refineThrough___lam__1___boxed), 14, 7);
lean_closure_set(v___f_1266_, 0, v___f_1265_);
lean_closure_set(v___f_1266_, 1, v_discrs_1264_);
lean_closure_set(v___f_1266_, 2, v_e_1253_);
lean_closure_set(v___f_1266_, 3, v_toMatcherInfo_1259_);
lean_closure_set(v___f_1266_, 4, v_params_1262_);
lean_closure_set(v___f_1266_, 5, v_matcherName_1260_);
lean_closure_set(v___f_1266_, 6, v_matcherLevels_1261_);
v___x_1267_ = 0;
v___x_1268_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_1263_, v___f_1266_, v___x_1267_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough___boxed(lean_object* v_matcherApp_1269_, lean_object* v_e_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1269_, v_e_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(lean_object* v___x_1277_, lean_object* v_motiveArgs_1278_, lean_object* v_n_1279_, lean_object* v_i_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___redArg(v___x_1277_, v_motiveArgs_1278_, v_i_1280_, v_a_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0___boxed(lean_object* v___x_1289_, lean_object* v_motiveArgs_1290_, lean_object* v_n_1291_, lean_object* v_i_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00Lean_Meta_MatcherApp_refineThrough_spec__0(v___x_1289_, v_motiveArgs_1290_, v_n_1291_, v_i_1292_, v_a_1293_, v_a_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1296_);
lean_dec_ref(v___y_1295_);
lean_dec(v_n_1291_);
lean_dec_ref(v_motiveArgs_1290_);
lean_dec_ref(v___x_1289_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f(lean_object* v_matcherApp_1301_, lean_object* v_e_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_MatcherApp_refineThrough(v_matcherApp_1301_, v_e_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1309_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1333_; 
v_a_1318_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1320_ = v___x_1308_;
v_isShared_1321_ = v_isSharedCheck_1333_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1308_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1333_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
uint8_t v___y_1323_; uint8_t v___x_1331_; 
v___x_1331_ = l_Lean_Exception_isInterrupt(v_a_1318_);
if (v___x_1331_ == 0)
{
uint8_t v___x_1332_; 
lean_inc(v_a_1318_);
v___x_1332_ = l_Lean_Exception_isRuntime(v_a_1318_);
v___y_1323_ = v___x_1332_;
goto v___jp_1322_;
}
else
{
v___y_1323_ = v___x_1331_;
goto v___jp_1322_;
}
v___jp_1322_:
{
if (v___y_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
lean_dec(v_a_1318_);
v___x_1324_ = lean_box(0);
if (v_isShared_1321_ == 0)
{
lean_ctor_set_tag(v___x_1320_, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1324_);
v___x_1326_ = v___x_1320_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
else
{
lean_object* v___x_1329_; 
if (v_isShared_1321_ == 0)
{
v___x_1329_ = v___x_1320_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1318_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_refineThrough_x3f___boxed(lean_object* v_matcherApp_1334_, lean_object* v_e_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Meta_MatcherApp_refineThrough_x3f(v_matcherApp_1334_, v_e_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(lean_object* v_lctx_1342_, lean_object* v_x_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v_keyedConfig_1349_; uint8_t v_trackZetaDelta_1350_; lean_object* v_zetaDeltaSet_1351_; lean_object* v_localInstances_1352_; lean_object* v_defEqCtx_x3f_1353_; lean_object* v_synthPendingDepth_1354_; lean_object* v_canUnfold_x3f_1355_; uint8_t v_univApprox_1356_; uint8_t v_inTypeClassResolution_1357_; uint8_t v_cacheInferType_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_keyedConfig_1349_ = lean_ctor_get(v___y_1344_, 0);
v_trackZetaDelta_1350_ = lean_ctor_get_uint8(v___y_1344_, sizeof(void*)*7);
v_zetaDeltaSet_1351_ = lean_ctor_get(v___y_1344_, 1);
v_localInstances_1352_ = lean_ctor_get(v___y_1344_, 3);
v_defEqCtx_x3f_1353_ = lean_ctor_get(v___y_1344_, 4);
v_synthPendingDepth_1354_ = lean_ctor_get(v___y_1344_, 5);
v_canUnfold_x3f_1355_ = lean_ctor_get(v___y_1344_, 6);
v_univApprox_1356_ = lean_ctor_get_uint8(v___y_1344_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1357_ = lean_ctor_get_uint8(v___y_1344_, sizeof(void*)*7 + 2);
v_cacheInferType_1358_ = lean_ctor_get_uint8(v___y_1344_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_1355_);
lean_inc(v_synthPendingDepth_1354_);
lean_inc(v_defEqCtx_x3f_1353_);
lean_inc_ref(v_localInstances_1352_);
lean_inc(v_zetaDeltaSet_1351_);
lean_inc_ref(v_keyedConfig_1349_);
v___x_1359_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1359_, 0, v_keyedConfig_1349_);
lean_ctor_set(v___x_1359_, 1, v_zetaDeltaSet_1351_);
lean_ctor_set(v___x_1359_, 2, v_lctx_1342_);
lean_ctor_set(v___x_1359_, 3, v_localInstances_1352_);
lean_ctor_set(v___x_1359_, 4, v_defEqCtx_x3f_1353_);
lean_ctor_set(v___x_1359_, 5, v_synthPendingDepth_1354_);
lean_ctor_set(v___x_1359_, 6, v_canUnfold_x3f_1355_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*7, v_trackZetaDelta_1350_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*7 + 1, v_univApprox_1356_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1357_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*7 + 3, v_cacheInferType_1358_);
lean_inc(v___y_1347_);
lean_inc_ref(v___y_1346_);
lean_inc(v___y_1345_);
v___x_1360_ = lean_apply_5(v_x_1343_, v___x_1359_, v___y_1345_, v___y_1346_, v___y_1347_, lean_box(0));
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg___boxed(lean_object* v_lctx_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1361_, v_x_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(lean_object* v_00_u03b1_1369_, lean_object* v_lctx_1370_, lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1370_, v_x_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___boxed(lean_object* v_00_u03b1_1378_, lean_object* v_lctx_1379_, lean_object* v_x_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0(v_00_u03b1_1378_, v_lctx_1379_, v_x_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(lean_object* v_as_1387_, size_t v_i_1388_, size_t v_stop_1389_, lean_object* v_b_1390_){
_start:
{
uint8_t v___x_1391_; 
v___x_1391_ = lean_usize_dec_eq(v_i_1388_, v_stop_1389_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v_fst_1393_; lean_object* v_snd_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; size_t v___x_1397_; size_t v___x_1398_; 
v___x_1392_ = lean_array_uget_borrowed(v_as_1387_, v_i_1388_);
v_fst_1393_ = lean_ctor_get(v___x_1392_, 0);
v_snd_1394_ = lean_ctor_get(v___x_1392_, 1);
v___x_1395_ = l_Lean_Expr_fvarId_x21(v_fst_1393_);
lean_inc(v_snd_1394_);
v___x_1396_ = l_Lean_LocalContext_setUserName(v_b_1390_, v___x_1395_, v_snd_1394_);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_i_1388_, v___x_1397_);
v_i_1388_ = v___x_1398_;
v_b_1390_ = v___x_1396_;
goto _start;
}
else
{
return v_b_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1___boxed(lean_object* v_as_1400_, lean_object* v_i_1401_, lean_object* v_stop_1402_, lean_object* v_b_1403_){
_start:
{
size_t v_i_boxed_1404_; size_t v_stop_boxed_1405_; lean_object* v_res_1406_; 
v_i_boxed_1404_ = lean_unbox_usize(v_i_1401_);
lean_dec(v_i_1401_);
v_stop_boxed_1405_ = lean_unbox_usize(v_stop_1402_);
lean_dec(v_stop_1402_);
v_res_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v_as_1400_, v_i_boxed_1404_, v_stop_boxed_1405_, v_b_1403_);
lean_dec_ref(v_as_1400_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(lean_object* v_fvars_1407_, lean_object* v_names_1408_, lean_object* v_k_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_lctx_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_lctx_1415_ = lean_ctor_get(v_a_1410_, 2);
v___x_1416_ = l_Array_zip___redArg(v_fvars_1407_, v_names_1408_);
v___x_1417_ = lean_unsigned_to_nat(0u);
v___x_1418_ = lean_array_get_size(v___x_1416_);
v___x_1419_ = lean_nat_dec_lt(v___x_1417_, v___x_1418_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; 
lean_dec_ref(v___x_1416_);
lean_inc_ref(v_lctx_1415_);
v___x_1420_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1415_, v_k_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
return v___x_1420_;
}
else
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_nat_dec_le(v___x_1418_, v___x_1418_);
if (v___x_1421_ == 0)
{
if (v___x_1419_ == 0)
{
lean_object* v___x_1422_; 
lean_dec_ref(v___x_1416_);
lean_inc_ref(v_lctx_1415_);
v___x_1422_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v_lctx_1415_, v_k_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
return v___x_1422_;
}
else
{
size_t v___x_1423_; size_t v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1423_ = ((size_t)0ULL);
v___x_1424_ = lean_usize_of_nat(v___x_1418_);
lean_inc_ref(v_lctx_1415_);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1416_, v___x_1423_, v___x_1424_, v_lctx_1415_);
lean_dec_ref(v___x_1416_);
v___x_1426_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1425_, v_k_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
return v___x_1426_;
}
}
else
{
size_t v___x_1427_; size_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1427_ = ((size_t)0ULL);
v___x_1428_ = lean_usize_of_nat(v___x_1418_);
lean_inc_ref(v_lctx_1415_);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__1(v___x_1416_, v___x_1427_, v___x_1428_, v_lctx_1415_);
lean_dec_ref(v___x_1416_);
v___x_1430_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl_spec__0___redArg(v___x_1429_, v_k_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg___boxed(lean_object* v_fvars_1431_, lean_object* v_names_1432_, lean_object* v_k_1433_, lean_object* v_a_1434_, lean_object* v_a_1435_, lean_object* v_a_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1431_, v_names_1432_, v_k_1433_, v_a_1434_, v_a_1435_, v_a_1436_, v_a_1437_);
lean_dec(v_a_1437_);
lean_dec_ref(v_a_1436_);
lean_dec(v_a_1435_);
lean_dec_ref(v_a_1434_);
lean_dec_ref(v_names_1432_);
lean_dec_ref(v_fvars_1431_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(lean_object* v_00_u03b1_1440_, lean_object* v_fvars_1441_, lean_object* v_names_1442_, lean_object* v_k_1443_, lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1441_, v_names_1442_, v_k_1443_, v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_fvars_1451_, lean_object* v_names_1452_, lean_object* v_k_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_, lean_object* v_a_1456_, lean_object* v_a_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl(v_00_u03b1_1450_, v_fvars_1451_, v_names_1452_, v_k_1453_, v_a_1454_, v_a_1455_, v_a_1456_, v_a_1457_);
lean_dec(v_a_1457_);
lean_dec_ref(v_a_1456_);
lean_dec(v_a_1455_);
lean_dec_ref(v_a_1454_);
lean_dec_ref(v_names_1452_);
lean_dec_ref(v_fvars_1451_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(lean_object* v_k_1460_, lean_object* v_fvars_1461_, lean_object* v_names_1462_, lean_object* v_runInBase_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_apply_2(v_runInBase_1463_, lean_box(0), v_k_1460_);
v___x_1470_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_1461_, v_names_1462_, v___x_1469_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed(lean_object* v_k_1471_, lean_object* v_fvars_1472_, lean_object* v_names_1473_, lean_object* v_runInBase_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0(v_k_1471_, v_fvars_1472_, v_names_1473_, v_runInBase_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec_ref(v_names_1473_);
lean_dec_ref(v_fvars_1472_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___redArg(lean_object* v_inst_1481_, lean_object* v_inst_1482_, lean_object* v_fvars_1483_, lean_object* v_names_1484_, lean_object* v_k_1485_){
_start:
{
lean_object* v_toBind_1486_; lean_object* v_liftWith_1487_; lean_object* v_restoreM_1488_; lean_object* v___f_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_toBind_1486_ = lean_ctor_get(v_inst_1482_, 1);
lean_inc(v_toBind_1486_);
lean_dec_ref(v_inst_1482_);
v_liftWith_1487_ = lean_ctor_get(v_inst_1481_, 0);
lean_inc(v_liftWith_1487_);
v_restoreM_1488_ = lean_ctor_get(v_inst_1481_, 1);
lean_inc(v_restoreM_1488_);
lean_dec_ref(v_inst_1481_);
v___f_1489_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_withUserNames___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_1489_, 0, v_k_1485_);
lean_closure_set(v___f_1489_, 1, v_fvars_1483_);
lean_closure_set(v___f_1489_, 2, v_names_1484_);
v___x_1490_ = lean_apply_2(v_liftWith_1487_, lean_box(0), v___f_1489_);
v___x_1491_ = lean_apply_1(v_restoreM_1488_, lean_box(0));
v___x_1492_ = lean_apply_4(v_toBind_1486_, lean_box(0), lean_box(0), v___x_1490_, v___x_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames(lean_object* v_n_1493_, lean_object* v_inst_1494_, lean_object* v_inst_1495_, lean_object* v_00_u03b1_1496_, lean_object* v_fvars_1497_, lean_object* v_names_1498_, lean_object* v_k_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_1494_, v_inst_1495_, v_fvars_1497_, v_names_1498_, v_k_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(lean_object* v_k_1501_, lean_object* v_runInBase_1502_, lean_object* v_ys_1503_, lean_object* v_args_1504_, lean_object* v___mask_1505_, lean_object* v___bodyType_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_apply_2(v_k_1501_, v_ys_1503_, v_args_1504_);
lean_inc(v___y_1510_);
lean_inc_ref(v___y_1509_);
lean_inc(v___y_1508_);
lean_inc_ref(v___y_1507_);
v___x_1513_ = lean_apply_7(v_runInBase_1502_, lean_box(0), v___x_1512_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, lean_box(0));
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed(lean_object* v_k_1514_, lean_object* v_runInBase_1515_, lean_object* v_ys_1516_, lean_object* v_args_1517_, lean_object* v___mask_1518_, lean_object* v___bodyType_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0(v_k_1514_, v_runInBase_1515_, v_ys_1516_, v_args_1517_, v___mask_1518_, v___bodyType_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec_ref(v___bodyType_1519_);
lean_dec_ref(v___mask_1518_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(lean_object* v_k_1526_, lean_object* v_origAltType_1527_, lean_object* v_altInfo_1528_, lean_object* v_runInBase_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_){
_start:
{
lean_object* v___f_1535_; lean_object* v___x_1536_; 
v___f_1535_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__0___boxed), 11, 2);
lean_closure_set(v___f_1535_, 0, v_k_1526_);
lean_closure_set(v___f_1535_, 1, v_runInBase_1529_);
v___x_1536_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_1527_, v_altInfo_1528_, v___f_1535_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed(lean_object* v_k_1537_, lean_object* v_origAltType_1538_, lean_object* v_altInfo_1539_, lean_object* v_runInBase_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1(v_k_1537_, v_origAltType_1538_, v_altInfo_1539_, v_runInBase_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(lean_object* v_inst_1547_, lean_object* v_inst_1548_, lean_object* v_origAltType_1549_, lean_object* v_altInfo_1550_, lean_object* v_k_1551_){
_start:
{
lean_object* v_toBind_1552_; lean_object* v_liftWith_1553_; lean_object* v_restoreM_1554_; lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_toBind_1552_ = lean_ctor_get(v_inst_1547_, 1);
lean_inc(v_toBind_1552_);
lean_dec_ref(v_inst_1547_);
v_liftWith_1553_ = lean_ctor_get(v_inst_1548_, 0);
lean_inc(v_liftWith_1553_);
v_restoreM_1554_ = lean_ctor_get(v_inst_1548_, 1);
lean_inc(v_restoreM_1554_);
lean_dec_ref(v_inst_1548_);
v___f_1555_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg___lam__1___boxed), 9, 3);
lean_closure_set(v___f_1555_, 0, v_k_1551_);
lean_closure_set(v___f_1555_, 1, v_origAltType_1549_);
lean_closure_set(v___f_1555_, 2, v_altInfo_1550_);
v___x_1556_ = lean_apply_2(v_liftWith_1553_, lean_box(0), v___f_1555_);
v___x_1557_ = lean_apply_1(v_restoreM_1554_, lean_box(0));
v___x_1558_ = lean_apply_4(v_toBind_1552_, lean_box(0), lean_box(0), v___x_1556_, v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27(lean_object* v_n_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_00_u03b1_1562_, lean_object* v_origAltType_1563_, lean_object* v_altInfo_1564_, lean_object* v_k_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_1560_, v_inst_1561_, v_origAltType_1563_, v_altInfo_1564_, v_k_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_altParams(lean_object* v_fvars_1567_){
_start:
{
lean_object* v_args_1568_; lean_object* v_discrEqs_1569_; lean_object* v___x_1570_; 
v_args_1568_ = lean_ctor_get(v_fvars_1567_, 0);
lean_inc_ref(v_args_1568_);
v_discrEqs_1569_ = lean_ctor_get(v_fvars_1567_, 3);
lean_inc_ref(v_discrEqs_1569_);
lean_dec_ref(v_fvars_1567_);
v___x_1570_ = l_Array_append___redArg(v_args_1568_, v_discrEqs_1569_);
lean_dec_ref(v_discrEqs_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_TransformAltFVars_all(lean_object* v_fvars_1571_){
_start:
{
lean_object* v_fields_1572_; lean_object* v_overlaps_1573_; lean_object* v_discrEqs_1574_; lean_object* v_extraEqs_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v_fields_1572_ = lean_ctor_get(v_fvars_1571_, 1);
lean_inc_ref(v_fields_1572_);
v_overlaps_1573_ = lean_ctor_get(v_fvars_1571_, 2);
lean_inc_ref(v_overlaps_1573_);
v_discrEqs_1574_ = lean_ctor_get(v_fvars_1571_, 3);
lean_inc_ref(v_discrEqs_1574_);
v_extraEqs_1575_ = lean_ctor_get(v_fvars_1571_, 4);
lean_inc_ref(v_extraEqs_1575_);
lean_dec_ref(v_fvars_1571_);
v___x_1576_ = l_Array_append___redArg(v_fields_1572_, v_overlaps_1573_);
lean_dec_ref(v_overlaps_1573_);
v___x_1577_ = l_Array_append___redArg(v___x_1576_, v_discrEqs_1574_);
lean_dec_ref(v_discrEqs_1574_);
v___x_1578_ = l_Array_append___redArg(v___x_1577_, v_extraEqs_1575_);
lean_dec_ref(v_extraEqs_1575_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0(lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_1583_ = l_Lean_throwError___redArg(v_inst_1579_, v_inst_1580_, v___x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed(lean_object* v_inst_1584_, lean_object* v_inst_1585_, lean_object* v_x_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__0(v_inst_1584_, v_inst_1585_, v_x_1586_);
lean_dec_ref(v_x_1586_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1(lean_object* v_inst_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = l_Lean_Expr_fvarId_x21(v_x_1589_);
v___x_1591_ = lean_alloc_closure((void*)(l_Lean_FVarId_getUserName___boxed), 6, 1);
lean_closure_set(v___x_1591_, 0, v___x_1590_);
v___x_1592_ = lean_apply_2(v_inst_1588_, lean_box(0), v___x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed(lean_object* v_inst_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__1(v_inst_1593_, v_x_1594_);
lean_dec_ref(v_x_1594_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2(lean_object* v_inst_1596_, lean_object* v___f_1597_, lean_object* v_xs_1598_, lean_object* v_x_1599_){
_start:
{
size_t v_sz_1600_; size_t v___x_1601_; lean_object* v___x_1602_; 
v_sz_1600_ = lean_array_size(v_xs_1598_);
v___x_1601_ = ((size_t)0ULL);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_1596_, v___f_1597_, v_sz_1600_, v___x_1601_, v_xs_1598_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed(lean_object* v_inst_1603_, lean_object* v___f_1604_, lean_object* v_xs_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__2(v_inst_1603_, v___f_1604_, v_xs_1605_, v_x_1606_);
lean_dec_ref(v_x_1606_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__3(lean_object* v_toPure_1608_, lean_object* v_____do__lift_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_apply_2(v_toPure_1608_, lean_box(0), v_____do__lift_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__4(lean_object* v_toPure_1611_, lean_object* v_____do__lift_1612_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_apply_2(v_toPure_1611_, lean_box(0), v_____do__lift_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5(lean_object* v_fst_1614_, lean_object* v_fst_1615_, lean_object* v___x_1616_, lean_object* v___x_1617_, lean_object* v_toPure_1618_, lean_object* v_____do__lift_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1620_ = lean_array_push(v_fst_1614_, v_____do__lift_1619_);
v___x_1621_ = lean_nat_add(v_fst_1615_, v___x_1616_);
v___x_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
lean_ctor_set(v___x_1622_, 1, v___x_1617_);
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1620_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
v___x_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
v___x_1625_ = lean_apply_2(v_toPure_1618_, lean_box(0), v___x_1624_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed(lean_object* v_fst_1626_, lean_object* v_fst_1627_, lean_object* v___x_1628_, lean_object* v___x_1629_, lean_object* v_toPure_1630_, lean_object* v_____do__lift_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__5(v_fst_1626_, v_fst_1627_, v___x_1628_, v___x_1629_, v_toPure_1630_, v_____do__lift_1631_);
lean_dec(v___x_1628_);
lean_dec(v_fst_1627_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6(uint8_t v_val_1633_, lean_object* v_a_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
if (v_val_1633_ == 0)
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Lean_Meta_mkEqRefl(v_a_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_mkHEqRefl(v_a_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed(lean_object* v_val_1642_, lean_object* v_a_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
uint8_t v_val_13926__boxed_1649_; lean_object* v_res_1650_; 
v_val_13926__boxed_1649_ = lean_unbox(v_val_1642_);
v_res_1650_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__6(v_val_13926__boxed_1649_, v_a_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__7(lean_object* v_toPure_1651_, lean_object* v_inst_1652_, lean_object* v_toBind_1653_, lean_object* v_a_1654_, lean_object* v_x_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_snd_1657_; lean_object* v_snd_1658_; lean_object* v_fst_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1707_; 
v_snd_1657_ = lean_ctor_get(v___y_1656_, 1);
lean_inc(v_snd_1657_);
v_snd_1658_ = lean_ctor_get(v_snd_1657_, 1);
lean_inc(v_snd_1658_);
v_fst_1659_ = lean_ctor_get(v___y_1656_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___y_1656_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v___y_1656_, 1);
lean_dec(v_unused_1708_);
v___x_1661_ = v___y_1656_;
v_isShared_1662_ = v_isSharedCheck_1707_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_fst_1659_);
lean_dec(v___y_1656_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1707_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v_fst_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1705_; 
v_fst_1663_ = lean_ctor_get(v_snd_1657_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_snd_1657_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v_snd_1657_, 1);
lean_dec(v_unused_1706_);
v___x_1665_ = v_snd_1657_;
v_isShared_1666_ = v_isSharedCheck_1705_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_fst_1663_);
lean_dec(v_snd_1657_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1705_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_array_1667_; lean_object* v_start_1668_; lean_object* v_stop_1669_; uint8_t v___x_1670_; 
v_array_1667_ = lean_ctor_get(v_snd_1658_, 0);
v_start_1668_ = lean_ctor_get(v_snd_1658_, 1);
v_stop_1669_ = lean_ctor_get(v_snd_1658_, 2);
v___x_1670_ = lean_nat_dec_lt(v_start_1668_, v_stop_1669_);
if (v___x_1670_ == 0)
{
lean_object* v___x_1672_; 
lean_dec_ref(v_a_1654_);
lean_dec(v_toBind_1653_);
lean_dec(v_inst_1652_);
if (v_isShared_1666_ == 0)
{
v___x_1672_ = v___x_1665_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_fst_1663_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v_snd_1658_);
v___x_1672_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v___x_1672_);
v___x_1674_ = v___x_1661_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_fst_1659_);
lean_ctor_set(v_reuseFailAlloc_1677_, 1, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
v___x_1676_ = lean_apply_2(v_toPure_1651_, lean_box(0), v___x_1675_);
return v___x_1676_;
}
}
}
else
{
lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1701_; 
lean_inc(v_stop_1669_);
lean_inc(v_start_1668_);
lean_inc_ref(v_array_1667_);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_snd_1658_);
if (v_isSharedCheck_1701_ == 0)
{
lean_object* v_unused_1702_; lean_object* v_unused_1703_; lean_object* v_unused_1704_; 
v_unused_1702_ = lean_ctor_get(v_snd_1658_, 2);
lean_dec(v_unused_1702_);
v_unused_1703_ = lean_ctor_get(v_snd_1658_, 1);
lean_dec(v_unused_1703_);
v_unused_1704_ = lean_ctor_get(v_snd_1658_, 0);
lean_dec(v_unused_1704_);
v___x_1680_ = v_snd_1658_;
v_isShared_1681_ = v_isSharedCheck_1701_;
goto v_resetjp_1679_;
}
else
{
lean_dec(v_snd_1658_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1701_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1682_ = lean_array_fget(v_array_1667_, v_start_1668_);
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_add(v_start_1668_, v___x_1683_);
lean_dec(v_start_1668_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v___x_1684_);
v___x_1686_ = v___x_1680_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_array_1667_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1700_, 2, v_stop_1669_);
v___x_1686_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v___x_1688_; 
lean_dec_ref(v_a_1654_);
lean_dec(v_toBind_1653_);
lean_dec(v_inst_1652_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 1, v___x_1686_);
v___x_1688_ = v___x_1665_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_fst_1663_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1690_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v___x_1688_);
v___x_1690_ = v___x_1661_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_fst_1659_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
v___x_1692_ = lean_apply_2(v_toPure_1651_, lean_box(0), v___x_1691_);
return v___x_1692_;
}
}
}
else
{
lean_object* v_val_1695_; lean_object* v___f_1696_; lean_object* v___f_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_del_object(v___x_1665_);
lean_del_object(v___x_1661_);
v_val_1695_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_val_1695_);
lean_dec_ref_known(v___x_1682_, 1);
v___f_1696_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__5___boxed), 6, 5);
lean_closure_set(v___f_1696_, 0, v_fst_1659_);
lean_closure_set(v___f_1696_, 1, v_fst_1663_);
lean_closure_set(v___f_1696_, 2, v___x_1683_);
lean_closure_set(v___f_1696_, 3, v___x_1686_);
lean_closure_set(v___f_1696_, 4, v_toPure_1651_);
v___f_1697_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__6___boxed), 7, 2);
lean_closure_set(v___f_1697_, 0, v_val_1695_);
lean_closure_set(v___f_1697_, 1, v_a_1654_);
v___x_1698_ = lean_apply_2(v_inst_1652_, lean_box(0), v___f_1697_);
v___x_1699_ = lean_apply_4(v_toBind_1653_, lean_box(0), lean_box(0), v___x_1698_, v___f_1696_);
return v___x_1699_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8(lean_object* v_heq_1709_, lean_object* v_fst_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_mkArrow(v_heq_1709_, v_fst_1710_, v___y_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed(lean_object* v_heq_1717_, lean_object* v_fst_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__8(v_heq_1717_, v_fst_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9(lean_object* v_heq_1727_, lean_object* v_fst_1728_, lean_object* v_fst_1729_, lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v_toPure_1732_, lean_object* v_motiveBody_x27_1733_){
_start:
{
uint8_t v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1734_ = l_Lean_Expr_isHEq(v_heq_1727_);
v___x_1735_ = lean_box(v___x_1734_);
v___x_1736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
v___x_1737_ = lean_array_push(v_fst_1728_, v___x_1736_);
v___x_1738_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_1739_ = lean_array_push(v_fst_1729_, v___x_1738_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1730_);
lean_ctor_set(v___x_1740_, 1, v___x_1731_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v___x_1739_);
lean_ctor_set(v___x_1741_, 1, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1737_);
lean_ctor_set(v___x_1742_, 1, v___x_1741_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_motiveBody_x27_1733_);
lean_ctor_set(v___x_1743_, 1, v___x_1742_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
v___x_1745_ = lean_apply_2(v_toPure_1732_, lean_box(0), v___x_1744_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed(lean_object* v_heq_1746_, lean_object* v_fst_1747_, lean_object* v_fst_1748_, lean_object* v___x_1749_, lean_object* v___x_1750_, lean_object* v_toPure_1751_, lean_object* v_motiveBody_x27_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__9(v_heq_1746_, v_fst_1747_, v_fst_1748_, v___x_1749_, v___x_1750_, v_toPure_1751_, v_motiveBody_x27_1752_);
lean_dec_ref(v_heq_1746_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__10(lean_object* v_fst_1754_, lean_object* v_fst_1755_, lean_object* v_fst_1756_, lean_object* v___x_1757_, lean_object* v___x_1758_, lean_object* v_toPure_1759_, lean_object* v_inst_1760_, lean_object* v_toBind_1761_, lean_object* v_heq_1762_){
_start:
{
lean_object* v___f_1763_; lean_object* v___f_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
lean_inc_ref(v_heq_1762_);
v___f_1763_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__8___boxed), 7, 2);
lean_closure_set(v___f_1763_, 0, v_heq_1762_);
lean_closure_set(v___f_1763_, 1, v_fst_1754_);
v___f_1764_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___boxed), 7, 6);
lean_closure_set(v___f_1764_, 0, v_heq_1762_);
lean_closure_set(v___f_1764_, 1, v_fst_1755_);
lean_closure_set(v___f_1764_, 2, v_fst_1756_);
lean_closure_set(v___f_1764_, 3, v___x_1757_);
lean_closure_set(v___f_1764_, 4, v___x_1758_);
lean_closure_set(v___f_1764_, 5, v_toPure_1759_);
v___x_1765_ = lean_apply_2(v_inst_1760_, lean_box(0), v___f_1763_);
v___x_1766_ = lean_apply_4(v_toBind_1761_, lean_box(0), lean_box(0), v___x_1765_, v___f_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11(lean_object* v___x_1767_, lean_object* v_a_1768_, lean_object* v_inst_1769_, lean_object* v_toBind_1770_, lean_object* v___f_1771_, lean_object* v_fst_1772_, lean_object* v_fst_1773_, lean_object* v___x_1774_, lean_object* v___x_1775_, lean_object* v___x_1776_, lean_object* v_fst_1777_, lean_object* v_toPure_1778_, uint8_t v_____do__lift_1779_){
_start:
{
if (v_____do__lift_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
lean_dec(v_toPure_1778_);
lean_dec(v_fst_1777_);
lean_dec_ref(v___x_1776_);
lean_dec_ref(v___x_1775_);
lean_dec(v___x_1774_);
lean_dec(v_fst_1773_);
lean_dec(v_fst_1772_);
v___x_1780_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEqHEq___boxed), 7, 2);
lean_closure_set(v___x_1780_, 0, v___x_1767_);
lean_closure_set(v___x_1780_, 1, v_a_1768_);
v___x_1781_ = lean_apply_2(v_inst_1769_, lean_box(0), v___x_1780_);
v___x_1782_ = lean_apply_4(v_toBind_1770_, lean_box(0), lean_box(0), v___x_1781_, v___f_1771_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec(v___f_1771_);
lean_dec(v_toBind_1770_);
lean_dec(v_inst_1769_);
lean_dec_ref(v_a_1768_);
lean_dec_ref(v___x_1767_);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_array_push(v_fst_1772_, v___x_1783_);
v___x_1785_ = lean_array_push(v_fst_1773_, v___x_1774_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1775_);
lean_ctor_set(v___x_1786_, 1, v___x_1776_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v___x_1784_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_fst_1777_);
lean_ctor_set(v___x_1789_, 1, v___x_1788_);
v___x_1790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1789_);
v___x_1791_ = lean_apply_2(v_toPure_1778_, lean_box(0), v___x_1790_);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed(lean_object* v___x_1792_, lean_object* v_a_1793_, lean_object* v_inst_1794_, lean_object* v_toBind_1795_, lean_object* v___f_1796_, lean_object* v_fst_1797_, lean_object* v_fst_1798_, lean_object* v___x_1799_, lean_object* v___x_1800_, lean_object* v___x_1801_, lean_object* v_fst_1802_, lean_object* v_toPure_1803_, lean_object* v_____do__lift_1804_){
_start:
{
uint8_t v_____do__lift_14117__boxed_1805_; lean_object* v_res_1806_; 
v_____do__lift_14117__boxed_1805_ = lean_unbox(v_____do__lift_1804_);
v_res_1806_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__11(v___x_1792_, v_a_1793_, v_inst_1794_, v_toBind_1795_, v___f_1796_, v_fst_1797_, v_fst_1798_, v___x_1799_, v___x_1800_, v___x_1801_, v_fst_1802_, v_toPure_1803_, v_____do__lift_14117__boxed_1805_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12(lean_object* v_toPure_1807_, uint8_t v_addEqualities_1808_, lean_object* v_inst_1809_, lean_object* v_toBind_1810_, lean_object* v_a_1811_, lean_object* v_x_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_snd_1814_; lean_object* v_snd_1815_; lean_object* v_snd_1816_; lean_object* v_snd_1817_; lean_object* v_fst_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1924_; 
v_snd_1814_ = lean_ctor_get(v___y_1813_, 1);
lean_inc(v_snd_1814_);
v_snd_1815_ = lean_ctor_get(v_snd_1814_, 1);
lean_inc(v_snd_1815_);
v_snd_1816_ = lean_ctor_get(v_snd_1815_, 1);
lean_inc(v_snd_1816_);
v_snd_1817_ = lean_ctor_get(v_snd_1816_, 1);
lean_inc(v_snd_1817_);
v_fst_1818_ = lean_ctor_get(v___y_1813_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___y_1813_);
if (v_isSharedCheck_1924_ == 0)
{
lean_object* v_unused_1925_; 
v_unused_1925_ = lean_ctor_get(v___y_1813_, 1);
lean_dec(v_unused_1925_);
v___x_1820_ = v___y_1813_;
v_isShared_1821_ = v_isSharedCheck_1924_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_fst_1818_);
lean_dec(v___y_1813_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1924_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_fst_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1922_; 
v_fst_1822_ = lean_ctor_get(v_snd_1814_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v_snd_1814_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v_snd_1814_, 1);
lean_dec(v_unused_1923_);
v___x_1824_ = v_snd_1814_;
v_isShared_1825_ = v_isSharedCheck_1922_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_fst_1822_);
lean_dec(v_snd_1814_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1922_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_fst_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1920_; 
v_fst_1826_ = lean_ctor_get(v_snd_1815_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_snd_1815_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v_snd_1815_, 1);
lean_dec(v_unused_1921_);
v___x_1828_ = v_snd_1815_;
v_isShared_1829_ = v_isSharedCheck_1920_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_fst_1826_);
lean_dec(v_snd_1815_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1920_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_fst_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1918_; 
v_fst_1830_ = lean_ctor_get(v_snd_1816_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v_snd_1816_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v_snd_1816_, 1);
lean_dec(v_unused_1919_);
v___x_1832_ = v_snd_1816_;
v_isShared_1833_ = v_isSharedCheck_1918_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_fst_1830_);
lean_dec(v_snd_1816_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1918_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_array_1834_; lean_object* v_start_1835_; lean_object* v_stop_1836_; uint8_t v___x_1837_; 
v_array_1834_ = lean_ctor_get(v_snd_1817_, 0);
v_start_1835_ = lean_ctor_get(v_snd_1817_, 1);
v_stop_1836_ = lean_ctor_get(v_snd_1817_, 2);
v___x_1837_ = lean_nat_dec_lt(v_start_1835_, v_stop_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1839_; 
lean_dec_ref(v_a_1811_);
lean_dec(v_toBind_1810_);
lean_dec(v_inst_1809_);
if (v_isShared_1833_ == 0)
{
v___x_1839_ = v___x_1832_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_fst_1830_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_snd_1817_);
v___x_1839_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1841_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___x_1839_);
v___x_1841_ = v___x_1828_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_fst_1826_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1843_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v___x_1841_);
v___x_1843_ = v___x_1824_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_fst_1822_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1843_);
v___x_1845_ = v___x_1820_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_fst_1818_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
v___x_1847_ = lean_apply_2(v_toPure_1807_, lean_box(0), v___x_1846_);
return v___x_1847_;
}
}
}
}
}
else
{
lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1914_; 
lean_inc(v_stop_1836_);
lean_inc(v_start_1835_);
lean_inc_ref(v_array_1834_);
v_isSharedCheck_1914_ = !lean_is_exclusive(v_snd_1817_);
if (v_isSharedCheck_1914_ == 0)
{
lean_object* v_unused_1915_; lean_object* v_unused_1916_; lean_object* v_unused_1917_; 
v_unused_1915_ = lean_ctor_get(v_snd_1817_, 2);
lean_dec(v_unused_1915_);
v_unused_1916_ = lean_ctor_get(v_snd_1817_, 1);
lean_dec(v_unused_1916_);
v_unused_1917_ = lean_ctor_get(v_snd_1817_, 0);
lean_dec(v_unused_1917_);
v___x_1853_ = v_snd_1817_;
v_isShared_1854_ = v_isSharedCheck_1914_;
goto v_resetjp_1852_;
}
else
{
lean_dec(v_snd_1817_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1914_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v_array_1855_; lean_object* v_start_1856_; lean_object* v_stop_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1862_; 
v_array_1855_ = lean_ctor_get(v_fst_1830_, 0);
v_start_1856_ = lean_ctor_get(v_fst_1830_, 1);
v_stop_1857_ = lean_ctor_get(v_fst_1830_, 2);
v___x_1858_ = lean_array_fget(v_array_1834_, v_start_1835_);
v___x_1859_ = lean_unsigned_to_nat(1u);
v___x_1860_ = lean_nat_add(v_start_1835_, v___x_1859_);
lean_dec(v_start_1835_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1860_);
v___x_1862_ = v___x_1853_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_array_1834_);
lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1860_);
lean_ctor_set(v_reuseFailAlloc_1913_, 2, v_stop_1836_);
v___x_1862_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_nat_dec_lt(v_start_1856_, v_stop_1857_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1865_; 
lean_dec(v___x_1858_);
lean_dec_ref(v_a_1811_);
lean_dec(v_toBind_1810_);
lean_dec(v_inst_1809_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1862_);
v___x_1865_ = v___x_1832_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_fst_1830_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1862_);
v___x_1865_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1867_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___x_1865_);
v___x_1867_ = v___x_1828_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_fst_1826_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v___x_1867_);
v___x_1869_ = v___x_1824_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_fst_1822_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1871_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1869_);
v___x_1871_ = v___x_1820_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v_fst_1818_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
v___x_1873_ = lean_apply_2(v_toPure_1807_, lean_box(0), v___x_1872_);
return v___x_1873_;
}
}
}
}
}
else
{
lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1909_; 
lean_inc(v_stop_1857_);
lean_inc(v_start_1856_);
lean_inc_ref(v_array_1855_);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_fst_1830_);
if (v_isSharedCheck_1909_ == 0)
{
lean_object* v_unused_1910_; lean_object* v_unused_1911_; lean_object* v_unused_1912_; 
v_unused_1910_ = lean_ctor_get(v_fst_1830_, 2);
lean_dec(v_unused_1910_);
v_unused_1911_ = lean_ctor_get(v_fst_1830_, 1);
lean_dec(v_unused_1911_);
v_unused_1912_ = lean_ctor_get(v_fst_1830_, 0);
lean_dec(v_unused_1912_);
v___x_1879_ = v_fst_1830_;
v_isShared_1880_ = v_isSharedCheck_1909_;
goto v_resetjp_1878_;
}
else
{
lean_dec(v_fst_1830_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1909_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1881_ = lean_array_fget(v_array_1855_, v_start_1856_);
v___x_1882_ = lean_nat_add(v_start_1856_, v___x_1859_);
lean_dec(v_start_1856_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1882_);
v___x_1884_ = v___x_1879_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_array_1855_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_stop_1857_);
v___x_1884_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
if (v_addEqualities_1808_ == 0)
{
lean_dec(v___x_1881_);
lean_dec_ref(v_a_1811_);
lean_dec(v_toBind_1810_);
lean_dec(v_inst_1809_);
goto v___jp_1885_;
}
else
{
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v___f_1903_; lean_object* v___f_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
lean_del_object(v___x_1832_);
lean_del_object(v___x_1828_);
lean_del_object(v___x_1824_);
lean_del_object(v___x_1820_);
lean_inc_n(v_toBind_1810_, 2);
lean_inc_n(v_inst_1809_, 2);
lean_inc(v_toPure_1807_);
lean_inc_ref(v___x_1862_);
lean_inc_ref(v___x_1884_);
lean_inc(v_fst_1826_);
lean_inc(v_fst_1822_);
lean_inc(v_fst_1818_);
v___f_1903_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__10), 9, 8);
lean_closure_set(v___f_1903_, 0, v_fst_1818_);
lean_closure_set(v___f_1903_, 1, v_fst_1822_);
lean_closure_set(v___f_1903_, 2, v_fst_1826_);
lean_closure_set(v___f_1903_, 3, v___x_1884_);
lean_closure_set(v___f_1903_, 4, v___x_1862_);
lean_closure_set(v___f_1903_, 5, v_toPure_1807_);
lean_closure_set(v___f_1903_, 6, v_inst_1809_);
lean_closure_set(v___f_1903_, 7, v_toBind_1810_);
lean_inc_ref(v_a_1811_);
v___f_1904_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__11___boxed), 13, 12);
lean_closure_set(v___f_1904_, 0, v___x_1881_);
lean_closure_set(v___f_1904_, 1, v_a_1811_);
lean_closure_set(v___f_1904_, 2, v_inst_1809_);
lean_closure_set(v___f_1904_, 3, v_toBind_1810_);
lean_closure_set(v___f_1904_, 4, v___f_1903_);
lean_closure_set(v___f_1904_, 5, v_fst_1822_);
lean_closure_set(v___f_1904_, 6, v_fst_1826_);
lean_closure_set(v___f_1904_, 7, v___x_1858_);
lean_closure_set(v___f_1904_, 8, v___x_1884_);
lean_closure_set(v___f_1904_, 9, v___x_1862_);
lean_closure_set(v___f_1904_, 10, v_fst_1818_);
lean_closure_set(v___f_1904_, 11, v_toPure_1807_);
v___x_1905_ = lean_alloc_closure((void*)(l_Lean_Meta_isProof___boxed), 6, 1);
lean_closure_set(v___x_1905_, 0, v_a_1811_);
v___x_1906_ = lean_apply_2(v_inst_1809_, lean_box(0), v___x_1905_);
v___x_1907_ = lean_apply_4(v_toBind_1810_, lean_box(0), lean_box(0), v___x_1906_, v___f_1904_);
return v___x_1907_;
}
else
{
lean_dec(v___x_1881_);
lean_dec_ref(v_a_1811_);
lean_dec(v_toBind_1810_);
lean_dec(v_inst_1809_);
goto v___jp_1885_;
}
}
v___jp_1885_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = lean_array_push(v_fst_1822_, v___x_1886_);
v___x_1888_ = lean_array_push(v_fst_1826_, v___x_1858_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v___x_1862_);
lean_ctor_set(v___x_1832_, 0, v___x_1884_);
v___x_1890_ = v___x_1832_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v___x_1862_);
v___x_1890_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1892_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___x_1890_);
lean_ctor_set(v___x_1828_, 0, v___x_1888_);
v___x_1892_ = v___x_1828_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v___x_1890_);
v___x_1892_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1894_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 1, v___x_1892_);
lean_ctor_set(v___x_1824_, 0, v___x_1887_);
v___x_1894_ = v___x_1824_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1887_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1892_);
v___x_1894_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
lean_object* v___x_1896_; 
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1894_);
v___x_1896_ = v___x_1820_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_fst_1818_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v___x_1898_ = lean_apply_2(v_toPure_1807_, lean_box(0), v___x_1897_);
return v___x_1898_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed(lean_object* v_toPure_1926_, lean_object* v_addEqualities_1927_, lean_object* v_inst_1928_, lean_object* v_toBind_1929_, lean_object* v_a_1930_, lean_object* v_x_1931_, lean_object* v___y_1932_){
_start:
{
uint8_t v_addEqualities_boxed_1933_; lean_object* v_res_1934_; 
v_addEqualities_boxed_1933_ = lean_unbox(v_addEqualities_1927_);
v_res_1934_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__12(v_toPure_1926_, v_addEqualities_boxed_1933_, v_inst_1928_, v_toBind_1929_, v_a_1930_, v_x_1931_, v___y_1932_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__13(lean_object* v_fst_1935_, lean_object* v_fst_1936_, lean_object* v_____do__lift_1937_, lean_object* v_toPure_1938_, lean_object* v_____do__lift_1939_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v_fst_1935_);
lean_ctor_set(v___x_1940_, 1, v_fst_1936_);
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v_____do__lift_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1942_, 0, v_____do__lift_1937_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_apply_2(v_toPure_1938_, lean_box(0), v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__14(lean_object* v_fst_1944_, lean_object* v_fst_1945_, lean_object* v_toPure_1946_, lean_object* v_fst_1947_, lean_object* v_inst_1948_, lean_object* v_toBind_1949_, lean_object* v_____do__lift_1950_){
_start:
{
lean_object* v___f_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___f_1951_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__13), 5, 4);
lean_closure_set(v___f_1951_, 0, v_fst_1944_);
lean_closure_set(v___f_1951_, 1, v_fst_1945_);
lean_closure_set(v___f_1951_, 2, v_____do__lift_1950_);
lean_closure_set(v___f_1951_, 3, v_toPure_1946_);
v___x_1952_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1952_, 0, v_fst_1947_);
v___x_1953_ = lean_apply_2(v_inst_1948_, lean_box(0), v___x_1952_);
v___x_1954_ = lean_apply_4(v_toBind_1949_, lean_box(0), lean_box(0), v___x_1953_, v___f_1951_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__15(lean_object* v_toPure_1955_, lean_object* v_inst_1956_, lean_object* v_toBind_1957_, lean_object* v_motiveArgs_1958_, lean_object* v_____s_1959_){
_start:
{
lean_object* v_snd_1960_; lean_object* v_snd_1961_; lean_object* v_fst_1962_; lean_object* v_fst_1963_; lean_object* v_fst_1964_; lean_object* v___f_1965_; uint8_t v___x_1966_; uint8_t v___x_1967_; uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_snd_1960_ = lean_ctor_get(v_____s_1959_, 1);
lean_inc(v_snd_1960_);
v_snd_1961_ = lean_ctor_get(v_snd_1960_, 1);
lean_inc(v_snd_1961_);
v_fst_1962_ = lean_ctor_get(v_____s_1959_, 0);
lean_inc_n(v_fst_1962_, 2);
lean_dec_ref(v_____s_1959_);
v_fst_1963_ = lean_ctor_get(v_snd_1960_, 0);
lean_inc(v_fst_1963_);
lean_dec(v_snd_1960_);
v_fst_1964_ = lean_ctor_get(v_snd_1961_, 0);
lean_inc(v_fst_1964_);
lean_dec(v_snd_1961_);
lean_inc(v_toBind_1957_);
lean_inc(v_inst_1956_);
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__14), 7, 6);
lean_closure_set(v___f_1965_, 0, v_fst_1963_);
lean_closure_set(v___f_1965_, 1, v_fst_1964_);
lean_closure_set(v___f_1965_, 2, v_toPure_1955_);
lean_closure_set(v___f_1965_, 3, v_fst_1962_);
lean_closure_set(v___f_1965_, 4, v_inst_1956_);
lean_closure_set(v___f_1965_, 5, v_toBind_1957_);
v___x_1966_ = 0;
v___x_1967_ = 1;
v___x_1968_ = 1;
v___x_1969_ = lean_box(v___x_1966_);
v___x_1970_ = lean_box(v___x_1967_);
v___x_1971_ = lean_box(v___x_1966_);
v___x_1972_ = lean_box(v___x_1967_);
v___x_1973_ = lean_box(v___x_1968_);
v___x_1974_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1974_, 0, v_motiveArgs_1958_);
lean_closure_set(v___x_1974_, 1, v_fst_1962_);
lean_closure_set(v___x_1974_, 2, v___x_1969_);
lean_closure_set(v___x_1974_, 3, v___x_1970_);
lean_closure_set(v___x_1974_, 4, v___x_1971_);
lean_closure_set(v___x_1974_, 5, v___x_1972_);
lean_closure_set(v___x_1974_, 6, v___x_1973_);
v___x_1975_ = lean_apply_2(v_inst_1956_, lean_box(0), v___x_1974_);
v___x_1976_ = lean_apply_4(v_toBind_1957_, lean_box(0), lean_box(0), v___x_1975_, v___f_1965_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__16(lean_object* v_toMatcherInfo_1979_, lean_object* v_discrs_x27_1980_, lean_object* v_motiveArgs_1981_, lean_object* v_inst_1982_, lean_object* v___f_1983_, lean_object* v_toBind_1984_, lean_object* v___f_1985_, lean_object* v_motiveBody_x27_1986_){
_start:
{
lean_object* v_discrInfos_1987_; lean_object* v___x_1988_; lean_object* v_addHEqualities_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; size_t v_sz_1998_; size_t v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v_discrInfos_1987_ = lean_ctor_get(v_toMatcherInfo_1979_, 4);
lean_inc_ref(v_discrInfos_1987_);
lean_dec_ref(v_toMatcherInfo_1979_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v_addHEqualities_1989_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_1990_ = lean_array_get_size(v_discrs_x27_1980_);
v___x_1991_ = l_Array_toSubarray___redArg(v_discrs_x27_1980_, v___x_1988_, v___x_1990_);
v___x_1992_ = lean_array_get_size(v_discrInfos_1987_);
v___x_1993_ = l_Array_toSubarray___redArg(v_discrInfos_1987_, v___x_1988_, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1991_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v_addHEqualities_1989_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_addHEqualities_1989_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_motiveBody_x27_1986_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v_sz_1998_ = lean_array_size(v_motiveArgs_1981_);
v___x_1999_ = ((size_t)0ULL);
v___x_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1982_, v_motiveArgs_1981_, v___f_1983_, v_sz_1998_, v___x_1999_, v___x_1997_);
v___x_2001_ = lean_apply_4(v_toBind_1984_, lean_box(0), lean_box(0), v___x_2000_, v___f_1985_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__17(lean_object* v_onMotive_2002_, lean_object* v_motiveArgs_2003_, lean_object* v_motiveBody_2004_, lean_object* v_toBind_2005_, lean_object* v___f_2006_, lean_object* v_____r_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_apply_2(v_onMotive_2002_, v_motiveArgs_2003_, v_motiveBody_2004_);
v___x_2009_ = lean_apply_4(v_toBind_2005_, lean_box(0), lean_box(0), v___x_2008_, v___f_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__18(lean_object* v___f_2010_, lean_object* v_____r_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_apply_1(v___f_2010_, v_____r_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19(lean_object* v_toPure_2013_, lean_object* v_inst_2014_, lean_object* v_toBind_2015_, lean_object* v_toMatcherInfo_2016_, lean_object* v_discrs_x27_2017_, lean_object* v_inst_2018_, lean_object* v___f_2019_, lean_object* v_onMotive_2020_, lean_object* v_discrs_2021_, lean_object* v_inst_2022_, lean_object* v_motiveArgs_2023_, lean_object* v_motiveBody_2024_){
_start:
{
lean_object* v___f_2025_; lean_object* v___f_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
lean_inc_ref_n(v_motiveArgs_2023_, 3);
lean_inc_n(v_toBind_2015_, 3);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__15), 5, 4);
lean_closure_set(v___f_2025_, 0, v_toPure_2013_);
lean_closure_set(v___f_2025_, 1, v_inst_2014_);
lean_closure_set(v___f_2025_, 2, v_toBind_2015_);
lean_closure_set(v___f_2025_, 3, v_motiveArgs_2023_);
lean_inc_ref(v_inst_2018_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16), 8, 7);
lean_closure_set(v___f_2026_, 0, v_toMatcherInfo_2016_);
lean_closure_set(v___f_2026_, 1, v_discrs_x27_2017_);
lean_closure_set(v___f_2026_, 2, v_motiveArgs_2023_);
lean_closure_set(v___f_2026_, 3, v_inst_2018_);
lean_closure_set(v___f_2026_, 4, v___f_2019_);
lean_closure_set(v___f_2026_, 5, v_toBind_2015_);
lean_closure_set(v___f_2026_, 6, v___f_2025_);
lean_inc_ref(v___f_2026_);
lean_inc_ref(v_motiveBody_2024_);
lean_inc(v_onMotive_2020_);
v___f_2027_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__17), 6, 5);
lean_closure_set(v___f_2027_, 0, v_onMotive_2020_);
lean_closure_set(v___f_2027_, 1, v_motiveArgs_2023_);
lean_closure_set(v___f_2027_, 2, v_motiveBody_2024_);
lean_closure_set(v___f_2027_, 3, v_toBind_2015_);
lean_closure_set(v___f_2027_, 4, v___f_2026_);
v___x_2028_ = lean_array_get_size(v_motiveArgs_2023_);
v___x_2029_ = lean_array_get_size(v_discrs_2021_);
v___x_2030_ = lean_nat_dec_eq(v___x_2028_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___f_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
lean_dec_ref(v___f_2026_);
lean_dec_ref(v_motiveBody_2024_);
lean_dec_ref(v_motiveArgs_2023_);
lean_dec(v_onMotive_2020_);
v___f_2031_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__18), 2, 1);
lean_closure_set(v___f_2031_, 0, v___f_2027_);
v___x_2032_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_2033_ = l_Nat_reprFast(v___x_2029_);
v___x_2034_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
v___x_2035_ = l_Lean_MessageData_ofFormat(v___x_2034_);
v___x_2036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2032_);
lean_ctor_set(v___x_2036_, 1, v___x_2035_);
v___x_2037_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_2038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = l_Lean_throwError___redArg(v_inst_2018_, v_inst_2022_, v___x_2038_);
v___x_2040_ = lean_apply_4(v_toBind_2015_, lean_box(0), lean_box(0), v___x_2039_, v___f_2031_);
return v___x_2040_;
}
else
{
lean_object* v___x_2041_; lean_object* v___x_2042_; 
lean_dec_ref(v___f_2027_);
lean_dec_ref(v_inst_2022_);
lean_dec_ref(v_inst_2018_);
v___x_2041_ = lean_box(0);
v___x_2042_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__17(v_onMotive_2020_, v_motiveArgs_2023_, v_motiveBody_2024_, v_toBind_2015_, v___f_2026_, v___x_2041_);
return v___x_2042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed(lean_object* v_toPure_2043_, lean_object* v_inst_2044_, lean_object* v_toBind_2045_, lean_object* v_toMatcherInfo_2046_, lean_object* v_discrs_x27_2047_, lean_object* v_inst_2048_, lean_object* v___f_2049_, lean_object* v_onMotive_2050_, lean_object* v_discrs_2051_, lean_object* v_inst_2052_, lean_object* v_motiveArgs_2053_, lean_object* v_motiveBody_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__19(v_toPure_2043_, v_inst_2044_, v_toBind_2045_, v_toMatcherInfo_2046_, v_discrs_x27_2047_, v_inst_2048_, v___f_2049_, v_onMotive_2050_, v_discrs_2051_, v_inst_2052_, v_motiveArgs_2053_, v_motiveBody_2054_);
lean_dec_ref(v_discrs_2051_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20(lean_object* v_fst_2056_, lean_object* v_numParams_2057_, lean_object* v_numDiscrs_2058_, lean_object* v_altInfos_2059_, lean_object* v_uElimPos_x3f_2060_, lean_object* v_snd_2061_, lean_object* v_overlaps_2062_, lean_object* v_matcherName_2063_, lean_object* v_matcherLevels_2064_, lean_object* v_params_x27_2065_, lean_object* v_fst_2066_, lean_object* v_discrs_x27_2067_, lean_object* v_fst_2068_, lean_object* v_toPure_2069_, lean_object* v_____do__lift_2070_){
_start:
{
lean_object* v_remaining_x27_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_remaining_x27_2071_ = l_Array_append___redArg(v_fst_2056_, v_____do__lift_2070_);
v___x_2072_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2072_, 0, v_numParams_2057_);
lean_ctor_set(v___x_2072_, 1, v_numDiscrs_2058_);
lean_ctor_set(v___x_2072_, 2, v_altInfos_2059_);
lean_ctor_set(v___x_2072_, 3, v_uElimPos_x3f_2060_);
lean_ctor_set(v___x_2072_, 4, v_snd_2061_);
lean_ctor_set(v___x_2072_, 5, v_overlaps_2062_);
v___x_2073_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2072_);
lean_ctor_set(v___x_2073_, 1, v_matcherName_2063_);
lean_ctor_set(v___x_2073_, 2, v_matcherLevels_2064_);
lean_ctor_set(v___x_2073_, 3, v_params_x27_2065_);
lean_ctor_set(v___x_2073_, 4, v_fst_2066_);
lean_ctor_set(v___x_2073_, 5, v_discrs_x27_2067_);
lean_ctor_set(v___x_2073_, 6, v_fst_2068_);
lean_ctor_set(v___x_2073_, 7, v_remaining_x27_2071_);
v___x_2074_ = lean_apply_2(v_toPure_2069_, lean_box(0), v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed(lean_object* v_fst_2075_, lean_object* v_numParams_2076_, lean_object* v_numDiscrs_2077_, lean_object* v_altInfos_2078_, lean_object* v_uElimPos_x3f_2079_, lean_object* v_snd_2080_, lean_object* v_overlaps_2081_, lean_object* v_matcherName_2082_, lean_object* v_matcherLevels_2083_, lean_object* v_params_x27_2084_, lean_object* v_fst_2085_, lean_object* v_discrs_x27_2086_, lean_object* v_fst_2087_, lean_object* v_toPure_2088_, lean_object* v_____do__lift_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__20(v_fst_2075_, v_numParams_2076_, v_numDiscrs_2077_, v_altInfos_2078_, v_uElimPos_x3f_2079_, v_snd_2080_, v_overlaps_2081_, v_matcherName_2082_, v_matcherLevels_2083_, v_params_x27_2084_, v_fst_2085_, v_discrs_x27_2086_, v_fst_2087_, v_toPure_2088_, v_____do__lift_2089_);
lean_dec_ref(v_____do__lift_2089_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21(lean_object* v_fst_2091_, lean_object* v_numParams_2092_, lean_object* v_numDiscrs_2093_, lean_object* v_altInfos_2094_, lean_object* v_uElimPos_x3f_2095_, lean_object* v_snd_2096_, lean_object* v_overlaps_2097_, lean_object* v_matcherName_2098_, lean_object* v_matcherLevels_2099_, lean_object* v_params_x27_2100_, lean_object* v_fst_2101_, lean_object* v_discrs_x27_2102_, lean_object* v_toPure_2103_, lean_object* v_onRemaining_2104_, lean_object* v_remaining_2105_, lean_object* v_toBind_2106_, lean_object* v_____s_2107_){
_start:
{
lean_object* v_fst_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_fst_2108_ = lean_ctor_get(v_____s_2107_, 0);
lean_inc(v_fst_2108_);
lean_dec_ref(v_____s_2107_);
v___f_2109_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__20___boxed), 15, 14);
lean_closure_set(v___f_2109_, 0, v_fst_2091_);
lean_closure_set(v___f_2109_, 1, v_numParams_2092_);
lean_closure_set(v___f_2109_, 2, v_numDiscrs_2093_);
lean_closure_set(v___f_2109_, 3, v_altInfos_2094_);
lean_closure_set(v___f_2109_, 4, v_uElimPos_x3f_2095_);
lean_closure_set(v___f_2109_, 5, v_snd_2096_);
lean_closure_set(v___f_2109_, 6, v_overlaps_2097_);
lean_closure_set(v___f_2109_, 7, v_matcherName_2098_);
lean_closure_set(v___f_2109_, 8, v_matcherLevels_2099_);
lean_closure_set(v___f_2109_, 9, v_params_x27_2100_);
lean_closure_set(v___f_2109_, 10, v_fst_2101_);
lean_closure_set(v___f_2109_, 11, v_discrs_x27_2102_);
lean_closure_set(v___f_2109_, 12, v_fst_2108_);
lean_closure_set(v___f_2109_, 13, v_toPure_2103_);
v___x_2110_ = lean_apply_1(v_onRemaining_2104_, v_remaining_2105_);
v___x_2111_ = lean_apply_4(v_toBind_2106_, lean_box(0), lean_box(0), v___x_2110_, v___f_2109_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed(lean_object** _args){
lean_object* v_fst_2112_ = _args[0];
lean_object* v_numParams_2113_ = _args[1];
lean_object* v_numDiscrs_2114_ = _args[2];
lean_object* v_altInfos_2115_ = _args[3];
lean_object* v_uElimPos_x3f_2116_ = _args[4];
lean_object* v_snd_2117_ = _args[5];
lean_object* v_overlaps_2118_ = _args[6];
lean_object* v_matcherName_2119_ = _args[7];
lean_object* v_matcherLevels_2120_ = _args[8];
lean_object* v_params_x27_2121_ = _args[9];
lean_object* v_fst_2122_ = _args[10];
lean_object* v_discrs_x27_2123_ = _args[11];
lean_object* v_toPure_2124_ = _args[12];
lean_object* v_onRemaining_2125_ = _args[13];
lean_object* v_remaining_2126_ = _args[14];
lean_object* v_toBind_2127_ = _args[15];
lean_object* v_____s_2128_ = _args[16];
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__21(v_fst_2112_, v_numParams_2113_, v_numDiscrs_2114_, v_altInfos_2115_, v_uElimPos_x3f_2116_, v_snd_2117_, v_overlaps_2118_, v_matcherName_2119_, v_matcherLevels_2120_, v_params_x27_2121_, v_fst_2122_, v_discrs_x27_2123_, v_toPure_2124_, v_onRemaining_2125_, v_remaining_2126_, v_toBind_2127_, v_____s_2128_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22(lean_object* v_toPure_2130_, lean_object* v_next_2131_, lean_object* v_G_2132_, lean_object* v_____do__lift_2133_){
_start:
{
if (lean_obj_tag(v_____do__lift_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
lean_dec(v_G_2132_);
v_a_2134_ = lean_ctor_get(v_____do__lift_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v_____do__lift_2133_, 1);
v___x_2135_ = lean_apply_2(v_toPure_2130_, lean_box(0), v_a_2134_);
return v___x_2135_;
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v_toPure_2130_);
v_a_2136_ = lean_ctor_get(v_____do__lift_2133_, 0);
lean_inc(v_a_2136_);
lean_dec_ref_known(v_____do__lift_2133_, 1);
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_add(v_next_2131_, v___x_2137_);
v___x_2139_ = lean_apply_4(v_G_2132_, v___x_2138_, v_a_2136_, lean_box(0), lean_box(0));
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed(lean_object* v_toPure_2140_, lean_object* v_next_2141_, lean_object* v_G_2142_, lean_object* v_____do__lift_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__22(v_toPure_2140_, v_next_2141_, v_G_2142_, v_____do__lift_2143_);
lean_dec(v_next_2141_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23(lean_object* v_xs_2145_, lean_object* v_ys4_2146_, uint8_t v___x_2147_, uint8_t v___x_2148_, lean_object* v_inst_2149_, lean_object* v_alt_x27_2150_){
_start:
{
lean_object* v___x_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2151_ = l_Array_append___redArg(v_xs_2145_, v_ys4_2146_);
v___x_2152_ = 1;
v___x_2153_ = lean_box(v___x_2147_);
v___x_2154_ = lean_box(v___x_2148_);
v___x_2155_ = lean_box(v___x_2147_);
v___x_2156_ = lean_box(v___x_2148_);
v___x_2157_ = lean_box(v___x_2152_);
v___x_2158_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2158_, 0, v___x_2151_);
lean_closure_set(v___x_2158_, 1, v_alt_x27_2150_);
lean_closure_set(v___x_2158_, 2, v___x_2153_);
lean_closure_set(v___x_2158_, 3, v___x_2154_);
lean_closure_set(v___x_2158_, 4, v___x_2155_);
lean_closure_set(v___x_2158_, 5, v___x_2156_);
lean_closure_set(v___x_2158_, 6, v___x_2157_);
v___x_2159_ = lean_apply_2(v_inst_2149_, lean_box(0), v___x_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed(lean_object* v_xs_2160_, lean_object* v_ys4_2161_, lean_object* v___x_2162_, lean_object* v___x_2163_, lean_object* v_inst_2164_, lean_object* v_alt_x27_2165_){
_start:
{
uint8_t v___x_14562__boxed_2166_; uint8_t v___x_14563__boxed_2167_; lean_object* v_res_2168_; 
v___x_14562__boxed_2166_ = lean_unbox(v___x_2162_);
v___x_14563__boxed_2167_ = lean_unbox(v___x_2163_);
v_res_2168_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__23(v_xs_2160_, v_ys4_2161_, v___x_14562__boxed_2166_, v___x_14563__boxed_2167_, v_inst_2164_, v_alt_x27_2165_);
lean_dec_ref(v_ys4_2161_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__24(lean_object* v_xs_2169_, lean_object* v_remaining_x27_2170_, lean_object* v_ys4_2171_, lean_object* v_onAlt_2172_, lean_object* v_next_2173_, lean_object* v_altType_2174_, lean_object* v_toBind_2175_, lean_object* v___f_2176_, lean_object* v_alt_2177_){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_inc_ref(v_remaining_x27_2170_);
lean_inc_ref(v_xs_2169_);
v___x_2178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2178_, 0, v_xs_2169_);
lean_ctor_set(v___x_2178_, 1, v_xs_2169_);
lean_ctor_set(v___x_2178_, 2, v_remaining_x27_2170_);
lean_ctor_set(v___x_2178_, 3, v_remaining_x27_2170_);
lean_ctor_set(v___x_2178_, 4, v_ys4_2171_);
v___x_2179_ = lean_apply_4(v_onAlt_2172_, v_next_2173_, v_altType_2174_, v___x_2178_, v_alt_2177_);
v___x_2180_ = lean_apply_4(v_toBind_2175_, lean_box(0), lean_box(0), v___x_2179_, v___f_2176_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__25(lean_object* v___x_2181_, lean_object* v_xs_2182_, lean_object* v_inst_2183_, lean_object* v_toBind_2184_, lean_object* v___f_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_names_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_inc_ref(v_xs_2182_);
v___x_2189_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2189_, 0, v___x_2181_);
lean_closure_set(v___x_2189_, 1, v_xs_2182_);
v___x_2190_ = lean_apply_2(v_inst_2183_, lean_box(0), v___x_2189_);
v___x_2191_ = lean_apply_4(v_toBind_2184_, lean_box(0), lean_box(0), v___x_2190_, v___f_2185_);
v___x_2192_ = l_Lean_Meta_MatcherApp_withUserNames___redArg(v_inst_2186_, v_inst_2187_, v_xs_2182_, v_names_2188_, v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26(lean_object* v_xs_2193_, uint8_t v___x_2194_, uint8_t v___x_2195_, lean_object* v_inst_2196_, lean_object* v_remaining_x27_2197_, lean_object* v_onAlt_2198_, lean_object* v_next_2199_, lean_object* v_toBind_2200_, lean_object* v___x_2201_, lean_object* v_inst_2202_, lean_object* v_inst_2203_, lean_object* v___f_2204_, lean_object* v_ys4_2205_, lean_object* v_altType_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___f_2210_; lean_object* v___f_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2207_ = lean_box(v___x_2194_);
v___x_2208_ = lean_box(v___x_2195_);
lean_inc(v_inst_2196_);
lean_inc_ref(v_ys4_2205_);
lean_inc_ref_n(v_xs_2193_, 2);
v___f_2209_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__23___boxed), 6, 5);
lean_closure_set(v___f_2209_, 0, v_xs_2193_);
lean_closure_set(v___f_2209_, 1, v_ys4_2205_);
lean_closure_set(v___f_2209_, 2, v___x_2207_);
lean_closure_set(v___f_2209_, 3, v___x_2208_);
lean_closure_set(v___f_2209_, 4, v_inst_2196_);
lean_inc_n(v_toBind_2200_, 2);
v___f_2210_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__24), 9, 8);
lean_closure_set(v___f_2210_, 0, v_xs_2193_);
lean_closure_set(v___f_2210_, 1, v_remaining_x27_2197_);
lean_closure_set(v___f_2210_, 2, v_ys4_2205_);
lean_closure_set(v___f_2210_, 3, v_onAlt_2198_);
lean_closure_set(v___f_2210_, 4, v_next_2199_);
lean_closure_set(v___f_2210_, 5, v_altType_2206_);
lean_closure_set(v___f_2210_, 6, v_toBind_2200_);
lean_closure_set(v___f_2210_, 7, v___f_2209_);
lean_inc_ref(v_inst_2203_);
lean_inc_ref(v_inst_2202_);
lean_inc_ref(v___x_2201_);
v___f_2211_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__25), 8, 7);
lean_closure_set(v___f_2211_, 0, v___x_2201_);
lean_closure_set(v___f_2211_, 1, v_xs_2193_);
lean_closure_set(v___f_2211_, 2, v_inst_2196_);
lean_closure_set(v___f_2211_, 3, v_toBind_2200_);
lean_closure_set(v___f_2211_, 4, v___f_2210_);
lean_closure_set(v___f_2211_, 5, v_inst_2202_);
lean_closure_set(v___f_2211_, 6, v_inst_2203_);
v___x_2212_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_2202_, v_inst_2203_, v___x_2201_, v___f_2204_, v___x_2194_);
v___x_2213_ = lean_apply_4(v_toBind_2200_, lean_box(0), lean_box(0), v___x_2212_, v___f_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed(lean_object* v_xs_2214_, lean_object* v___x_2215_, lean_object* v___x_2216_, lean_object* v_inst_2217_, lean_object* v_remaining_x27_2218_, lean_object* v_onAlt_2219_, lean_object* v_next_2220_, lean_object* v_toBind_2221_, lean_object* v___x_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v___f_2225_, lean_object* v_ys4_2226_, lean_object* v_altType_2227_){
_start:
{
uint8_t v___x_14615__boxed_2228_; uint8_t v___x_14616__boxed_2229_; lean_object* v_res_2230_; 
v___x_14615__boxed_2228_ = lean_unbox(v___x_2215_);
v___x_14616__boxed_2229_ = lean_unbox(v___x_2216_);
v_res_2230_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__26(v_xs_2214_, v___x_14615__boxed_2228_, v___x_14616__boxed_2229_, v_inst_2217_, v_remaining_x27_2218_, v_onAlt_2219_, v_next_2220_, v_toBind_2221_, v___x_2222_, v_inst_2223_, v_inst_2224_, v___f_2225_, v_ys4_2226_, v_altType_2227_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27(uint8_t v___x_2231_, uint8_t v___x_2232_, lean_object* v_inst_2233_, lean_object* v_remaining_x27_2234_, lean_object* v_onAlt_2235_, lean_object* v_next_2236_, lean_object* v_toBind_2237_, lean_object* v___x_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v___f_2241_, lean_object* v_fst_2242_, lean_object* v_xs_2243_, lean_object* v_altType_2244_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___f_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2245_ = lean_box(v___x_2231_);
v___x_2246_ = lean_box(v___x_2232_);
lean_inc_ref(v_inst_2240_);
lean_inc_ref(v_inst_2239_);
v___f_2247_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__26___boxed), 14, 12);
lean_closure_set(v___f_2247_, 0, v_xs_2243_);
lean_closure_set(v___f_2247_, 1, v___x_2245_);
lean_closure_set(v___f_2247_, 2, v___x_2246_);
lean_closure_set(v___f_2247_, 3, v_inst_2233_);
lean_closure_set(v___f_2247_, 4, v_remaining_x27_2234_);
lean_closure_set(v___f_2247_, 5, v_onAlt_2235_);
lean_closure_set(v___f_2247_, 6, v_next_2236_);
lean_closure_set(v___f_2247_, 7, v_toBind_2237_);
lean_closure_set(v___f_2247_, 8, v___x_2238_);
lean_closure_set(v___f_2247_, 9, v_inst_2239_);
lean_closure_set(v___f_2247_, 10, v_inst_2240_);
lean_closure_set(v___f_2247_, 11, v___f_2241_);
v___x_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2248_, 0, v_fst_2242_);
v___x_2249_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2239_, v_inst_2240_, v_altType_2244_, v___x_2248_, v___f_2247_, v___x_2231_, v___x_2231_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed(lean_object* v___x_2250_, lean_object* v___x_2251_, lean_object* v_inst_2252_, lean_object* v_remaining_x27_2253_, lean_object* v_onAlt_2254_, lean_object* v_next_2255_, lean_object* v_toBind_2256_, lean_object* v___x_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v___f_2260_, lean_object* v_fst_2261_, lean_object* v_xs_2262_, lean_object* v_altType_2263_){
_start:
{
uint8_t v___x_14650__boxed_2264_; uint8_t v___x_14651__boxed_2265_; lean_object* v_res_2266_; 
v___x_14650__boxed_2264_ = lean_unbox(v___x_2250_);
v___x_14651__boxed_2265_ = lean_unbox(v___x_2251_);
v_res_2266_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__27(v___x_14650__boxed_2264_, v___x_14651__boxed_2265_, v_inst_2252_, v_remaining_x27_2253_, v_onAlt_2254_, v_next_2255_, v_toBind_2256_, v___x_2257_, v_inst_2258_, v_inst_2259_, v___f_2260_, v_fst_2261_, v_xs_2262_, v_altType_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__28(lean_object* v_fst_2267_, lean_object* v___x_2268_, lean_object* v___x_2269_, lean_object* v___x_2270_, lean_object* v_toPure_2271_, lean_object* v_alt_x27_2272_){
_start:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2273_ = lean_array_push(v_fst_2267_, v_alt_x27_2272_);
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2268_);
lean_ctor_set(v___x_2274_, 1, v___x_2269_);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2270_);
lean_ctor_set(v___x_2275_, 1, v___x_2274_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2273_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
v___x_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2277_, 0, v___x_2276_);
v___x_2278_ = lean_apply_2(v_toPure_2271_, lean_box(0), v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29(lean_object* v___x_2279_, lean_object* v_toPure_2280_, lean_object* v_toBind_2281_, lean_object* v___f_2282_, uint8_t v___x_2283_, uint8_t v___x_2284_, lean_object* v_inst_2285_, lean_object* v_remaining_x27_2286_, lean_object* v_onAlt_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v___f_2290_, lean_object* v_fst_2291_, lean_object* v_next_2292_, lean_object* v_acc_2293_, lean_object* v_h_2294_, lean_object* v_G_2295_){
_start:
{
uint8_t v___x_2296_; 
v___x_2296_ = lean_nat_dec_lt(v_next_2292_, v___x_2279_);
if (v___x_2296_ == 0)
{
lean_object* v___x_2297_; 
lean_dec(v_G_2295_);
lean_dec(v_next_2292_);
lean_dec(v_fst_2291_);
lean_dec(v___f_2290_);
lean_dec_ref(v_inst_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec(v_onAlt_2287_);
lean_dec_ref(v_remaining_x27_2286_);
lean_dec(v_inst_2285_);
lean_dec(v___f_2282_);
lean_dec(v_toBind_2281_);
v___x_2297_ = lean_apply_2(v_toPure_2280_, lean_box(0), v_acc_2293_);
return v___x_2297_;
}
else
{
lean_object* v_snd_2298_; lean_object* v_snd_2299_; lean_object* v_snd_2300_; lean_object* v_fst_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2411_; 
v_snd_2298_ = lean_ctor_get(v_acc_2293_, 1);
lean_inc(v_snd_2298_);
v_snd_2299_ = lean_ctor_get(v_snd_2298_, 1);
lean_inc(v_snd_2299_);
v_snd_2300_ = lean_ctor_get(v_snd_2299_, 1);
lean_inc(v_snd_2300_);
v_fst_2301_ = lean_ctor_get(v_acc_2293_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v_acc_2293_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v_acc_2293_, 1);
lean_dec(v_unused_2412_);
v___x_2303_ = v_acc_2293_;
v_isShared_2304_ = v_isSharedCheck_2411_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_fst_2301_);
lean_dec(v_acc_2293_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2411_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_fst_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2409_; 
v_fst_2305_ = lean_ctor_get(v_snd_2298_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_snd_2298_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_snd_2298_, 1);
lean_dec(v_unused_2410_);
v___x_2307_ = v_snd_2298_;
v_isShared_2308_ = v_isSharedCheck_2409_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_fst_2305_);
lean_dec(v_snd_2298_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2409_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_fst_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2407_; 
v_fst_2309_ = lean_ctor_get(v_snd_2299_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v_snd_2299_);
if (v_isSharedCheck_2407_ == 0)
{
lean_object* v_unused_2408_; 
v_unused_2408_ = lean_ctor_get(v_snd_2299_, 1);
lean_dec(v_unused_2408_);
v___x_2311_ = v_snd_2299_;
v_isShared_2312_ = v_isSharedCheck_2407_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_fst_2309_);
lean_dec(v_snd_2299_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2407_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v_array_2313_; lean_object* v_start_2314_; lean_object* v_stop_2315_; lean_object* v___f_2316_; lean_object* v___y_2318_; uint8_t v___x_2321_; 
v_array_2313_ = lean_ctor_get(v_snd_2300_, 0);
v_start_2314_ = lean_ctor_get(v_snd_2300_, 1);
v_stop_2315_ = lean_ctor_get(v_snd_2300_, 2);
lean_inc(v_next_2292_);
lean_inc(v_toPure_2280_);
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__22___boxed), 4, 3);
lean_closure_set(v___f_2316_, 0, v_toPure_2280_);
lean_closure_set(v___f_2316_, 1, v_next_2292_);
lean_closure_set(v___f_2316_, 2, v_G_2295_);
v___x_2321_ = lean_nat_dec_lt(v_start_2314_, v_stop_2315_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2323_; 
lean_dec(v_next_2292_);
lean_dec(v_fst_2291_);
lean_dec(v___f_2290_);
lean_dec_ref(v_inst_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec(v_onAlt_2287_);
lean_dec_ref(v_remaining_x27_2286_);
lean_dec(v_inst_2285_);
if (v_isShared_2312_ == 0)
{
v___x_2323_ = v___x_2311_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_fst_2309_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_snd_2300_);
v___x_2323_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 1, v___x_2323_);
v___x_2325_ = v___x_2307_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_fst_2305_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 1, v___x_2325_);
v___x_2327_ = v___x_2303_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2301_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
v___x_2329_ = lean_apply_2(v_toPure_2280_, lean_box(0), v___x_2328_);
v___y_2318_ = v___x_2329_;
goto v___jp_2317_;
}
}
}
}
else
{
lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2403_; 
lean_inc(v_stop_2315_);
lean_inc(v_start_2314_);
lean_inc_ref(v_array_2313_);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_snd_2300_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; lean_object* v_unused_2405_; lean_object* v_unused_2406_; 
v_unused_2404_ = lean_ctor_get(v_snd_2300_, 2);
lean_dec(v_unused_2404_);
v_unused_2405_ = lean_ctor_get(v_snd_2300_, 1);
lean_dec(v_unused_2405_);
v_unused_2406_ = lean_ctor_get(v_snd_2300_, 0);
lean_dec(v_unused_2406_);
v___x_2334_ = v_snd_2300_;
v_isShared_2335_ = v_isSharedCheck_2403_;
goto v_resetjp_2333_;
}
else
{
lean_dec(v_snd_2300_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2403_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_array_2336_; lean_object* v_start_2337_; lean_object* v_stop_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v_array_2336_ = lean_ctor_get(v_fst_2309_, 0);
v_start_2337_ = lean_ctor_get(v_fst_2309_, 1);
v_stop_2338_ = lean_ctor_get(v_fst_2309_, 2);
v___x_2339_ = lean_array_fget(v_array_2313_, v_start_2314_);
v___x_2340_ = lean_unsigned_to_nat(1u);
v___x_2341_ = lean_nat_add(v_start_2314_, v___x_2340_);
lean_dec(v_start_2314_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 1, v___x_2341_);
v___x_2343_ = v___x_2334_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_array_2313_);
lean_ctor_set(v_reuseFailAlloc_2402_, 1, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2402_, 2, v_stop_2315_);
v___x_2343_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_nat_dec_lt(v_start_2337_, v_stop_2338_);
if (v___x_2344_ == 0)
{
lean_object* v___x_2346_; 
lean_dec(v___x_2339_);
lean_dec(v_next_2292_);
lean_dec(v_fst_2291_);
lean_dec(v___f_2290_);
lean_dec_ref(v_inst_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec(v_onAlt_2287_);
lean_dec_ref(v_remaining_x27_2286_);
lean_dec(v_inst_2285_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_2343_);
v___x_2346_ = v___x_2311_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_fst_2309_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v___x_2343_);
v___x_2346_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 1, v___x_2346_);
v___x_2348_ = v___x_2307_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_fst_2305_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 1, v___x_2348_);
v___x_2350_ = v___x_2303_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_fst_2301_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
v___x_2352_ = lean_apply_2(v_toPure_2280_, lean_box(0), v___x_2351_);
v___y_2318_ = v___x_2352_;
goto v___jp_2317_;
}
}
}
}
else
{
lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2398_; 
lean_inc(v_stop_2338_);
lean_inc(v_start_2337_);
lean_inc_ref(v_array_2336_);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_fst_2309_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; lean_object* v_unused_2400_; lean_object* v_unused_2401_; 
v_unused_2399_ = lean_ctor_get(v_fst_2309_, 2);
lean_dec(v_unused_2399_);
v_unused_2400_ = lean_ctor_get(v_fst_2309_, 1);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_fst_2309_, 0);
lean_dec(v_unused_2401_);
v___x_2357_ = v_fst_2309_;
v_isShared_2358_ = v_isSharedCheck_2398_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v_fst_2309_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2398_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v_array_2359_; lean_object* v_start_2360_; lean_object* v_stop_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2365_; 
v_array_2359_ = lean_ctor_get(v_fst_2305_, 0);
v_start_2360_ = lean_ctor_get(v_fst_2305_, 1);
v_stop_2361_ = lean_ctor_get(v_fst_2305_, 2);
v___x_2362_ = lean_array_fget(v_array_2336_, v_start_2337_);
v___x_2363_ = lean_nat_add(v_start_2337_, v___x_2340_);
lean_dec(v_start_2337_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 1, v___x_2363_);
v___x_2365_ = v___x_2357_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_array_2336_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2397_, 2, v_stop_2338_);
v___x_2365_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
uint8_t v___x_2366_; 
v___x_2366_ = lean_nat_dec_lt(v_start_2360_, v_stop_2361_);
if (v___x_2366_ == 0)
{
lean_object* v___x_2368_; 
lean_dec(v___x_2362_);
lean_dec(v___x_2339_);
lean_dec(v_next_2292_);
lean_dec(v_fst_2291_);
lean_dec(v___f_2290_);
lean_dec_ref(v_inst_2289_);
lean_dec_ref(v_inst_2288_);
lean_dec(v_onAlt_2287_);
lean_dec_ref(v_remaining_x27_2286_);
lean_dec(v_inst_2285_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_2343_);
lean_ctor_set(v___x_2311_, 0, v___x_2365_);
v___x_2368_ = v___x_2311_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2365_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v___x_2343_);
v___x_2368_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2370_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 1, v___x_2368_);
v___x_2370_ = v___x_2307_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_fst_2305_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v___x_2368_);
v___x_2370_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2372_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 1, v___x_2370_);
v___x_2372_ = v___x_2303_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_fst_2301_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2370_);
v___x_2372_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
v___x_2374_ = lean_apply_2(v_toPure_2280_, lean_box(0), v___x_2373_);
v___y_2318_ = v___x_2374_;
goto v___jp_2317_;
}
}
}
}
else
{
lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2393_; 
lean_inc(v_stop_2361_);
lean_inc(v_start_2360_);
lean_inc_ref(v_array_2359_);
lean_del_object(v___x_2311_);
lean_del_object(v___x_2307_);
lean_del_object(v___x_2303_);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_fst_2305_);
if (v_isSharedCheck_2393_ == 0)
{
lean_object* v_unused_2394_; lean_object* v_unused_2395_; lean_object* v_unused_2396_; 
v_unused_2394_ = lean_ctor_get(v_fst_2305_, 2);
lean_dec(v_unused_2394_);
v_unused_2395_ = lean_ctor_get(v_fst_2305_, 1);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_fst_2305_, 0);
lean_dec(v_unused_2396_);
v___x_2379_ = v_fst_2305_;
v_isShared_2380_ = v_isSharedCheck_2393_;
goto v_resetjp_2378_;
}
else
{
lean_dec(v_fst_2305_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2393_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___f_2384_; lean_object* v___x_2385_; lean_object* v___x_2387_; 
v___x_2381_ = lean_array_fget_borrowed(v_array_2359_, v_start_2360_);
v___x_2382_ = lean_box(v___x_2283_);
v___x_2383_ = lean_box(v___x_2284_);
lean_inc_ref(v_inst_2289_);
lean_inc_ref(v_inst_2288_);
lean_inc(v___x_2381_);
lean_inc(v_toBind_2281_);
v___f_2384_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__27___boxed), 14, 12);
lean_closure_set(v___f_2384_, 0, v___x_2382_);
lean_closure_set(v___f_2384_, 1, v___x_2383_);
lean_closure_set(v___f_2384_, 2, v_inst_2285_);
lean_closure_set(v___f_2384_, 3, v_remaining_x27_2286_);
lean_closure_set(v___f_2384_, 4, v_onAlt_2287_);
lean_closure_set(v___f_2384_, 5, v_next_2292_);
lean_closure_set(v___f_2384_, 6, v_toBind_2281_);
lean_closure_set(v___f_2384_, 7, v___x_2381_);
lean_closure_set(v___f_2384_, 8, v_inst_2288_);
lean_closure_set(v___f_2384_, 9, v_inst_2289_);
lean_closure_set(v___f_2384_, 10, v___f_2290_);
lean_closure_set(v___f_2384_, 11, v_fst_2291_);
v___x_2385_ = lean_nat_add(v_start_2360_, v___x_2340_);
lean_dec(v_start_2360_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v___x_2385_);
v___x_2387_ = v___x_2379_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_array_2359_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_stop_2361_);
v___x_2387_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___f_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__28), 6, 5);
lean_closure_set(v___f_2388_, 0, v_fst_2301_);
lean_closure_set(v___f_2388_, 1, v___x_2365_);
lean_closure_set(v___f_2388_, 2, v___x_2343_);
lean_closure_set(v___f_2388_, 3, v___x_2387_);
lean_closure_set(v___f_2388_, 4, v_toPure_2280_);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2362_);
v___x_2390_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2288_, v_inst_2289_, v___x_2339_, v___x_2389_, v___f_2384_, v___x_2283_, v___x_2283_);
lean_inc(v_toBind_2281_);
v___x_2391_ = lean_apply_4(v_toBind_2281_, lean_box(0), lean_box(0), v___x_2390_, v___f_2388_);
v___y_2318_ = v___x_2391_;
goto v___jp_2317_;
}
}
}
}
}
}
}
}
}
v___jp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_inc(v_toBind_2281_);
v___x_2319_ = lean_apply_4(v_toBind_2281_, lean_box(0), lean_box(0), v___y_2318_, v___f_2282_);
v___x_2320_ = lean_apply_4(v_toBind_2281_, lean_box(0), lean_box(0), v___x_2319_, v___f_2316_);
return v___x_2320_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed(lean_object** _args){
lean_object* v___x_2413_ = _args[0];
lean_object* v_toPure_2414_ = _args[1];
lean_object* v_toBind_2415_ = _args[2];
lean_object* v___f_2416_ = _args[3];
lean_object* v___x_2417_ = _args[4];
lean_object* v___x_2418_ = _args[5];
lean_object* v_inst_2419_ = _args[6];
lean_object* v_remaining_x27_2420_ = _args[7];
lean_object* v_onAlt_2421_ = _args[8];
lean_object* v_inst_2422_ = _args[9];
lean_object* v_inst_2423_ = _args[10];
lean_object* v___f_2424_ = _args[11];
lean_object* v_fst_2425_ = _args[12];
lean_object* v_next_2426_ = _args[13];
lean_object* v_acc_2427_ = _args[14];
lean_object* v_h_2428_ = _args[15];
lean_object* v_G_2429_ = _args[16];
_start:
{
uint8_t v___x_14701__boxed_2430_; uint8_t v___x_14702__boxed_2431_; lean_object* v_res_2432_; 
v___x_14701__boxed_2430_ = lean_unbox(v___x_2417_);
v___x_14702__boxed_2431_ = lean_unbox(v___x_2418_);
v_res_2432_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__29(v___x_2413_, v_toPure_2414_, v_toBind_2415_, v___f_2416_, v___x_14701__boxed_2430_, v___x_14702__boxed_2431_, v_inst_2419_, v_remaining_x27_2420_, v_onAlt_2421_, v_inst_2422_, v_inst_2423_, v___f_2424_, v_fst_2425_, v_next_2426_, v_acc_2427_, v_h_2428_, v_G_2429_);
lean_dec(v___x_2413_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__30(lean_object* v_matcherApp_2433_, lean_object* v_alts_2434_, lean_object* v___x_2435_, lean_object* v___x_2436_, lean_object* v_remaining_x27_2437_, lean_object* v___f_2438_, lean_object* v_toBind_2439_, lean_object* v___f_2440_, lean_object* v_altTypes_2441_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2442_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_2433_);
v___x_2443_ = lean_array_get_size(v___x_2442_);
v___x_2444_ = lean_array_get_size(v_altTypes_2441_);
lean_inc_n(v___x_2435_, 3);
v___x_2445_ = l_Array_toSubarray___redArg(v_alts_2434_, v___x_2435_, v___x_2436_);
v___x_2446_ = l_Array_toSubarray___redArg(v___x_2442_, v___x_2435_, v___x_2443_);
v___x_2447_ = l_Array_toSubarray___redArg(v_altTypes_2441_, v___x_2435_, v___x_2444_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2446_);
lean_ctor_set(v___x_2448_, 1, v___x_2447_);
v___x_2449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2445_);
lean_ctor_set(v___x_2449_, 1, v___x_2448_);
v___x_2450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2450_, 0, v_remaining_x27_2437_);
lean_ctor_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2438_, v___x_2435_, v___x_2450_, lean_box(0));
v___x_2452_ = lean_apply_4(v_toBind_2439_, lean_box(0), lean_box(0), v___x_2451_, v___f_2440_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31(lean_object* v_alts_2453_, lean_object* v_toPure_2454_, lean_object* v_toBind_2455_, lean_object* v___f_2456_, uint8_t v___x_2457_, uint8_t v___x_2458_, lean_object* v_inst_2459_, lean_object* v_remaining_x27_2460_, lean_object* v_onAlt_2461_, lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v___f_2464_, lean_object* v_fst_2465_, lean_object* v_matcherApp_2466_, lean_object* v___x_2467_, lean_object* v___f_2468_, lean_object* v_aux_2469_, lean_object* v_____r_2470_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___f_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2471_ = lean_array_get_size(v_alts_2453_);
v___x_2472_ = lean_box(v___x_2457_);
v___x_2473_ = lean_box(v___x_2458_);
lean_inc_ref(v_remaining_x27_2460_);
lean_inc(v_inst_2459_);
lean_inc_n(v_toBind_2455_, 2);
v___f_2474_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__29___boxed), 17, 13);
lean_closure_set(v___f_2474_, 0, v___x_2471_);
lean_closure_set(v___f_2474_, 1, v_toPure_2454_);
lean_closure_set(v___f_2474_, 2, v_toBind_2455_);
lean_closure_set(v___f_2474_, 3, v___f_2456_);
lean_closure_set(v___f_2474_, 4, v___x_2472_);
lean_closure_set(v___f_2474_, 5, v___x_2473_);
lean_closure_set(v___f_2474_, 6, v_inst_2459_);
lean_closure_set(v___f_2474_, 7, v_remaining_x27_2460_);
lean_closure_set(v___f_2474_, 8, v_onAlt_2461_);
lean_closure_set(v___f_2474_, 9, v_inst_2462_);
lean_closure_set(v___f_2474_, 10, v_inst_2463_);
lean_closure_set(v___f_2474_, 11, v___f_2464_);
lean_closure_set(v___f_2474_, 12, v_fst_2465_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__30), 9, 8);
lean_closure_set(v___f_2475_, 0, v_matcherApp_2466_);
lean_closure_set(v___f_2475_, 1, v_alts_2453_);
lean_closure_set(v___f_2475_, 2, v___x_2467_);
lean_closure_set(v___f_2475_, 3, v___x_2471_);
lean_closure_set(v___f_2475_, 4, v_remaining_x27_2460_);
lean_closure_set(v___f_2475_, 5, v___f_2474_);
lean_closure_set(v___f_2475_, 6, v_toBind_2455_);
lean_closure_set(v___f_2475_, 7, v___f_2468_);
v___x_2476_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_2476_, 0, v___x_2471_);
lean_closure_set(v___x_2476_, 1, v_aux_2469_);
v___x_2477_ = lean_apply_2(v_inst_2459_, lean_box(0), v___x_2476_);
v___x_2478_ = lean_apply_4(v_toBind_2455_, lean_box(0), lean_box(0), v___x_2477_, v___f_2475_);
return v___x_2478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_alts_2479_ = _args[0];
lean_object* v_toPure_2480_ = _args[1];
lean_object* v_toBind_2481_ = _args[2];
lean_object* v___f_2482_ = _args[3];
lean_object* v___x_2483_ = _args[4];
lean_object* v___x_2484_ = _args[5];
lean_object* v_inst_2485_ = _args[6];
lean_object* v_remaining_x27_2486_ = _args[7];
lean_object* v_onAlt_2487_ = _args[8];
lean_object* v_inst_2488_ = _args[9];
lean_object* v_inst_2489_ = _args[10];
lean_object* v___f_2490_ = _args[11];
lean_object* v_fst_2491_ = _args[12];
lean_object* v_matcherApp_2492_ = _args[13];
lean_object* v___x_2493_ = _args[14];
lean_object* v___f_2494_ = _args[15];
lean_object* v_aux_2495_ = _args[16];
lean_object* v_____r_2496_ = _args[17];
_start:
{
uint8_t v___x_14958__boxed_2497_; uint8_t v___x_14959__boxed_2498_; lean_object* v_res_2499_; 
v___x_14958__boxed_2497_ = lean_unbox(v___x_2483_);
v___x_14959__boxed_2498_ = lean_unbox(v___x_2484_);
v_res_2499_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__31(v_alts_2479_, v_toPure_2480_, v_toBind_2481_, v___f_2482_, v___x_14958__boxed_2497_, v___x_14959__boxed_2498_, v_inst_2485_, v_remaining_x27_2486_, v_onAlt_2487_, v_inst_2488_, v_inst_2489_, v___f_2490_, v_fst_2491_, v_matcherApp_2492_, v___x_2493_, v___f_2494_, v_aux_2495_, v_____r_2496_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__32(lean_object* v___x_2500_, lean_object* v_e_2501_){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = l_Lean_indentD(v_e_2501_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2500_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33(lean_object* v___x_2504_, lean_object* v___f_2505_, lean_object* v_runInBase_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_apply_2(v_runInBase_2506_, lean_box(0), v___x_2504_);
v___x_2513_ = l_Lean_Meta_mapErrorImp___redArg(v___x_2512_, v___f_2505_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed(lean_object* v___x_2514_, lean_object* v___f_2515_, lean_object* v_runInBase_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__33(v___x_2514_, v___f_2515_, v_runInBase_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35(lean_object* v_toPure_2523_, lean_object* v_next_2524_, lean_object* v_G_2525_, lean_object* v_____do__lift_2526_){
_start:
{
if (lean_obj_tag(v_____do__lift_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___x_2528_; 
lean_dec(v_G_2525_);
v_a_2527_ = lean_ctor_get(v_____do__lift_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v_____do__lift_2526_, 1);
v___x_2528_ = lean_apply_2(v_toPure_2523_, lean_box(0), v_a_2527_);
return v___x_2528_;
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v_toPure_2523_);
v_a_2529_ = lean_ctor_get(v_____do__lift_2526_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v_____do__lift_2526_, 1);
v___x_2530_ = lean_unsigned_to_nat(1u);
v___x_2531_ = lean_nat_add(v_next_2524_, v___x_2530_);
v___x_2532_ = lean_apply_4(v_G_2525_, v___x_2531_, v_a_2529_, lean_box(0), lean_box(0));
return v___x_2532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed(lean_object* v_toPure_2533_, lean_object* v_next_2534_, lean_object* v_G_2535_, lean_object* v_____do__lift_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__35(v_toPure_2533_, v_next_2534_, v_G_2535_, v_____do__lift_2536_);
lean_dec(v_next_2534_);
return v_res_2537_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2546_ = lean_box(0);
v___x_2547_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__4));
v___x_2548_ = l_Lean_mkConst(v___x_2547_, v___x_2546_);
return v___x_2548_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2549_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__5);
v___x_2550_ = lean_unsigned_to_nat(2u);
v___x_2551_ = lean_mk_empty_array_with_capacity(v___x_2550_);
v___x_2552_ = lean_array_push(v___x_2551_, v___x_2549_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34(lean_object* v___x_2553_, lean_object* v_toPure_2554_, lean_object* v_inst_2555_, lean_object* v_alt_x27_2556_){
_start:
{
uint8_t v_hasUnitThunk_2557_; 
v_hasUnitThunk_2557_ = lean_ctor_get_uint8(v___x_2553_, sizeof(void*)*2);
if (v_hasUnitThunk_2557_ == 0)
{
lean_object* v___x_2558_; 
lean_dec(v_inst_2555_);
v___x_2558_ = lean_apply_2(v_toPure_2554_, lean_box(0), v_alt_x27_2556_);
return v___x_2558_;
}
else
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec(v_toPure_2554_);
v___x_2559_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_2560_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_2561_ = lean_array_push(v___x_2560_, v_alt_x27_2556_);
v___x_2562_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___boxed), 7, 2);
lean_closure_set(v___x_2562_, 0, v___x_2559_);
lean_closure_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_apply_2(v_inst_2555_, lean_box(0), v___x_2562_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed(lean_object* v___x_2564_, lean_object* v_toPure_2565_, lean_object* v_inst_2566_, lean_object* v_alt_x27_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__34(v___x_2564_, v_toPure_2565_, v_inst_2566_, v_alt_x27_2567_);
lean_dec_ref(v___x_2564_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36(lean_object* v_ys_2569_, lean_object* v_ys2_2570_, lean_object* v_ys3_2571_, lean_object* v_ys4_2572_, uint8_t v___x_2573_, uint8_t v_useSplitter_2574_, lean_object* v_inst_2575_, lean_object* v_alt_x27_2576_){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2577_ = l_Array_append___redArg(v_ys_2569_, v_ys2_2570_);
v___x_2578_ = l_Array_append___redArg(v___x_2577_, v_ys3_2571_);
v___x_2579_ = l_Array_append___redArg(v___x_2578_, v_ys4_2572_);
v___x_2580_ = 1;
v___x_2581_ = lean_box(v___x_2573_);
v___x_2582_ = lean_box(v_useSplitter_2574_);
v___x_2583_ = lean_box(v___x_2573_);
v___x_2584_ = lean_box(v_useSplitter_2574_);
v___x_2585_ = lean_box(v___x_2580_);
v___x_2586_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_2586_, 0, v___x_2579_);
lean_closure_set(v___x_2586_, 1, v_alt_x27_2576_);
lean_closure_set(v___x_2586_, 2, v___x_2581_);
lean_closure_set(v___x_2586_, 3, v___x_2582_);
lean_closure_set(v___x_2586_, 4, v___x_2583_);
lean_closure_set(v___x_2586_, 5, v___x_2584_);
lean_closure_set(v___x_2586_, 6, v___x_2585_);
v___x_2587_ = lean_apply_2(v_inst_2575_, lean_box(0), v___x_2586_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed(lean_object* v_ys_2588_, lean_object* v_ys2_2589_, lean_object* v_ys3_2590_, lean_object* v_ys4_2591_, lean_object* v___x_2592_, lean_object* v_useSplitter_2593_, lean_object* v_inst_2594_, lean_object* v_alt_x27_2595_){
_start:
{
uint8_t v___x_15112__boxed_2596_; uint8_t v_useSplitter_boxed_2597_; lean_object* v_res_2598_; 
v___x_15112__boxed_2596_ = lean_unbox(v___x_2592_);
v_useSplitter_boxed_2597_ = lean_unbox(v_useSplitter_2593_);
v_res_2598_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__36(v_ys_2588_, v_ys2_2589_, v_ys3_2590_, v_ys4_2591_, v___x_15112__boxed_2596_, v_useSplitter_boxed_2597_, v_inst_2594_, v_alt_x27_2595_);
lean_dec_ref(v_ys4_2591_);
lean_dec_ref(v_ys3_2590_);
lean_dec_ref(v_ys2_2589_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__37(lean_object* v_args_2599_, lean_object* v_ys_2600_, lean_object* v_ys2_2601_, lean_object* v_ys3_2602_, lean_object* v_ys4_2603_, lean_object* v_onAlt_2604_, lean_object* v_next_2605_, lean_object* v_altType_2606_, lean_object* v_toBind_2607_, lean_object* v___f_2608_, lean_object* v_alt_2609_){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2610_, 0, v_args_2599_);
lean_ctor_set(v___x_2610_, 1, v_ys_2600_);
lean_ctor_set(v___x_2610_, 2, v_ys2_2601_);
lean_ctor_set(v___x_2610_, 3, v_ys3_2602_);
lean_ctor_set(v___x_2610_, 4, v_ys4_2603_);
v___x_2611_ = lean_apply_4(v_onAlt_2604_, v_next_2605_, v_altType_2606_, v___x_2610_, v_alt_2609_);
v___x_2612_ = lean_apply_4(v_toBind_2607_, lean_box(0), lean_box(0), v___x_2611_, v___f_2608_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38(lean_object* v_inst_2613_, lean_object* v_ys_2614_, lean_object* v_ys2_2615_, lean_object* v_ys3_2616_, uint8_t v___x_2617_, uint8_t v_useSplitter_2618_, lean_object* v_inst_2619_, lean_object* v_args_2620_, lean_object* v_onAlt_2621_, lean_object* v_next_2622_, lean_object* v_toBind_2623_, lean_object* v___x_2624_, lean_object* v___f_2625_, lean_object* v_ys4_2626_, lean_object* v_altType_2627_){
_start:
{
lean_object* v_toMonadExceptOf_2628_; lean_object* v_tryCatch_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___f_2632_; lean_object* v___f_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_toMonadExceptOf_2628_ = lean_ctor_get(v_inst_2613_, 0);
lean_inc_ref(v_toMonadExceptOf_2628_);
lean_dec_ref(v_inst_2613_);
v_tryCatch_2629_ = lean_ctor_get(v_toMonadExceptOf_2628_, 1);
lean_inc(v_tryCatch_2629_);
lean_dec_ref(v_toMonadExceptOf_2628_);
v___x_2630_ = lean_box(v___x_2617_);
v___x_2631_ = lean_box(v_useSplitter_2618_);
lean_inc(v_inst_2619_);
lean_inc_ref(v_ys4_2626_);
lean_inc_ref_n(v_ys3_2616_, 2);
lean_inc_ref(v_ys2_2615_);
lean_inc_ref(v_ys_2614_);
v___f_2632_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__36___boxed), 8, 7);
lean_closure_set(v___f_2632_, 0, v_ys_2614_);
lean_closure_set(v___f_2632_, 1, v_ys2_2615_);
lean_closure_set(v___f_2632_, 2, v_ys3_2616_);
lean_closure_set(v___f_2632_, 3, v_ys4_2626_);
lean_closure_set(v___f_2632_, 4, v___x_2630_);
lean_closure_set(v___f_2632_, 5, v___x_2631_);
lean_closure_set(v___f_2632_, 6, v_inst_2619_);
lean_inc(v_toBind_2623_);
lean_inc_ref(v_args_2620_);
v___f_2633_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__37), 11, 10);
lean_closure_set(v___f_2633_, 0, v_args_2620_);
lean_closure_set(v___f_2633_, 1, v_ys_2614_);
lean_closure_set(v___f_2633_, 2, v_ys2_2615_);
lean_closure_set(v___f_2633_, 3, v_ys3_2616_);
lean_closure_set(v___f_2633_, 4, v_ys4_2626_);
lean_closure_set(v___f_2633_, 5, v_onAlt_2621_);
lean_closure_set(v___f_2633_, 6, v_next_2622_);
lean_closure_set(v___f_2633_, 7, v_altType_2627_);
lean_closure_set(v___f_2633_, 8, v_toBind_2623_);
lean_closure_set(v___f_2633_, 9, v___f_2632_);
v___x_2634_ = l_Array_append___redArg(v_args_2620_, v_ys3_2616_);
lean_dec_ref(v_ys3_2616_);
v___x_2635_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateLambda___boxed), 7, 2);
lean_closure_set(v___x_2635_, 0, v___x_2624_);
lean_closure_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_apply_2(v_inst_2619_, lean_box(0), v___x_2635_);
v___x_2637_ = lean_apply_3(v_tryCatch_2629_, lean_box(0), v___x_2636_, v___f_2625_);
v___x_2638_ = lean_apply_4(v_toBind_2623_, lean_box(0), lean_box(0), v___x_2637_, v___f_2633_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed(lean_object* v_inst_2639_, lean_object* v_ys_2640_, lean_object* v_ys2_2641_, lean_object* v_ys3_2642_, lean_object* v___x_2643_, lean_object* v_useSplitter_2644_, lean_object* v_inst_2645_, lean_object* v_args_2646_, lean_object* v_onAlt_2647_, lean_object* v_next_2648_, lean_object* v_toBind_2649_, lean_object* v___x_2650_, lean_object* v___f_2651_, lean_object* v_ys4_2652_, lean_object* v_altType_2653_){
_start:
{
uint8_t v___x_15149__boxed_2654_; uint8_t v_useSplitter_boxed_2655_; lean_object* v_res_2656_; 
v___x_15149__boxed_2654_ = lean_unbox(v___x_2643_);
v_useSplitter_boxed_2655_ = lean_unbox(v_useSplitter_2644_);
v_res_2656_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__38(v_inst_2639_, v_ys_2640_, v_ys2_2641_, v_ys3_2642_, v___x_15149__boxed_2654_, v_useSplitter_boxed_2655_, v_inst_2645_, v_args_2646_, v_onAlt_2647_, v_next_2648_, v_toBind_2649_, v___x_2650_, v___f_2651_, v_ys4_2652_, v_altType_2653_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39(lean_object* v_inst_2657_, lean_object* v_ys_2658_, lean_object* v_ys2_2659_, uint8_t v___x_2660_, uint8_t v_useSplitter_2661_, lean_object* v_inst_2662_, lean_object* v_args_2663_, lean_object* v_onAlt_2664_, lean_object* v_next_2665_, lean_object* v_toBind_2666_, lean_object* v___x_2667_, lean_object* v___f_2668_, lean_object* v_fst_2669_, lean_object* v_inst_2670_, lean_object* v_inst_2671_, lean_object* v_ys3_2672_, lean_object* v_altType_2673_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2674_ = lean_box(v___x_2660_);
v___x_2675_ = lean_box(v_useSplitter_2661_);
v___f_2676_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__38___boxed), 15, 13);
lean_closure_set(v___f_2676_, 0, v_inst_2657_);
lean_closure_set(v___f_2676_, 1, v_ys_2658_);
lean_closure_set(v___f_2676_, 2, v_ys2_2659_);
lean_closure_set(v___f_2676_, 3, v_ys3_2672_);
lean_closure_set(v___f_2676_, 4, v___x_2674_);
lean_closure_set(v___f_2676_, 5, v___x_2675_);
lean_closure_set(v___f_2676_, 6, v_inst_2662_);
lean_closure_set(v___f_2676_, 7, v_args_2663_);
lean_closure_set(v___f_2676_, 8, v_onAlt_2664_);
lean_closure_set(v___f_2676_, 9, v_next_2665_);
lean_closure_set(v___f_2676_, 10, v_toBind_2666_);
lean_closure_set(v___f_2676_, 11, v___x_2667_);
lean_closure_set(v___f_2676_, 12, v___f_2668_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v_fst_2669_);
v___x_2678_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2670_, v_inst_2671_, v_altType_2673_, v___x_2677_, v___f_2676_, v___x_2660_, v___x_2660_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed(lean_object** _args){
lean_object* v_inst_2679_ = _args[0];
lean_object* v_ys_2680_ = _args[1];
lean_object* v_ys2_2681_ = _args[2];
lean_object* v___x_2682_ = _args[3];
lean_object* v_useSplitter_2683_ = _args[4];
lean_object* v_inst_2684_ = _args[5];
lean_object* v_args_2685_ = _args[6];
lean_object* v_onAlt_2686_ = _args[7];
lean_object* v_next_2687_ = _args[8];
lean_object* v_toBind_2688_ = _args[9];
lean_object* v___x_2689_ = _args[10];
lean_object* v___f_2690_ = _args[11];
lean_object* v_fst_2691_ = _args[12];
lean_object* v_inst_2692_ = _args[13];
lean_object* v_inst_2693_ = _args[14];
lean_object* v_ys3_2694_ = _args[15];
lean_object* v_altType_2695_ = _args[16];
_start:
{
uint8_t v___x_15182__boxed_2696_; uint8_t v_useSplitter_boxed_2697_; lean_object* v_res_2698_; 
v___x_15182__boxed_2696_ = lean_unbox(v___x_2682_);
v_useSplitter_boxed_2697_ = lean_unbox(v_useSplitter_2683_);
v_res_2698_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__39(v_inst_2679_, v_ys_2680_, v_ys2_2681_, v___x_15182__boxed_2696_, v_useSplitter_boxed_2697_, v_inst_2684_, v_args_2685_, v_onAlt_2686_, v_next_2687_, v_toBind_2688_, v___x_2689_, v___f_2690_, v_fst_2691_, v_inst_2692_, v_inst_2693_, v_ys3_2694_, v_altType_2695_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40(lean_object* v_inst_2699_, lean_object* v_ys_2700_, uint8_t v___x_2701_, uint8_t v_useSplitter_2702_, lean_object* v_inst_2703_, lean_object* v_args_2704_, lean_object* v_onAlt_2705_, lean_object* v_next_2706_, lean_object* v_toBind_2707_, lean_object* v___x_2708_, lean_object* v___f_2709_, lean_object* v_fst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_numDiscrEqs_2713_, lean_object* v_ys2_2714_, lean_object* v_altType_2715_){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2716_ = lean_box(v___x_2701_);
v___x_2717_ = lean_box(v_useSplitter_2702_);
lean_inc_ref(v_inst_2712_);
lean_inc_ref(v_inst_2711_);
v___f_2718_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__39___boxed), 17, 15);
lean_closure_set(v___f_2718_, 0, v_inst_2699_);
lean_closure_set(v___f_2718_, 1, v_ys_2700_);
lean_closure_set(v___f_2718_, 2, v_ys2_2714_);
lean_closure_set(v___f_2718_, 3, v___x_2716_);
lean_closure_set(v___f_2718_, 4, v___x_2717_);
lean_closure_set(v___f_2718_, 5, v_inst_2703_);
lean_closure_set(v___f_2718_, 6, v_args_2704_);
lean_closure_set(v___f_2718_, 7, v_onAlt_2705_);
lean_closure_set(v___f_2718_, 8, v_next_2706_);
lean_closure_set(v___f_2718_, 9, v_toBind_2707_);
lean_closure_set(v___f_2718_, 10, v___x_2708_);
lean_closure_set(v___f_2718_, 11, v___f_2709_);
lean_closure_set(v___f_2718_, 12, v_fst_2710_);
lean_closure_set(v___f_2718_, 13, v_inst_2711_);
lean_closure_set(v___f_2718_, 14, v_inst_2712_);
v___x_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2719_, 0, v_numDiscrEqs_2713_);
v___x_2720_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2711_, v_inst_2712_, v_altType_2715_, v___x_2719_, v___f_2718_, v___x_2701_, v___x_2701_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed(lean_object** _args){
lean_object* v_inst_2721_ = _args[0];
lean_object* v_ys_2722_ = _args[1];
lean_object* v___x_2723_ = _args[2];
lean_object* v_useSplitter_2724_ = _args[3];
lean_object* v_inst_2725_ = _args[4];
lean_object* v_args_2726_ = _args[5];
lean_object* v_onAlt_2727_ = _args[6];
lean_object* v_next_2728_ = _args[7];
lean_object* v_toBind_2729_ = _args[8];
lean_object* v___x_2730_ = _args[9];
lean_object* v___f_2731_ = _args[10];
lean_object* v_fst_2732_ = _args[11];
lean_object* v_inst_2733_ = _args[12];
lean_object* v_inst_2734_ = _args[13];
lean_object* v_numDiscrEqs_2735_ = _args[14];
lean_object* v_ys2_2736_ = _args[15];
lean_object* v_altType_2737_ = _args[16];
_start:
{
uint8_t v___x_15213__boxed_2738_; uint8_t v_useSplitter_boxed_2739_; lean_object* v_res_2740_; 
v___x_15213__boxed_2738_ = lean_unbox(v___x_2723_);
v_useSplitter_boxed_2739_ = lean_unbox(v_useSplitter_2724_);
v_res_2740_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__40(v_inst_2721_, v_ys_2722_, v___x_15213__boxed_2738_, v_useSplitter_boxed_2739_, v_inst_2725_, v_args_2726_, v_onAlt_2727_, v_next_2728_, v_toBind_2729_, v___x_2730_, v___f_2731_, v_fst_2732_, v_inst_2733_, v_inst_2734_, v_numDiscrEqs_2735_, v_ys2_2736_, v_altType_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41(lean_object* v___x_2741_, lean_object* v_inst_2742_, lean_object* v_inst_2743_, lean_object* v___f_2744_, uint8_t v___x_2745_, lean_object* v_toBind_2746_, lean_object* v___f_2747_, lean_object* v_altType_2748_){
_start:
{
lean_object* v_numOverlaps_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
v_numOverlaps_2749_ = lean_ctor_get(v___x_2741_, 1);
lean_inc(v_numOverlaps_2749_);
v___x_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_numOverlaps_2749_);
v___x_2751_ = l_Lean_Meta_forallBoundedTelescope___redArg(v_inst_2742_, v_inst_2743_, v_altType_2748_, v___x_2750_, v___f_2744_, v___x_2745_, v___x_2745_);
v___x_2752_ = lean_apply_4(v_toBind_2746_, lean_box(0), lean_box(0), v___x_2751_, v___f_2747_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed(lean_object* v___x_2753_, lean_object* v_inst_2754_, lean_object* v_inst_2755_, lean_object* v___f_2756_, lean_object* v___x_2757_, lean_object* v_toBind_2758_, lean_object* v___f_2759_, lean_object* v_altType_2760_){
_start:
{
uint8_t v___x_15247__boxed_2761_; lean_object* v_res_2762_; 
v___x_15247__boxed_2761_ = lean_unbox(v___x_2757_);
v_res_2762_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__41(v___x_2753_, v_inst_2754_, v_inst_2755_, v___f_2756_, v___x_15247__boxed_2761_, v_toBind_2758_, v___f_2759_, v_altType_2760_);
lean_dec_ref(v___x_2753_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__42(lean_object* v___f_2763_, lean_object* v_altType_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = lean_apply_1(v___f_2763_, v_altType_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2770_ = lean_box(0);
v___x_2771_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__1));
v___x_2772_ = l_Lean_mkConst(v___x_2771_, v___x_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44(uint8_t v_hasUnitThunk_2773_, lean_object* v_toPure_2774_, lean_object* v_toBind_2775_, lean_object* v___f_2776_, lean_object* v___x_2777_, lean_object* v_inst_2778_, lean_object* v___f_2779_, lean_object* v_altType_2780_){
_start:
{
if (v_hasUnitThunk_2773_ == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
lean_dec(v___f_2779_);
lean_dec(v_inst_2778_);
v___x_2781_ = lean_apply_2(v_toPure_2774_, lean_box(0), v_altType_2780_);
v___x_2782_ = lean_apply_4(v_toBind_2775_, lean_box(0), lean_box(0), v___x_2781_, v___f_2776_);
return v___x_2782_;
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
lean_dec(v___f_2776_);
lean_dec(v_toPure_2774_);
v___x_2783_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_2784_ = lean_mk_empty_array_with_capacity(v___x_2777_);
v___x_2785_ = lean_array_push(v___x_2784_, v___x_2783_);
v___x_2786_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2786_, 0, v_altType_2780_);
lean_closure_set(v___x_2786_, 1, v___x_2785_);
v___x_2787_ = lean_apply_2(v_inst_2778_, lean_box(0), v___x_2786_);
v___x_2788_ = lean_apply_4(v_toBind_2775_, lean_box(0), lean_box(0), v___x_2787_, v___f_2779_);
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed(lean_object* v_hasUnitThunk_2789_, lean_object* v_toPure_2790_, lean_object* v_toBind_2791_, lean_object* v___f_2792_, lean_object* v___x_2793_, lean_object* v_inst_2794_, lean_object* v___f_2795_, lean_object* v_altType_2796_){
_start:
{
uint8_t v_hasUnitThunk_boxed_2797_; lean_object* v_res_2798_; 
v_hasUnitThunk_boxed_2797_ = lean_unbox(v_hasUnitThunk_2789_);
v_res_2798_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__44(v_hasUnitThunk_boxed_2797_, v_toPure_2790_, v_toBind_2791_, v___f_2792_, v___x_2793_, v_inst_2794_, v___f_2795_, v_altType_2796_);
lean_dec(v___x_2793_);
return v_res_2798_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3(void){
_start:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2802_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__2));
v___x_2803_ = lean_unsigned_to_nat(8u);
v___x_2804_ = lean_unsigned_to_nat(360u);
v___x_2805_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2806_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2807_ = l_mkPanicMessageWithDecl(v___x_2806_, v___x_2805_, v___x_2804_, v___x_2803_, v___x_2802_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43(lean_object* v___x_2808_, lean_object* v_inst_2809_, lean_object* v_inst_2810_, uint8_t v___x_2811_, uint8_t v_useSplitter_2812_, lean_object* v_inst_2813_, lean_object* v_onAlt_2814_, lean_object* v_next_2815_, lean_object* v_toBind_2816_, lean_object* v___x_2817_, lean_object* v___f_2818_, lean_object* v_fst_2819_, lean_object* v_inst_2820_, lean_object* v_numDiscrEqs_2821_, lean_object* v___f_2822_, uint8_t v_hasUnitThunk_2823_, lean_object* v_toPure_2824_, lean_object* v___x_2825_, lean_object* v___x_2826_, lean_object* v_ys_2827_, lean_object* v_args_2828_){
_start:
{
lean_object* v_numFields_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v_numFields_2829_ = lean_ctor_get(v___x_2808_, 0);
v___x_2830_ = lean_array_get_size(v_ys_2827_);
v___x_2831_ = lean_nat_dec_eq(v___x_2830_, v_numFields_2829_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec_ref(v_args_2828_);
lean_dec_ref(v_ys_2827_);
lean_dec_ref(v___x_2826_);
lean_dec(v___x_2825_);
lean_dec(v_toPure_2824_);
lean_dec(v___f_2822_);
lean_dec(v_numDiscrEqs_2821_);
lean_dec_ref(v_inst_2820_);
lean_dec(v_fst_2819_);
lean_dec(v___f_2818_);
lean_dec_ref(v___x_2817_);
lean_dec(v_toBind_2816_);
lean_dec(v_next_2815_);
lean_dec(v_onAlt_2814_);
lean_dec(v_inst_2813_);
lean_dec_ref(v_inst_2810_);
lean_dec_ref(v___x_2808_);
v___x_2832_ = l_Lean_instInhabitedExpr;
v___x_2833_ = l_instInhabitedOfMonad___redArg(v_inst_2809_, v___x_2832_);
v___x_2834_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_2835_ = l_panic___redArg(v___x_2833_, v___x_2834_);
lean_dec(v___x_2833_);
return v___x_2835_;
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___f_2838_; lean_object* v___x_2839_; lean_object* v___f_2840_; lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___f_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2836_ = lean_box(v___x_2811_);
v___x_2837_ = lean_box(v_useSplitter_2812_);
lean_inc_ref(v_inst_2809_);
lean_inc_ref(v_inst_2820_);
lean_inc_n(v_toBind_2816_, 3);
lean_inc_n(v_inst_2813_, 2);
lean_inc_ref(v_ys_2827_);
v___f_2838_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__40___boxed), 17, 15);
lean_closure_set(v___f_2838_, 0, v_inst_2810_);
lean_closure_set(v___f_2838_, 1, v_ys_2827_);
lean_closure_set(v___f_2838_, 2, v___x_2836_);
lean_closure_set(v___f_2838_, 3, v___x_2837_);
lean_closure_set(v___f_2838_, 4, v_inst_2813_);
lean_closure_set(v___f_2838_, 5, v_args_2828_);
lean_closure_set(v___f_2838_, 6, v_onAlt_2814_);
lean_closure_set(v___f_2838_, 7, v_next_2815_);
lean_closure_set(v___f_2838_, 8, v_toBind_2816_);
lean_closure_set(v___f_2838_, 9, v___x_2817_);
lean_closure_set(v___f_2838_, 10, v___f_2818_);
lean_closure_set(v___f_2838_, 11, v_fst_2819_);
lean_closure_set(v___f_2838_, 12, v_inst_2820_);
lean_closure_set(v___f_2838_, 13, v_inst_2809_);
lean_closure_set(v___f_2838_, 14, v_numDiscrEqs_2821_);
v___x_2839_ = lean_box(v___x_2811_);
v___f_2840_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__41___boxed), 8, 7);
lean_closure_set(v___f_2840_, 0, v___x_2808_);
lean_closure_set(v___f_2840_, 1, v_inst_2820_);
lean_closure_set(v___f_2840_, 2, v_inst_2809_);
lean_closure_set(v___f_2840_, 3, v___f_2838_);
lean_closure_set(v___f_2840_, 4, v___x_2839_);
lean_closure_set(v___f_2840_, 5, v_toBind_2816_);
lean_closure_set(v___f_2840_, 6, v___f_2822_);
v___f_2841_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__42), 2, 1);
lean_closure_set(v___f_2841_, 0, v___f_2840_);
v___x_2842_ = lean_box(v_hasUnitThunk_2823_);
lean_inc_ref(v___f_2841_);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__44___boxed), 8, 7);
lean_closure_set(v___f_2843_, 0, v___x_2842_);
lean_closure_set(v___f_2843_, 1, v_toPure_2824_);
lean_closure_set(v___f_2843_, 2, v_toBind_2816_);
lean_closure_set(v___f_2843_, 3, v___f_2841_);
lean_closure_set(v___f_2843_, 4, v___x_2825_);
lean_closure_set(v___f_2843_, 5, v_inst_2813_);
lean_closure_set(v___f_2843_, 6, v___f_2841_);
v___x_2844_ = lean_alloc_closure((void*)(l_Lean_Meta_instantiateForall___boxed), 7, 2);
lean_closure_set(v___x_2844_, 0, v___x_2826_);
lean_closure_set(v___x_2844_, 1, v_ys_2827_);
v___x_2845_ = lean_apply_2(v_inst_2813_, lean_box(0), v___x_2844_);
v___x_2846_ = lean_apply_4(v_toBind_2816_, lean_box(0), lean_box(0), v___x_2845_, v___f_2843_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed(lean_object** _args){
lean_object* v___x_2847_ = _args[0];
lean_object* v_inst_2848_ = _args[1];
lean_object* v_inst_2849_ = _args[2];
lean_object* v___x_2850_ = _args[3];
lean_object* v_useSplitter_2851_ = _args[4];
lean_object* v_inst_2852_ = _args[5];
lean_object* v_onAlt_2853_ = _args[6];
lean_object* v_next_2854_ = _args[7];
lean_object* v_toBind_2855_ = _args[8];
lean_object* v___x_2856_ = _args[9];
lean_object* v___f_2857_ = _args[10];
lean_object* v_fst_2858_ = _args[11];
lean_object* v_inst_2859_ = _args[12];
lean_object* v_numDiscrEqs_2860_ = _args[13];
lean_object* v___f_2861_ = _args[14];
lean_object* v_hasUnitThunk_2862_ = _args[15];
lean_object* v_toPure_2863_ = _args[16];
lean_object* v___x_2864_ = _args[17];
lean_object* v___x_2865_ = _args[18];
lean_object* v_ys_2866_ = _args[19];
lean_object* v_args_2867_ = _args[20];
_start:
{
uint8_t v___x_15342__boxed_2868_; uint8_t v_useSplitter_boxed_2869_; uint8_t v_hasUnitThunk_boxed_2870_; lean_object* v_res_2871_; 
v___x_15342__boxed_2868_ = lean_unbox(v___x_2850_);
v_useSplitter_boxed_2869_ = lean_unbox(v_useSplitter_2851_);
v_hasUnitThunk_boxed_2870_ = lean_unbox(v_hasUnitThunk_2862_);
v_res_2871_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__43(v___x_2847_, v_inst_2848_, v_inst_2849_, v___x_15342__boxed_2868_, v_useSplitter_boxed_2869_, v_inst_2852_, v_onAlt_2853_, v_next_2854_, v_toBind_2855_, v___x_2856_, v___f_2857_, v_fst_2858_, v_inst_2859_, v_numDiscrEqs_2860_, v___f_2861_, v_hasUnitThunk_boxed_2870_, v_toPure_2863_, v___x_2864_, v___x_2865_, v_ys_2866_, v_args_2867_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__45(lean_object* v_fst_2872_, lean_object* v___x_2873_, lean_object* v___x_2874_, lean_object* v___x_2875_, lean_object* v___x_2876_, lean_object* v___x_2877_, lean_object* v_toPure_2878_, lean_object* v_alt_x27_2879_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2880_ = lean_array_push(v_fst_2872_, v_alt_x27_2879_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2873_);
lean_ctor_set(v___x_2881_, 1, v___x_2874_);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2875_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2876_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2877_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2880_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
v___x_2887_ = lean_apply_2(v_toPure_2878_, lean_box(0), v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0(void){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Array_instInhabited(lean_box(0));
return v___x_2888_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1(void){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Subarray_empty(lean_box(0));
return v___x_2889_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2(void){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2890_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
return v___x_2891_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3(void){
_start:
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2892_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__2);
v___x_2893_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v___x_2893_);
lean_ctor_set(v___x_2894_, 1, v___x_2892_);
return v___x_2894_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2895_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__3);
v___x_2896_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___x_2895_);
return v___x_2897_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5(void){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__4);
v___x_2899_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__1);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2899_);
lean_ctor_set(v___x_2900_, 1, v___x_2898_);
return v___x_2900_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6(void){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__5);
v___x_2902_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__0);
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2902_);
lean_ctor_set(v___x_2903_, 1, v___x_2901_);
return v___x_2903_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7(void){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__6);
v___x_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2904_);
return v___x_2905_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9(void){
_start:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2907_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__8));
v___x_2908_ = lean_unsigned_to_nat(6u);
v___x_2909_ = lean_unsigned_to_nat(358u);
v___x_2910_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__1));
v___x_2911_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__0));
v___x_2912_ = l_mkPanicMessageWithDecl(v___x_2911_, v___x_2910_, v___x_2909_, v___x_2908_, v___x_2907_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__46(lean_object* v___x_2913_, lean_object* v_toPure_2914_, lean_object* v_toBind_2915_, lean_object* v___f_2916_, lean_object* v___x_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, uint8_t v___x_2921_, uint8_t v_useSplitter_2922_, lean_object* v_onAlt_2923_, lean_object* v___f_2924_, lean_object* v_fst_2925_, lean_object* v_inst_2926_, lean_object* v_numDiscrEqs_2927_, lean_object* v_next_2928_, lean_object* v_acc_2929_, lean_object* v_h_2930_, lean_object* v_G_2931_){
_start:
{
uint8_t v___x_2932_; 
v___x_2932_ = lean_nat_dec_lt(v_next_2928_, v___x_2913_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2933_; 
lean_dec(v_G_2931_);
lean_dec(v_next_2928_);
lean_dec(v_numDiscrEqs_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_fst_2925_);
lean_dec(v___f_2924_);
lean_dec(v_onAlt_2923_);
lean_dec_ref(v_inst_2920_);
lean_dec(v_inst_2919_);
lean_dec_ref(v_inst_2918_);
lean_dec(v___f_2916_);
lean_dec(v_toBind_2915_);
v___x_2933_ = lean_apply_2(v_toPure_2914_, lean_box(0), v_acc_2929_);
return v___x_2933_;
}
else
{
lean_object* v_snd_2934_; lean_object* v_snd_2935_; lean_object* v_snd_2936_; lean_object* v_snd_2937_; lean_object* v_snd_2938_; lean_object* v_fst_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_3153_; 
v_snd_2934_ = lean_ctor_get(v_acc_2929_, 1);
lean_inc(v_snd_2934_);
v_snd_2935_ = lean_ctor_get(v_snd_2934_, 1);
lean_inc(v_snd_2935_);
v_snd_2936_ = lean_ctor_get(v_snd_2935_, 1);
lean_inc(v_snd_2936_);
v_snd_2937_ = lean_ctor_get(v_snd_2936_, 1);
lean_inc(v_snd_2937_);
v_snd_2938_ = lean_ctor_get(v_snd_2937_, 1);
lean_inc(v_snd_2938_);
v_fst_2939_ = lean_ctor_get(v_acc_2929_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_acc_2929_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v_acc_2929_, 1);
lean_dec(v_unused_3154_);
v___x_2941_ = v_acc_2929_;
v_isShared_2942_ = v_isSharedCheck_3153_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_fst_2939_);
lean_dec(v_acc_2929_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_3153_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v_fst_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_3151_; 
v_fst_2943_ = lean_ctor_get(v_snd_2934_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v_snd_2934_);
if (v_isSharedCheck_3151_ == 0)
{
lean_object* v_unused_3152_; 
v_unused_3152_ = lean_ctor_get(v_snd_2934_, 1);
lean_dec(v_unused_3152_);
v___x_2945_ = v_snd_2934_;
v_isShared_2946_ = v_isSharedCheck_3151_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_fst_2943_);
lean_dec(v_snd_2934_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_3151_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v_fst_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_3149_; 
v_fst_2947_ = lean_ctor_get(v_snd_2935_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_snd_2935_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v_snd_2935_, 1);
lean_dec(v_unused_3150_);
v___x_2949_ = v_snd_2935_;
v_isShared_2950_ = v_isSharedCheck_3149_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_fst_2947_);
lean_dec(v_snd_2935_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_3149_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v_fst_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_3147_; 
v_fst_2951_ = lean_ctor_get(v_snd_2936_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_snd_2936_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v_snd_2936_, 1);
lean_dec(v_unused_3148_);
v___x_2953_ = v_snd_2936_;
v_isShared_2954_ = v_isSharedCheck_3147_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_fst_2951_);
lean_dec(v_snd_2936_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_3147_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v_fst_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_3145_; 
v_fst_2955_ = lean_ctor_get(v_snd_2937_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_snd_2937_);
if (v_isSharedCheck_3145_ == 0)
{
lean_object* v_unused_3146_; 
v_unused_3146_ = lean_ctor_get(v_snd_2937_, 1);
lean_dec(v_unused_3146_);
v___x_2957_ = v_snd_2937_;
v_isShared_2958_ = v_isSharedCheck_3145_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_fst_2955_);
lean_dec(v_snd_2937_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_3145_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v_array_2959_; lean_object* v_start_2960_; lean_object* v_stop_2961_; lean_object* v___f_2962_; lean_object* v___y_2964_; uint8_t v___x_2967_; 
v_array_2959_ = lean_ctor_get(v_snd_2938_, 0);
v_start_2960_ = lean_ctor_get(v_snd_2938_, 1);
v_stop_2961_ = lean_ctor_get(v_snd_2938_, 2);
lean_inc(v_next_2928_);
lean_inc(v_toPure_2914_);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__35___boxed), 4, 3);
lean_closure_set(v___f_2962_, 0, v_toPure_2914_);
lean_closure_set(v___f_2962_, 1, v_next_2928_);
lean_closure_set(v___f_2962_, 2, v_G_2931_);
v___x_2967_ = lean_nat_dec_lt(v_start_2960_, v_stop_2961_);
if (v___x_2967_ == 0)
{
lean_object* v___x_2969_; 
lean_dec(v_next_2928_);
lean_dec(v_numDiscrEqs_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_fst_2925_);
lean_dec(v___f_2924_);
lean_dec(v_onAlt_2923_);
lean_dec_ref(v_inst_2920_);
lean_dec(v_inst_2919_);
lean_dec_ref(v_inst_2918_);
if (v_isShared_2958_ == 0)
{
v___x_2969_ = v___x_2957_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_fst_2955_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v_snd_2938_);
v___x_2969_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
lean_object* v___x_2971_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2969_);
v___x_2971_ = v___x_2953_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_fst_2951_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v___x_2969_);
v___x_2971_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2973_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_2971_);
v___x_2973_ = v___x_2949_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_fst_2947_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2975_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_2973_);
v___x_2975_ = v___x_2945_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_fst_2943_);
lean_ctor_set(v_reuseFailAlloc_2981_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_2975_);
v___x_2977_ = v___x_2941_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_2980_, 1, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
v___x_2979_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_2978_);
v___y_2964_ = v___x_2979_;
goto v___jp_2963_;
}
}
}
}
}
}
else
{
lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_3141_; 
lean_inc(v_stop_2961_);
lean_inc(v_start_2960_);
lean_inc_ref(v_array_2959_);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_snd_2938_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; lean_object* v_unused_3143_; lean_object* v_unused_3144_; 
v_unused_3142_ = lean_ctor_get(v_snd_2938_, 2);
lean_dec(v_unused_3142_);
v_unused_3143_ = lean_ctor_get(v_snd_2938_, 1);
lean_dec(v_unused_3143_);
v_unused_3144_ = lean_ctor_get(v_snd_2938_, 0);
lean_dec(v_unused_3144_);
v___x_2986_ = v_snd_2938_;
v_isShared_2987_ = v_isSharedCheck_3141_;
goto v_resetjp_2985_;
}
else
{
lean_dec(v_snd_2938_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_3141_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v_array_2988_; lean_object* v_start_2989_; lean_object* v_stop_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2995_; 
v_array_2988_ = lean_ctor_get(v_fst_2955_, 0);
v_start_2989_ = lean_ctor_get(v_fst_2955_, 1);
v_stop_2990_ = lean_ctor_get(v_fst_2955_, 2);
v___x_2991_ = lean_array_fget(v_array_2959_, v_start_2960_);
v___x_2992_ = lean_unsigned_to_nat(1u);
v___x_2993_ = lean_nat_add(v_start_2960_, v___x_2992_);
lean_dec(v_start_2960_);
if (v_isShared_2987_ == 0)
{
lean_ctor_set(v___x_2986_, 1, v___x_2993_);
v___x_2995_ = v___x_2986_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_array_2959_);
lean_ctor_set(v_reuseFailAlloc_3140_, 1, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_3140_, 2, v_stop_2961_);
v___x_2995_ = v_reuseFailAlloc_3140_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_nat_dec_lt(v_start_2989_, v_stop_2990_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2998_; 
lean_dec(v___x_2991_);
lean_dec(v_next_2928_);
lean_dec(v_numDiscrEqs_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_fst_2925_);
lean_dec(v___f_2924_);
lean_dec(v_onAlt_2923_);
lean_dec_ref(v_inst_2920_);
lean_dec(v_inst_2919_);
lean_dec_ref(v_inst_2918_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2995_);
v___x_2998_ = v___x_2957_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_fst_2955_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v___x_2995_);
v___x_2998_ = v_reuseFailAlloc_3013_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_3000_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_2998_);
v___x_3000_ = v___x_2953_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_fst_2951_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3002_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_3000_);
v___x_3002_ = v___x_2949_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_fst_2947_);
lean_ctor_set(v_reuseFailAlloc_3011_, 1, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
lean_object* v___x_3004_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_3002_);
v___x_3004_ = v___x_2945_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_fst_2943_);
lean_ctor_set(v_reuseFailAlloc_3010_, 1, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
lean_object* v___x_3006_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_3004_);
v___x_3006_ = v___x_2941_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3006_);
v___x_3008_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_3007_);
v___y_2964_ = v___x_3008_;
goto v___jp_2963_;
}
}
}
}
}
}
else
{
lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3136_; 
lean_inc(v_stop_2990_);
lean_inc(v_start_2989_);
lean_inc_ref(v_array_2988_);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_fst_2955_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; lean_object* v_unused_3138_; lean_object* v_unused_3139_; 
v_unused_3137_ = lean_ctor_get(v_fst_2955_, 2);
lean_dec(v_unused_3137_);
v_unused_3138_ = lean_ctor_get(v_fst_2955_, 1);
lean_dec(v_unused_3138_);
v_unused_3139_ = lean_ctor_get(v_fst_2955_, 0);
lean_dec(v_unused_3139_);
v___x_3015_ = v_fst_2955_;
v_isShared_3016_ = v_isSharedCheck_3136_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v_fst_2955_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3136_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v_array_3017_; lean_object* v_start_3018_; lean_object* v_stop_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3023_; 
v_array_3017_ = lean_ctor_get(v_fst_2951_, 0);
v_start_3018_ = lean_ctor_get(v_fst_2951_, 1);
v_stop_3019_ = lean_ctor_get(v_fst_2951_, 2);
v___x_3020_ = lean_array_fget(v_array_2988_, v_start_2989_);
v___x_3021_ = lean_nat_add(v_start_2989_, v___x_2992_);
lean_dec(v_start_2989_);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 1, v___x_3021_);
v___x_3023_ = v___x_3015_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_array_2988_);
lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3135_, 2, v_stop_2990_);
v___x_3023_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_nat_dec_lt(v_start_3018_, v_stop_3019_);
if (v___x_3024_ == 0)
{
lean_object* v___x_3026_; 
lean_dec(v___x_3020_);
lean_dec(v___x_2991_);
lean_dec(v_next_2928_);
lean_dec(v_numDiscrEqs_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_fst_2925_);
lean_dec(v___f_2924_);
lean_dec(v_onAlt_2923_);
lean_dec_ref(v_inst_2920_);
lean_dec(v_inst_2919_);
lean_dec_ref(v_inst_2918_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2995_);
lean_ctor_set(v___x_2957_, 0, v___x_3023_);
v___x_3026_ = v___x_2957_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_2995_);
v___x_3026_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_3026_);
v___x_3028_ = v___x_2953_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_fst_2951_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_3026_);
v___x_3028_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3030_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_3028_);
v___x_3030_ = v___x_2949_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_fst_2947_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3032_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_3030_);
v___x_3032_ = v___x_2945_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_fst_2943_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
lean_object* v___x_3034_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_3032_);
v___x_3034_ = v___x_2941_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_3037_, 1, v___x_3032_);
v___x_3034_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
v___x_3036_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_3035_);
v___y_2964_ = v___x_3036_;
goto v___jp_2963_;
}
}
}
}
}
}
else
{
lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3131_; 
lean_inc(v_stop_3019_);
lean_inc(v_start_3018_);
lean_inc_ref(v_array_3017_);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_fst_2951_);
if (v_isSharedCheck_3131_ == 0)
{
lean_object* v_unused_3132_; lean_object* v_unused_3133_; lean_object* v_unused_3134_; 
v_unused_3132_ = lean_ctor_get(v_fst_2951_, 2);
lean_dec(v_unused_3132_);
v_unused_3133_ = lean_ctor_get(v_fst_2951_, 1);
lean_dec(v_unused_3133_);
v_unused_3134_ = lean_ctor_get(v_fst_2951_, 0);
lean_dec(v_unused_3134_);
v___x_3043_ = v_fst_2951_;
v_isShared_3044_ = v_isSharedCheck_3131_;
goto v_resetjp_3042_;
}
else
{
lean_dec(v_fst_2951_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3131_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_array_3045_; lean_object* v_start_3046_; lean_object* v_stop_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v_array_3045_ = lean_ctor_get(v_fst_2947_, 0);
v_start_3046_ = lean_ctor_get(v_fst_2947_, 1);
v_stop_3047_ = lean_ctor_get(v_fst_2947_, 2);
v___x_3048_ = lean_array_fget(v_array_3017_, v_start_3018_);
v___x_3049_ = lean_nat_add(v_start_3018_, v___x_2992_);
lean_dec(v_start_3018_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 1, v___x_3049_);
v___x_3051_ = v___x_3043_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_array_3017_);
lean_ctor_set(v_reuseFailAlloc_3130_, 1, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3130_, 2, v_stop_3019_);
v___x_3051_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
uint8_t v___x_3052_; 
v___x_3052_ = lean_nat_dec_lt(v_start_3046_, v_stop_3047_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3054_; 
lean_dec(v___x_3048_);
lean_dec(v___x_3020_);
lean_dec(v___x_2991_);
lean_dec(v_next_2928_);
lean_dec(v_numDiscrEqs_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_fst_2925_);
lean_dec(v___f_2924_);
lean_dec(v_onAlt_2923_);
lean_dec_ref(v_inst_2920_);
lean_dec(v_inst_2919_);
lean_dec_ref(v_inst_2918_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2995_);
lean_ctor_set(v___x_2957_, 0, v___x_3023_);
v___x_3054_ = v___x_2957_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3069_, 1, v___x_2995_);
v___x_3054_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
lean_object* v___x_3056_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_3054_);
lean_ctor_set(v___x_2953_, 0, v___x_3051_);
v___x_3056_ = v___x_2953_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
lean_object* v___x_3058_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_3056_);
v___x_3058_ = v___x_2949_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_fst_2947_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3060_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_3058_);
v___x_3060_ = v___x_2945_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_fst_2943_);
lean_ctor_set(v_reuseFailAlloc_3066_, 1, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3062_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_3060_);
v___x_3062_ = v___x_2941_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
v___x_3064_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_3063_);
v___y_2964_ = v___x_3064_;
goto v___jp_2963_;
}
}
}
}
}
}
else
{
lean_object* v___x_3071_; uint8_t v_isShared_3072_; uint8_t v_isSharedCheck_3126_; 
lean_inc(v_stop_3047_);
lean_inc(v_start_3046_);
lean_inc_ref(v_array_3045_);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_fst_2947_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; lean_object* v_unused_3128_; lean_object* v_unused_3129_; 
v_unused_3127_ = lean_ctor_get(v_fst_2947_, 2);
lean_dec(v_unused_3127_);
v_unused_3128_ = lean_ctor_get(v_fst_2947_, 1);
lean_dec(v_unused_3128_);
v_unused_3129_ = lean_ctor_get(v_fst_2947_, 0);
lean_dec(v_unused_3129_);
v___x_3071_ = v_fst_2947_;
v_isShared_3072_ = v_isSharedCheck_3126_;
goto v_resetjp_3070_;
}
else
{
lean_dec(v_fst_2947_);
v___x_3071_ = lean_box(0);
v_isShared_3072_ = v_isSharedCheck_3126_;
goto v_resetjp_3070_;
}
v_resetjp_3070_:
{
lean_object* v_array_3073_; lean_object* v_start_3074_; lean_object* v_stop_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v_array_3073_ = lean_ctor_get(v_fst_2943_, 0);
v_start_3074_ = lean_ctor_get(v_fst_2943_, 1);
v_stop_3075_ = lean_ctor_get(v_fst_2943_, 2);
v___x_3076_ = lean_array_fget(v_array_3045_, v_start_3046_);
v___x_3077_ = lean_nat_add(v_start_3046_, v___x_2992_);
lean_dec(v_start_3046_);
if (v_isShared_3072_ == 0)
{
lean_ctor_set(v___x_3071_, 1, v___x_3077_);
v___x_3079_ = v___x_3071_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_array_3045_);
lean_ctor_set(v_reuseFailAlloc_3125_, 1, v___x_3077_);
lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_stop_3047_);
v___x_3079_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
uint8_t v___x_3080_; 
v___x_3080_ = lean_nat_dec_lt(v_start_3074_, v_stop_3075_);
if (v___x_3080_ == 0)
{
lean_object* v___x_3082_; 
lean_dec(v___x_3076_);
lean_dec(v___x_3048_);
lean_dec(v___x_3020_);
lean_dec(v___x_2991_);
lean_dec(v_next_2928_);
lean_dec(v_numDiscrEqs_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_fst_2925_);
lean_dec(v___f_2924_);
lean_dec(v_onAlt_2923_);
lean_dec_ref(v_inst_2920_);
lean_dec(v_inst_2919_);
lean_dec_ref(v_inst_2918_);
if (v_isShared_2958_ == 0)
{
lean_ctor_set(v___x_2957_, 1, v___x_2995_);
lean_ctor_set(v___x_2957_, 0, v___x_3023_);
v___x_3082_ = v___x_2957_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3097_, 1, v___x_2995_);
v___x_3082_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3084_; 
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 1, v___x_3082_);
lean_ctor_set(v___x_2953_, 0, v___x_3051_);
v___x_3084_ = v___x_2953_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3051_);
lean_ctor_set(v_reuseFailAlloc_3096_, 1, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3086_; 
if (v_isShared_2950_ == 0)
{
lean_ctor_set(v___x_2949_, 1, v___x_3084_);
lean_ctor_set(v___x_2949_, 0, v___x_3079_);
v___x_3086_ = v___x_2949_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3079_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3084_);
v___x_3086_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3088_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v___x_3086_);
v___x_3088_ = v___x_2945_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_fst_2943_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3086_);
v___x_3088_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3090_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 1, v___x_3088_);
v___x_3090_ = v___x_2941_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_fst_2939_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3088_);
v___x_3090_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
v___x_3092_ = lean_apply_2(v_toPure_2914_, lean_box(0), v___x_3091_);
v___y_2964_ = v___x_3092_;
goto v___jp_2963_;
}
}
}
}
}
}
else
{
lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3121_; 
lean_inc(v_stop_3075_);
lean_inc(v_start_3074_);
lean_inc_ref(v_array_3073_);
lean_del_object(v___x_2957_);
lean_del_object(v___x_2953_);
lean_del_object(v___x_2949_);
lean_del_object(v___x_2945_);
lean_del_object(v___x_2941_);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_fst_2943_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; lean_object* v_unused_3123_; lean_object* v_unused_3124_; 
v_unused_3122_ = lean_ctor_get(v_fst_2943_, 2);
lean_dec(v_unused_3122_);
v_unused_3123_ = lean_ctor_get(v_fst_2943_, 1);
lean_dec(v_unused_3123_);
v_unused_3124_ = lean_ctor_get(v_fst_2943_, 0);
lean_dec(v_unused_3124_);
v___x_3099_ = v_fst_2943_;
v_isShared_3100_ = v_isSharedCheck_3121_;
goto v_resetjp_3098_;
}
else
{
lean_dec(v_fst_2943_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3121_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v_numOverlaps_3101_; uint8_t v_hasUnitThunk_3102_; uint8_t v___x_3103_; 
v_numOverlaps_3101_ = lean_ctor_get(v___x_3076_, 1);
v_hasUnitThunk_3102_ = lean_ctor_get_uint8(v___x_3076_, sizeof(void*)*2);
v___x_3103_ = lean_nat_dec_eq(v_numOverlaps_3101_, v___x_2917_);
if (v___x_3103_ == 0)
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_del_object(v___x_3099_);
lean_dec_ref(v___x_3079_);
lean_dec(v___x_3076_);
lean_dec(v_stop_3075_);
lean_dec(v_start_3074_);
lean_dec_ref(v_array_3073_);
lean_dec_ref(v___x_3051_);
lean_dec(v___x_3048_);
lean_dec_ref(v___x_3023_);
lean_dec(v___x_3020_);
lean_dec_ref(v___x_2995_);
lean_dec(v___x_2991_);
lean_dec(v_fst_2939_);
lean_dec(v_next_2928_);
lean_dec(v_numDiscrEqs_2927_);
lean_dec_ref(v_inst_2926_);
lean_dec(v_fst_2925_);
lean_dec(v___f_2924_);
lean_dec(v_onAlt_2923_);
lean_dec_ref(v_inst_2920_);
lean_dec(v_inst_2919_);
lean_dec(v_toPure_2914_);
v___x_3104_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_3105_ = l_instInhabitedOfMonad___redArg(v_inst_2918_, v___x_3104_);
v___x_3106_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_3107_ = l_panic___redArg(v___x_3105_, v___x_3106_);
lean_dec(v___x_3105_);
v___y_2964_ = v___x_3107_;
goto v___jp_2963_;
}
else
{
lean_object* v___f_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___f_3113_; lean_object* v___x_3114_; lean_object* v___x_3116_; 
lean_inc(v_inst_2919_);
lean_inc_n(v_toPure_2914_, 2);
lean_inc(v___x_3048_);
v___f_3108_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___boxed), 4, 3);
lean_closure_set(v___f_3108_, 0, v___x_3048_);
lean_closure_set(v___f_3108_, 1, v_toPure_2914_);
lean_closure_set(v___f_3108_, 2, v_inst_2919_);
v___x_3109_ = lean_array_fget_borrowed(v_array_3073_, v_start_3074_);
v___x_3110_ = lean_box(v___x_2921_);
v___x_3111_ = lean_box(v_useSplitter_2922_);
v___x_3112_ = lean_box(v_hasUnitThunk_3102_);
lean_inc_ref(v_inst_2926_);
lean_inc(v___x_3109_);
lean_inc(v_toBind_2915_);
lean_inc_ref(v_inst_2918_);
v___f_3113_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__43___boxed), 21, 19);
lean_closure_set(v___f_3113_, 0, v___x_3048_);
lean_closure_set(v___f_3113_, 1, v_inst_2918_);
lean_closure_set(v___f_3113_, 2, v_inst_2920_);
lean_closure_set(v___f_3113_, 3, v___x_3110_);
lean_closure_set(v___f_3113_, 4, v___x_3111_);
lean_closure_set(v___f_3113_, 5, v_inst_2919_);
lean_closure_set(v___f_3113_, 6, v_onAlt_2923_);
lean_closure_set(v___f_3113_, 7, v_next_2928_);
lean_closure_set(v___f_3113_, 8, v_toBind_2915_);
lean_closure_set(v___f_3113_, 9, v___x_3109_);
lean_closure_set(v___f_3113_, 10, v___f_2924_);
lean_closure_set(v___f_3113_, 11, v_fst_2925_);
lean_closure_set(v___f_3113_, 12, v_inst_2926_);
lean_closure_set(v___f_3113_, 13, v_numDiscrEqs_2927_);
lean_closure_set(v___f_3113_, 14, v___f_3108_);
lean_closure_set(v___f_3113_, 15, v___x_3112_);
lean_closure_set(v___f_3113_, 16, v_toPure_2914_);
lean_closure_set(v___f_3113_, 17, v___x_2992_);
lean_closure_set(v___f_3113_, 18, v___x_2991_);
v___x_3114_ = lean_nat_add(v_start_3074_, v___x_2992_);
lean_dec(v_start_3074_);
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 1, v___x_3114_);
v___x_3116_ = v___x_3099_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_array_3073_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3114_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_stop_3075_);
v___x_3116_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
lean_object* v___f_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___f_3117_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__45), 8, 7);
lean_closure_set(v___f_3117_, 0, v_fst_2939_);
lean_closure_set(v___f_3117_, 1, v___x_3023_);
lean_closure_set(v___f_3117_, 2, v___x_2995_);
lean_closure_set(v___f_3117_, 3, v___x_3051_);
lean_closure_set(v___f_3117_, 4, v___x_3079_);
lean_closure_set(v___f_3117_, 5, v___x_3116_);
lean_closure_set(v___f_3117_, 6, v_toPure_2914_);
v___x_3118_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___redArg(v_inst_2918_, v_inst_2926_, v___x_3020_, v___x_3076_, v___f_3113_);
lean_inc(v_toBind_2915_);
v___x_3119_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v___x_3118_, v___f_3117_);
v___y_2964_ = v___x_3119_;
goto v___jp_2963_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_2963_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
lean_inc(v_toBind_2915_);
v___x_2965_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v___y_2964_, v___f_2916_);
v___x_2966_ = lean_apply_4(v_toBind_2915_, lean_box(0), lean_box(0), v___x_2965_, v___f_2962_);
return v___x_2966_;
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
lean_object* v___x_3155_ = _args[0];
lean_object* v_toPure_3156_ = _args[1];
lean_object* v_toBind_3157_ = _args[2];
lean_object* v___f_3158_ = _args[3];
lean_object* v___x_3159_ = _args[4];
lean_object* v_inst_3160_ = _args[5];
lean_object* v_inst_3161_ = _args[6];
lean_object* v_inst_3162_ = _args[7];
lean_object* v___x_3163_ = _args[8];
lean_object* v_useSplitter_3164_ = _args[9];
lean_object* v_onAlt_3165_ = _args[10];
lean_object* v___f_3166_ = _args[11];
lean_object* v_fst_3167_ = _args[12];
lean_object* v_inst_3168_ = _args[13];
lean_object* v_numDiscrEqs_3169_ = _args[14];
lean_object* v_next_3170_ = _args[15];
lean_object* v_acc_3171_ = _args[16];
lean_object* v_h_3172_ = _args[17];
lean_object* v_G_3173_ = _args[18];
_start:
{
uint8_t v___x_15501__boxed_3174_; uint8_t v_useSplitter_boxed_3175_; lean_object* v_res_3176_; 
v___x_15501__boxed_3174_ = lean_unbox(v___x_3163_);
v_useSplitter_boxed_3175_ = lean_unbox(v_useSplitter_3164_);
v_res_3176_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__46(v___x_3155_, v_toPure_3156_, v_toBind_3157_, v___f_3158_, v___x_3159_, v_inst_3160_, v_inst_3161_, v_inst_3162_, v___x_15501__boxed_3174_, v_useSplitter_boxed_3175_, v_onAlt_3165_, v___f_3166_, v_fst_3167_, v_inst_3168_, v_numDiscrEqs_3169_, v_next_3170_, v_acc_3171_, v_h_3172_, v_G_3173_);
lean_dec(v___x_3159_);
lean_dec(v___x_3155_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47(lean_object* v_fst_3177_, lean_object* v_numParams_3178_, lean_object* v_numDiscrs_3179_, lean_object* v_altInfos_3180_, lean_object* v_uElimPos_x3f_3181_, lean_object* v_snd_3182_, lean_object* v_overlaps_3183_, lean_object* v_splitterName_3184_, lean_object* v_matcherLevels_3185_, lean_object* v_params_x27_3186_, lean_object* v_fst_3187_, lean_object* v_discrs_x27_3188_, lean_object* v_fst_3189_, lean_object* v_toPure_3190_, lean_object* v_____do__lift_3191_){
_start:
{
lean_object* v_remaining_x27_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v_remaining_x27_3192_ = l_Array_append___redArg(v_fst_3177_, v_____do__lift_3191_);
v___x_3193_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3193_, 0, v_numParams_3178_);
lean_ctor_set(v___x_3193_, 1, v_numDiscrs_3179_);
lean_ctor_set(v___x_3193_, 2, v_altInfos_3180_);
lean_ctor_set(v___x_3193_, 3, v_uElimPos_x3f_3181_);
lean_ctor_set(v___x_3193_, 4, v_snd_3182_);
lean_ctor_set(v___x_3193_, 5, v_overlaps_3183_);
v___x_3194_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
lean_ctor_set(v___x_3194_, 1, v_splitterName_3184_);
lean_ctor_set(v___x_3194_, 2, v_matcherLevels_3185_);
lean_ctor_set(v___x_3194_, 3, v_params_x27_3186_);
lean_ctor_set(v___x_3194_, 4, v_fst_3187_);
lean_ctor_set(v___x_3194_, 5, v_discrs_x27_3188_);
lean_ctor_set(v___x_3194_, 6, v_fst_3189_);
lean_ctor_set(v___x_3194_, 7, v_remaining_x27_3192_);
v___x_3195_ = lean_apply_2(v_toPure_3190_, lean_box(0), v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed(lean_object* v_fst_3196_, lean_object* v_numParams_3197_, lean_object* v_numDiscrs_3198_, lean_object* v_altInfos_3199_, lean_object* v_uElimPos_x3f_3200_, lean_object* v_snd_3201_, lean_object* v_overlaps_3202_, lean_object* v_splitterName_3203_, lean_object* v_matcherLevels_3204_, lean_object* v_params_x27_3205_, lean_object* v_fst_3206_, lean_object* v_discrs_x27_3207_, lean_object* v_fst_3208_, lean_object* v_toPure_3209_, lean_object* v_____do__lift_3210_){
_start:
{
lean_object* v_res_3211_; 
v_res_3211_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__47(v_fst_3196_, v_numParams_3197_, v_numDiscrs_3198_, v_altInfos_3199_, v_uElimPos_x3f_3200_, v_snd_3201_, v_overlaps_3202_, v_splitterName_3203_, v_matcherLevels_3204_, v_params_x27_3205_, v_fst_3206_, v_discrs_x27_3207_, v_fst_3208_, v_toPure_3209_, v_____do__lift_3210_);
lean_dec_ref(v_____do__lift_3210_);
return v_res_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48(lean_object* v_fst_3212_, lean_object* v_numParams_3213_, lean_object* v_numDiscrs_3214_, lean_object* v_altInfos_3215_, lean_object* v_uElimPos_x3f_3216_, lean_object* v_snd_3217_, lean_object* v_overlaps_3218_, lean_object* v_splitterName_3219_, lean_object* v_matcherLevels_3220_, lean_object* v_params_x27_3221_, lean_object* v_fst_3222_, lean_object* v_discrs_x27_3223_, lean_object* v_toPure_3224_, lean_object* v_onRemaining_3225_, lean_object* v_remaining_3226_, lean_object* v_toBind_3227_, lean_object* v_____s_3228_){
_start:
{
lean_object* v_fst_3229_; lean_object* v___f_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_fst_3229_ = lean_ctor_get(v_____s_3228_, 0);
lean_inc(v_fst_3229_);
lean_dec_ref(v_____s_3228_);
v___f_3230_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__47___boxed), 15, 14);
lean_closure_set(v___f_3230_, 0, v_fst_3212_);
lean_closure_set(v___f_3230_, 1, v_numParams_3213_);
lean_closure_set(v___f_3230_, 2, v_numDiscrs_3214_);
lean_closure_set(v___f_3230_, 3, v_altInfos_3215_);
lean_closure_set(v___f_3230_, 4, v_uElimPos_x3f_3216_);
lean_closure_set(v___f_3230_, 5, v_snd_3217_);
lean_closure_set(v___f_3230_, 6, v_overlaps_3218_);
lean_closure_set(v___f_3230_, 7, v_splitterName_3219_);
lean_closure_set(v___f_3230_, 8, v_matcherLevels_3220_);
lean_closure_set(v___f_3230_, 9, v_params_x27_3221_);
lean_closure_set(v___f_3230_, 10, v_fst_3222_);
lean_closure_set(v___f_3230_, 11, v_discrs_x27_3223_);
lean_closure_set(v___f_3230_, 12, v_fst_3229_);
lean_closure_set(v___f_3230_, 13, v_toPure_3224_);
v___x_3231_ = lean_apply_1(v_onRemaining_3225_, v_remaining_3226_);
v___x_3232_ = lean_apply_4(v_toBind_3227_, lean_box(0), lean_box(0), v___x_3231_, v___f_3230_);
return v___x_3232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed(lean_object** _args){
lean_object* v_fst_3233_ = _args[0];
lean_object* v_numParams_3234_ = _args[1];
lean_object* v_numDiscrs_3235_ = _args[2];
lean_object* v_altInfos_3236_ = _args[3];
lean_object* v_uElimPos_x3f_3237_ = _args[4];
lean_object* v_snd_3238_ = _args[5];
lean_object* v_overlaps_3239_ = _args[6];
lean_object* v_splitterName_3240_ = _args[7];
lean_object* v_matcherLevels_3241_ = _args[8];
lean_object* v_params_x27_3242_ = _args[9];
lean_object* v_fst_3243_ = _args[10];
lean_object* v_discrs_x27_3244_ = _args[11];
lean_object* v_toPure_3245_ = _args[12];
lean_object* v_onRemaining_3246_ = _args[13];
lean_object* v_remaining_3247_ = _args[14];
lean_object* v_toBind_3248_ = _args[15];
lean_object* v_____s_3249_ = _args[16];
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__48(v_fst_3233_, v_numParams_3234_, v_numDiscrs_3235_, v_altInfos_3236_, v_uElimPos_x3f_3237_, v_snd_3238_, v_overlaps_3239_, v_splitterName_3240_, v_matcherLevels_3241_, v_params_x27_3242_, v_fst_3243_, v_discrs_x27_3244_, v_toPure_3245_, v_onRemaining_3246_, v_remaining_3247_, v_toBind_3248_, v_____s_3249_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49(lean_object* v_splitterMatchInfo_3251_, lean_object* v_fst_3252_, lean_object* v_numParams_3253_, lean_object* v_numDiscrs_3254_, lean_object* v_altInfos_3255_, lean_object* v_uElimPos_x3f_3256_, lean_object* v_snd_3257_, lean_object* v_overlaps_3258_, lean_object* v_splitterName_3259_, lean_object* v_matcherLevels_3260_, lean_object* v_params_x27_3261_, lean_object* v_fst_3262_, lean_object* v_discrs_x27_3263_, lean_object* v_toPure_3264_, lean_object* v_onRemaining_3265_, lean_object* v_remaining_3266_, lean_object* v_toBind_3267_, lean_object* v_origAltTypes_3268_, lean_object* v_alts_3269_, lean_object* v___x_3270_, lean_object* v___x_3271_, lean_object* v_remaining_x27_3272_, lean_object* v___f_3273_, lean_object* v_altTypes_3274_){
_start:
{
lean_object* v_altInfos_3275_; lean_object* v___f_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_altInfos_3275_ = lean_ctor_get(v_splitterMatchInfo_3251_, 2);
lean_inc_ref(v_altInfos_3275_);
lean_dec_ref(v_splitterMatchInfo_3251_);
lean_inc(v_toBind_3267_);
lean_inc_ref(v_altInfos_3255_);
v___f_3276_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__48___boxed), 17, 16);
lean_closure_set(v___f_3276_, 0, v_fst_3252_);
lean_closure_set(v___f_3276_, 1, v_numParams_3253_);
lean_closure_set(v___f_3276_, 2, v_numDiscrs_3254_);
lean_closure_set(v___f_3276_, 3, v_altInfos_3255_);
lean_closure_set(v___f_3276_, 4, v_uElimPos_x3f_3256_);
lean_closure_set(v___f_3276_, 5, v_snd_3257_);
lean_closure_set(v___f_3276_, 6, v_overlaps_3258_);
lean_closure_set(v___f_3276_, 7, v_splitterName_3259_);
lean_closure_set(v___f_3276_, 8, v_matcherLevels_3260_);
lean_closure_set(v___f_3276_, 9, v_params_x27_3261_);
lean_closure_set(v___f_3276_, 10, v_fst_3262_);
lean_closure_set(v___f_3276_, 11, v_discrs_x27_3263_);
lean_closure_set(v___f_3276_, 12, v_toPure_3264_);
lean_closure_set(v___f_3276_, 13, v_onRemaining_3265_);
lean_closure_set(v___f_3276_, 14, v_remaining_3266_);
lean_closure_set(v___f_3276_, 15, v_toBind_3267_);
v___x_3277_ = lean_array_get_size(v_altInfos_3255_);
v___x_3278_ = lean_array_get_size(v_altInfos_3275_);
v___x_3279_ = lean_array_get_size(v_origAltTypes_3268_);
v___x_3280_ = lean_array_get_size(v_altTypes_3274_);
lean_inc_n(v___x_3270_, 5);
v___x_3281_ = l_Array_toSubarray___redArg(v_alts_3269_, v___x_3270_, v___x_3271_);
v___x_3282_ = l_Array_toSubarray___redArg(v_altInfos_3255_, v___x_3270_, v___x_3277_);
v___x_3283_ = l_Array_toSubarray___redArg(v_altInfos_3275_, v___x_3270_, v___x_3278_);
v___x_3284_ = l_Array_toSubarray___redArg(v_origAltTypes_3268_, v___x_3270_, v___x_3279_);
v___x_3285_ = l_Array_toSubarray___redArg(v_altTypes_3274_, v___x_3270_, v___x_3280_);
v___x_3286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3283_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3282_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3281_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_remaining_x27_3272_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
v___x_3291_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_3273_, v___x_3270_, v___x_3290_, lean_box(0));
v___x_3292_ = lean_apply_4(v_toBind_3267_, lean_box(0), lean_box(0), v___x_3291_, v___f_3276_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed(lean_object** _args){
lean_object* v_splitterMatchInfo_3293_ = _args[0];
lean_object* v_fst_3294_ = _args[1];
lean_object* v_numParams_3295_ = _args[2];
lean_object* v_numDiscrs_3296_ = _args[3];
lean_object* v_altInfos_3297_ = _args[4];
lean_object* v_uElimPos_x3f_3298_ = _args[5];
lean_object* v_snd_3299_ = _args[6];
lean_object* v_overlaps_3300_ = _args[7];
lean_object* v_splitterName_3301_ = _args[8];
lean_object* v_matcherLevels_3302_ = _args[9];
lean_object* v_params_x27_3303_ = _args[10];
lean_object* v_fst_3304_ = _args[11];
lean_object* v_discrs_x27_3305_ = _args[12];
lean_object* v_toPure_3306_ = _args[13];
lean_object* v_onRemaining_3307_ = _args[14];
lean_object* v_remaining_3308_ = _args[15];
lean_object* v_toBind_3309_ = _args[16];
lean_object* v_origAltTypes_3310_ = _args[17];
lean_object* v_alts_3311_ = _args[18];
lean_object* v___x_3312_ = _args[19];
lean_object* v___x_3313_ = _args[20];
lean_object* v_remaining_x27_3314_ = _args[21];
lean_object* v___f_3315_ = _args[22];
lean_object* v_altTypes_3316_ = _args[23];
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__49(v_splitterMatchInfo_3293_, v_fst_3294_, v_numParams_3295_, v_numDiscrs_3296_, v_altInfos_3297_, v_uElimPos_x3f_3298_, v_snd_3299_, v_overlaps_3300_, v_splitterName_3301_, v_matcherLevels_3302_, v_params_x27_3303_, v_fst_3304_, v_discrs_x27_3305_, v_toPure_3306_, v_onRemaining_3307_, v_remaining_3308_, v_toBind_3309_, v_origAltTypes_3310_, v_alts_3311_, v___x_3312_, v___x_3313_, v_remaining_x27_3314_, v___f_3315_, v_altTypes_3316_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__50(lean_object* v___x_3318_, lean_object* v_aux2_3319_, lean_object* v_inst_3320_, lean_object* v_toBind_3321_, lean_object* v___f_3322_, lean_object* v_____r_3323_){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3324_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3324_, 0, v___x_3318_);
lean_closure_set(v___x_3324_, 1, v_aux2_3319_);
v___x_3325_ = lean_apply_2(v_inst_3320_, lean_box(0), v___x_3324_);
v___x_3326_ = lean_apply_4(v_toBind_3321_, lean_box(0), lean_box(0), v___x_3325_, v___f_3322_);
return v___x_3326_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1(void){
_start:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__0));
v___x_3329_ = l_Lean_stringToMessageData(v___x_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53(lean_object* v___x_3330_, lean_object* v_params_x27_3331_, lean_object* v_fst_3332_, lean_object* v_discrs_x27_3333_, lean_object* v_fst_3334_, lean_object* v_numParams_3335_, lean_object* v_numDiscrs_3336_, lean_object* v_altInfos_3337_, lean_object* v_uElimPos_x3f_3338_, lean_object* v_snd_3339_, lean_object* v_overlaps_3340_, lean_object* v_matcherLevels_3341_, lean_object* v_toPure_3342_, lean_object* v_onRemaining_3343_, lean_object* v_remaining_3344_, lean_object* v_toBind_3345_, lean_object* v_origAltTypes_3346_, lean_object* v_alts_3347_, lean_object* v___x_3348_, lean_object* v___x_3349_, lean_object* v_remaining_x27_3350_, lean_object* v___f_3351_, lean_object* v_inst_3352_, lean_object* v___x_3353_, uint8_t v___x_3354_, lean_object* v_liftWith_3355_, lean_object* v_restoreM_3356_, lean_object* v_matchEqns_3357_){
_start:
{
lean_object* v_splitterName_3358_; lean_object* v_splitterMatchInfo_3359_; lean_object* v___x_3360_; lean_object* v_aux2_3361_; lean_object* v_aux2_3362_; lean_object* v_aux2_3363_; lean_object* v___x_3364_; lean_object* v___f_3365_; lean_object* v___f_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___f_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___f_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_splitterName_3358_ = lean_ctor_get(v_matchEqns_3357_, 1);
lean_inc_n(v_splitterName_3358_, 2);
v_splitterMatchInfo_3359_ = lean_ctor_get(v_matchEqns_3357_, 2);
lean_inc_ref(v_splitterMatchInfo_3359_);
lean_dec_ref(v_matchEqns_3357_);
v___x_3360_ = l_Lean_mkConst(v_splitterName_3358_, v___x_3330_);
v_aux2_3361_ = l_Lean_mkAppN(v___x_3360_, v_params_x27_3331_);
lean_inc_ref(v_fst_3332_);
v_aux2_3362_ = l_Lean_Expr_app___override(v_aux2_3361_, v_fst_3332_);
v_aux2_3363_ = l_Lean_mkAppN(v_aux2_3362_, v_discrs_x27_3333_);
lean_inc_ref_n(v_aux2_3363_, 2);
v___x_3364_ = l_Lean_indentExpr(v_aux2_3363_);
lean_inc(v___x_3349_);
lean_inc_n(v_toBind_3345_, 3);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__49___boxed), 24, 23);
lean_closure_set(v___f_3365_, 0, v_splitterMatchInfo_3359_);
lean_closure_set(v___f_3365_, 1, v_fst_3334_);
lean_closure_set(v___f_3365_, 2, v_numParams_3335_);
lean_closure_set(v___f_3365_, 3, v_numDiscrs_3336_);
lean_closure_set(v___f_3365_, 4, v_altInfos_3337_);
lean_closure_set(v___f_3365_, 5, v_uElimPos_x3f_3338_);
lean_closure_set(v___f_3365_, 6, v_snd_3339_);
lean_closure_set(v___f_3365_, 7, v_overlaps_3340_);
lean_closure_set(v___f_3365_, 8, v_splitterName_3358_);
lean_closure_set(v___f_3365_, 9, v_matcherLevels_3341_);
lean_closure_set(v___f_3365_, 10, v_params_x27_3331_);
lean_closure_set(v___f_3365_, 11, v_fst_3332_);
lean_closure_set(v___f_3365_, 12, v_discrs_x27_3333_);
lean_closure_set(v___f_3365_, 13, v_toPure_3342_);
lean_closure_set(v___f_3365_, 14, v_onRemaining_3343_);
lean_closure_set(v___f_3365_, 15, v_remaining_3344_);
lean_closure_set(v___f_3365_, 16, v_toBind_3345_);
lean_closure_set(v___f_3365_, 17, v_origAltTypes_3346_);
lean_closure_set(v___f_3365_, 18, v_alts_3347_);
lean_closure_set(v___f_3365_, 19, v___x_3348_);
lean_closure_set(v___f_3365_, 20, v___x_3349_);
lean_closure_set(v___f_3365_, 21, v_remaining_x27_3350_);
lean_closure_set(v___f_3365_, 22, v___f_3351_);
lean_inc(v_inst_3352_);
v___f_3366_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__50), 6, 5);
lean_closure_set(v___f_3366_, 0, v___x_3349_);
lean_closure_set(v___f_3366_, 1, v_aux2_3363_);
lean_closure_set(v___f_3366_, 2, v_inst_3352_);
lean_closure_set(v___f_3366_, 3, v_toBind_3345_);
lean_closure_set(v___f_3366_, 4, v___f_3365_);
v___x_3367_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
lean_ctor_set(v___x_3368_, 1, v___x_3364_);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v___x_3353_);
v___f_3370_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3370_, 0, v___x_3369_);
v___x_3371_ = lean_box(v___x_3354_);
v___x_3372_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3372_, 0, v_aux2_3363_);
lean_closure_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_apply_2(v_inst_3352_, lean_box(0), v___x_3372_);
v___f_3374_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3374_, 0, v___x_3373_);
lean_closure_set(v___f_3374_, 1, v___f_3370_);
v___x_3375_ = lean_apply_2(v_liftWith_3355_, lean_box(0), v___f_3374_);
v___x_3376_ = lean_apply_1(v_restoreM_3356_, lean_box(0));
v___x_3377_ = lean_apply_4(v_toBind_3345_, lean_box(0), lean_box(0), v___x_3375_, v___x_3376_);
v___x_3378_ = lean_apply_4(v_toBind_3345_, lean_box(0), lean_box(0), v___x_3377_, v___f_3366_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed(lean_object** _args){
lean_object* v___x_3379_ = _args[0];
lean_object* v_params_x27_3380_ = _args[1];
lean_object* v_fst_3381_ = _args[2];
lean_object* v_discrs_x27_3382_ = _args[3];
lean_object* v_fst_3383_ = _args[4];
lean_object* v_numParams_3384_ = _args[5];
lean_object* v_numDiscrs_3385_ = _args[6];
lean_object* v_altInfos_3386_ = _args[7];
lean_object* v_uElimPos_x3f_3387_ = _args[8];
lean_object* v_snd_3388_ = _args[9];
lean_object* v_overlaps_3389_ = _args[10];
lean_object* v_matcherLevels_3390_ = _args[11];
lean_object* v_toPure_3391_ = _args[12];
lean_object* v_onRemaining_3392_ = _args[13];
lean_object* v_remaining_3393_ = _args[14];
lean_object* v_toBind_3394_ = _args[15];
lean_object* v_origAltTypes_3395_ = _args[16];
lean_object* v_alts_3396_ = _args[17];
lean_object* v___x_3397_ = _args[18];
lean_object* v___x_3398_ = _args[19];
lean_object* v_remaining_x27_3399_ = _args[20];
lean_object* v___f_3400_ = _args[21];
lean_object* v_inst_3401_ = _args[22];
lean_object* v___x_3402_ = _args[23];
lean_object* v___x_3403_ = _args[24];
lean_object* v_liftWith_3404_ = _args[25];
lean_object* v_restoreM_3405_ = _args[26];
lean_object* v_matchEqns_3406_ = _args[27];
_start:
{
uint8_t v___x_16046__boxed_3407_; lean_object* v_res_3408_; 
v___x_16046__boxed_3407_ = lean_unbox(v___x_3403_);
v_res_3408_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__53(v___x_3379_, v_params_x27_3380_, v_fst_3381_, v_discrs_x27_3382_, v_fst_3383_, v_numParams_3384_, v_numDiscrs_3385_, v_altInfos_3386_, v_uElimPos_x3f_3387_, v_snd_3388_, v_overlaps_3389_, v_matcherLevels_3390_, v_toPure_3391_, v_onRemaining_3392_, v_remaining_3393_, v_toBind_3394_, v_origAltTypes_3395_, v_alts_3396_, v___x_3397_, v___x_3398_, v_remaining_x27_3399_, v___f_3400_, v_inst_3401_, v___x_3402_, v___x_16046__boxed_3407_, v_liftWith_3404_, v_restoreM_3405_, v_matchEqns_3406_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51(lean_object* v___x_3409_, lean_object* v_params_x27_3410_, lean_object* v_fst_3411_, lean_object* v_discrs_x27_3412_, lean_object* v_fst_3413_, lean_object* v_numParams_3414_, lean_object* v_numDiscrs_3415_, lean_object* v_altInfos_3416_, lean_object* v_uElimPos_x3f_3417_, lean_object* v_snd_3418_, lean_object* v_overlaps_3419_, lean_object* v_matcherLevels_3420_, lean_object* v_toPure_3421_, lean_object* v_onRemaining_3422_, lean_object* v_remaining_3423_, lean_object* v_toBind_3424_, lean_object* v_alts_3425_, lean_object* v___x_3426_, lean_object* v___x_3427_, lean_object* v_remaining_x27_3428_, lean_object* v___f_3429_, lean_object* v_inst_3430_, lean_object* v___x_3431_, uint8_t v___x_3432_, lean_object* v_liftWith_3433_, lean_object* v_restoreM_3434_, lean_object* v_matcherName_3435_, lean_object* v_origAltTypes_3436_){
_start:
{
lean_object* v___x_3437_; lean_object* v___f_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3437_ = lean_box(v___x_3432_);
lean_inc(v_inst_3430_);
lean_inc(v_toBind_3424_);
v___f_3438_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__53___boxed), 28, 27);
lean_closure_set(v___f_3438_, 0, v___x_3409_);
lean_closure_set(v___f_3438_, 1, v_params_x27_3410_);
lean_closure_set(v___f_3438_, 2, v_fst_3411_);
lean_closure_set(v___f_3438_, 3, v_discrs_x27_3412_);
lean_closure_set(v___f_3438_, 4, v_fst_3413_);
lean_closure_set(v___f_3438_, 5, v_numParams_3414_);
lean_closure_set(v___f_3438_, 6, v_numDiscrs_3415_);
lean_closure_set(v___f_3438_, 7, v_altInfos_3416_);
lean_closure_set(v___f_3438_, 8, v_uElimPos_x3f_3417_);
lean_closure_set(v___f_3438_, 9, v_snd_3418_);
lean_closure_set(v___f_3438_, 10, v_overlaps_3419_);
lean_closure_set(v___f_3438_, 11, v_matcherLevels_3420_);
lean_closure_set(v___f_3438_, 12, v_toPure_3421_);
lean_closure_set(v___f_3438_, 13, v_onRemaining_3422_);
lean_closure_set(v___f_3438_, 14, v_remaining_3423_);
lean_closure_set(v___f_3438_, 15, v_toBind_3424_);
lean_closure_set(v___f_3438_, 16, v_origAltTypes_3436_);
lean_closure_set(v___f_3438_, 17, v_alts_3425_);
lean_closure_set(v___f_3438_, 18, v___x_3426_);
lean_closure_set(v___f_3438_, 19, v___x_3427_);
lean_closure_set(v___f_3438_, 20, v_remaining_x27_3428_);
lean_closure_set(v___f_3438_, 21, v___f_3429_);
lean_closure_set(v___f_3438_, 22, v_inst_3430_);
lean_closure_set(v___f_3438_, 23, v___x_3431_);
lean_closure_set(v___f_3438_, 24, v___x_3437_);
lean_closure_set(v___f_3438_, 25, v_liftWith_3433_);
lean_closure_set(v___f_3438_, 26, v_restoreM_3434_);
v___x_3439_ = lean_alloc_closure((void*)(l_Lean_Meta_Match_getEquationsFor___boxed), 6, 1);
lean_closure_set(v___x_3439_, 0, v_matcherName_3435_);
v___x_3440_ = lean_apply_2(v_inst_3430_, lean_box(0), v___x_3439_);
v___x_3441_ = lean_apply_4(v_toBind_3424_, lean_box(0), lean_box(0), v___x_3440_, v___f_3438_);
return v___x_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed(lean_object** _args){
lean_object* v___x_3442_ = _args[0];
lean_object* v_params_x27_3443_ = _args[1];
lean_object* v_fst_3444_ = _args[2];
lean_object* v_discrs_x27_3445_ = _args[3];
lean_object* v_fst_3446_ = _args[4];
lean_object* v_numParams_3447_ = _args[5];
lean_object* v_numDiscrs_3448_ = _args[6];
lean_object* v_altInfos_3449_ = _args[7];
lean_object* v_uElimPos_x3f_3450_ = _args[8];
lean_object* v_snd_3451_ = _args[9];
lean_object* v_overlaps_3452_ = _args[10];
lean_object* v_matcherLevels_3453_ = _args[11];
lean_object* v_toPure_3454_ = _args[12];
lean_object* v_onRemaining_3455_ = _args[13];
lean_object* v_remaining_3456_ = _args[14];
lean_object* v_toBind_3457_ = _args[15];
lean_object* v_alts_3458_ = _args[16];
lean_object* v___x_3459_ = _args[17];
lean_object* v___x_3460_ = _args[18];
lean_object* v_remaining_x27_3461_ = _args[19];
lean_object* v___f_3462_ = _args[20];
lean_object* v_inst_3463_ = _args[21];
lean_object* v___x_3464_ = _args[22];
lean_object* v___x_3465_ = _args[23];
lean_object* v_liftWith_3466_ = _args[24];
lean_object* v_restoreM_3467_ = _args[25];
lean_object* v_matcherName_3468_ = _args[26];
lean_object* v_origAltTypes_3469_ = _args[27];
_start:
{
uint8_t v___x_16108__boxed_3470_; lean_object* v_res_3471_; 
v___x_16108__boxed_3470_ = lean_unbox(v___x_3465_);
v_res_3471_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__51(v___x_3442_, v_params_x27_3443_, v_fst_3444_, v_discrs_x27_3445_, v_fst_3446_, v_numParams_3447_, v_numDiscrs_3448_, v_altInfos_3449_, v_uElimPos_x3f_3450_, v_snd_3451_, v_overlaps_3452_, v_matcherLevels_3453_, v_toPure_3454_, v_onRemaining_3455_, v_remaining_3456_, v_toBind_3457_, v_alts_3458_, v___x_3459_, v___x_3460_, v_remaining_x27_3461_, v___f_3462_, v_inst_3463_, v___x_3464_, v___x_16108__boxed_3470_, v_liftWith_3466_, v_restoreM_3467_, v_matcherName_3468_, v_origAltTypes_3469_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52(lean_object* v_alts_3472_, lean_object* v_toPure_3473_, lean_object* v_toBind_3474_, lean_object* v___f_3475_, lean_object* v___x_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, uint8_t v___x_3480_, uint8_t v_useSplitter_3481_, lean_object* v_onAlt_3482_, lean_object* v___f_3483_, lean_object* v_fst_3484_, lean_object* v_inst_3485_, lean_object* v_numDiscrEqs_3486_, lean_object* v___x_3487_, lean_object* v_params_x27_3488_, lean_object* v_fst_3489_, lean_object* v_discrs_x27_3490_, lean_object* v_fst_3491_, lean_object* v_numParams_3492_, lean_object* v_numDiscrs_3493_, lean_object* v_altInfos_3494_, lean_object* v_uElimPos_x3f_3495_, lean_object* v_snd_3496_, lean_object* v_overlaps_3497_, lean_object* v_matcherLevels_3498_, lean_object* v_onRemaining_3499_, lean_object* v_remaining_3500_, lean_object* v_remaining_x27_3501_, lean_object* v___x_3502_, uint8_t v___x_3503_, lean_object* v_liftWith_3504_, lean_object* v_restoreM_3505_, lean_object* v_matcherName_3506_, lean_object* v_aux1_3507_, lean_object* v_____r_3508_){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; lean_object* v___f_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3509_ = lean_array_get_size(v_alts_3472_);
v___x_3510_ = lean_box(v___x_3480_);
v___x_3511_ = lean_box(v_useSplitter_3481_);
lean_inc_n(v_inst_3478_, 2);
lean_inc(v___x_3476_);
lean_inc_n(v_toBind_3474_, 2);
lean_inc(v_toPure_3473_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__46___boxed), 19, 15);
lean_closure_set(v___f_3512_, 0, v___x_3509_);
lean_closure_set(v___f_3512_, 1, v_toPure_3473_);
lean_closure_set(v___f_3512_, 2, v_toBind_3474_);
lean_closure_set(v___f_3512_, 3, v___f_3475_);
lean_closure_set(v___f_3512_, 4, v___x_3476_);
lean_closure_set(v___f_3512_, 5, v_inst_3477_);
lean_closure_set(v___f_3512_, 6, v_inst_3478_);
lean_closure_set(v___f_3512_, 7, v_inst_3479_);
lean_closure_set(v___f_3512_, 8, v___x_3510_);
lean_closure_set(v___f_3512_, 9, v___x_3511_);
lean_closure_set(v___f_3512_, 10, v_onAlt_3482_);
lean_closure_set(v___f_3512_, 11, v___f_3483_);
lean_closure_set(v___f_3512_, 12, v_fst_3484_);
lean_closure_set(v___f_3512_, 13, v_inst_3485_);
lean_closure_set(v___f_3512_, 14, v_numDiscrEqs_3486_);
v___x_3513_ = lean_box(v___x_3503_);
v___f_3514_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__51___boxed), 28, 27);
lean_closure_set(v___f_3514_, 0, v___x_3487_);
lean_closure_set(v___f_3514_, 1, v_params_x27_3488_);
lean_closure_set(v___f_3514_, 2, v_fst_3489_);
lean_closure_set(v___f_3514_, 3, v_discrs_x27_3490_);
lean_closure_set(v___f_3514_, 4, v_fst_3491_);
lean_closure_set(v___f_3514_, 5, v_numParams_3492_);
lean_closure_set(v___f_3514_, 6, v_numDiscrs_3493_);
lean_closure_set(v___f_3514_, 7, v_altInfos_3494_);
lean_closure_set(v___f_3514_, 8, v_uElimPos_x3f_3495_);
lean_closure_set(v___f_3514_, 9, v_snd_3496_);
lean_closure_set(v___f_3514_, 10, v_overlaps_3497_);
lean_closure_set(v___f_3514_, 11, v_matcherLevels_3498_);
lean_closure_set(v___f_3514_, 12, v_toPure_3473_);
lean_closure_set(v___f_3514_, 13, v_onRemaining_3499_);
lean_closure_set(v___f_3514_, 14, v_remaining_3500_);
lean_closure_set(v___f_3514_, 15, v_toBind_3474_);
lean_closure_set(v___f_3514_, 16, v_alts_3472_);
lean_closure_set(v___f_3514_, 17, v___x_3476_);
lean_closure_set(v___f_3514_, 18, v___x_3509_);
lean_closure_set(v___f_3514_, 19, v_remaining_x27_3501_);
lean_closure_set(v___f_3514_, 20, v___f_3512_);
lean_closure_set(v___f_3514_, 21, v_inst_3478_);
lean_closure_set(v___f_3514_, 22, v___x_3502_);
lean_closure_set(v___f_3514_, 23, v___x_3513_);
lean_closure_set(v___f_3514_, 24, v_liftWith_3504_);
lean_closure_set(v___f_3514_, 25, v_restoreM_3505_);
lean_closure_set(v___f_3514_, 26, v_matcherName_3506_);
v___x_3515_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_3515_, 0, v___x_3509_);
lean_closure_set(v___x_3515_, 1, v_aux1_3507_);
v___x_3516_ = lean_apply_2(v_inst_3478_, lean_box(0), v___x_3515_);
v___x_3517_ = lean_apply_4(v_toBind_3474_, lean_box(0), lean_box(0), v___x_3516_, v___f_3514_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed(lean_object** _args){
lean_object* v_alts_3518_ = _args[0];
lean_object* v_toPure_3519_ = _args[1];
lean_object* v_toBind_3520_ = _args[2];
lean_object* v___f_3521_ = _args[3];
lean_object* v___x_3522_ = _args[4];
lean_object* v_inst_3523_ = _args[5];
lean_object* v_inst_3524_ = _args[6];
lean_object* v_inst_3525_ = _args[7];
lean_object* v___x_3526_ = _args[8];
lean_object* v_useSplitter_3527_ = _args[9];
lean_object* v_onAlt_3528_ = _args[10];
lean_object* v___f_3529_ = _args[11];
lean_object* v_fst_3530_ = _args[12];
lean_object* v_inst_3531_ = _args[13];
lean_object* v_numDiscrEqs_3532_ = _args[14];
lean_object* v___x_3533_ = _args[15];
lean_object* v_params_x27_3534_ = _args[16];
lean_object* v_fst_3535_ = _args[17];
lean_object* v_discrs_x27_3536_ = _args[18];
lean_object* v_fst_3537_ = _args[19];
lean_object* v_numParams_3538_ = _args[20];
lean_object* v_numDiscrs_3539_ = _args[21];
lean_object* v_altInfos_3540_ = _args[22];
lean_object* v_uElimPos_x3f_3541_ = _args[23];
lean_object* v_snd_3542_ = _args[24];
lean_object* v_overlaps_3543_ = _args[25];
lean_object* v_matcherLevels_3544_ = _args[26];
lean_object* v_onRemaining_3545_ = _args[27];
lean_object* v_remaining_3546_ = _args[28];
lean_object* v_remaining_x27_3547_ = _args[29];
lean_object* v___x_3548_ = _args[30];
lean_object* v___x_3549_ = _args[31];
lean_object* v_liftWith_3550_ = _args[32];
lean_object* v_restoreM_3551_ = _args[33];
lean_object* v_matcherName_3552_ = _args[34];
lean_object* v_aux1_3553_ = _args[35];
lean_object* v_____r_3554_ = _args[36];
_start:
{
uint8_t v___x_16142__boxed_3555_; uint8_t v_useSplitter_boxed_3556_; uint8_t v___x_16149__boxed_3557_; lean_object* v_res_3558_; 
v___x_16142__boxed_3555_ = lean_unbox(v___x_3526_);
v_useSplitter_boxed_3556_ = lean_unbox(v_useSplitter_3527_);
v___x_16149__boxed_3557_ = lean_unbox(v___x_3549_);
v_res_3558_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__52(v_alts_3518_, v_toPure_3519_, v_toBind_3520_, v___f_3521_, v___x_3522_, v_inst_3523_, v_inst_3524_, v_inst_3525_, v___x_16142__boxed_3555_, v_useSplitter_boxed_3556_, v_onAlt_3528_, v___f_3529_, v_fst_3530_, v_inst_3531_, v_numDiscrEqs_3532_, v___x_3533_, v_params_x27_3534_, v_fst_3535_, v_discrs_x27_3536_, v_fst_3537_, v_numParams_3538_, v_numDiscrs_3539_, v_altInfos_3540_, v_uElimPos_x3f_3541_, v_snd_3542_, v_overlaps_3543_, v_matcherLevels_3544_, v_onRemaining_3545_, v_remaining_3546_, v_remaining_x27_3547_, v___x_3548_, v___x_16149__boxed_3557_, v_liftWith_3550_, v_restoreM_3551_, v_matcherName_3552_, v_aux1_3553_, v_____r_3554_);
return v_res_3558_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; 
v___x_3560_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__0));
v___x_3561_ = l_Lean_stringToMessageData(v___x_3560_);
return v___x_3561_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__2));
v___x_3564_ = l_Lean_stringToMessageData(v___x_3563_);
return v___x_3564_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__4));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55(lean_object* v_numParams_3568_, lean_object* v_numDiscrs_3569_, lean_object* v_altInfos_3570_, lean_object* v_uElimPos_x3f_3571_, lean_object* v_snd_3572_, lean_object* v_overlaps_3573_, lean_object* v_matcherName_3574_, lean_object* v_matcherLevels_3575_, lean_object* v_params_x27_3576_, lean_object* v_fst_3577_, lean_object* v_discrs_x27_3578_, lean_object* v_toPure_3579_, lean_object* v_onRemaining_3580_, lean_object* v_remaining_3581_, lean_object* v_toBind_3582_, lean_object* v_inst_3583_, lean_object* v_alts_3584_, lean_object* v___f_3585_, uint8_t v___x_3586_, lean_object* v_inst_3587_, lean_object* v_remaining_x27_3588_, lean_object* v_onAlt_3589_, lean_object* v_inst_3590_, lean_object* v___f_3591_, lean_object* v_matcherApp_3592_, lean_object* v___x_3593_, uint8_t v_useSplitter_3594_, uint8_t v_isCasesOn_3595_, lean_object* v___f_3596_, lean_object* v_inst_3597_, lean_object* v___f_3598_, lean_object* v_numDiscrEqs_3599_, lean_object* v_____s_3600_){
_start:
{
lean_object* v_snd_3601_; lean_object* v_fst_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3669_; 
v_snd_3601_ = lean_ctor_get(v_____s_3600_, 1);
v_fst_3602_ = lean_ctor_get(v_____s_3600_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v_____s_3600_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3604_ = v_____s_3600_;
v_isShared_3605_ = v_isSharedCheck_3669_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_snd_3601_);
lean_inc(v_fst_3602_);
lean_dec(v_____s_3600_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3669_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v_fst_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3667_; 
v_fst_3606_ = lean_ctor_get(v_snd_3601_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v_snd_3601_);
if (v_isSharedCheck_3667_ == 0)
{
lean_object* v_unused_3668_; 
v_unused_3668_ = lean_ctor_get(v_snd_3601_, 1);
lean_dec(v_unused_3668_);
v___x_3608_ = v_snd_3601_;
v_isShared_3609_ = v_isSharedCheck_3667_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_fst_3606_);
lean_dec(v_snd_3601_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3667_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___f_3610_; 
lean_inc(v_toBind_3582_);
lean_inc_ref(v_remaining_3581_);
lean_inc(v_onRemaining_3580_);
lean_inc(v_toPure_3579_);
lean_inc_ref(v_discrs_x27_3578_);
lean_inc_ref(v_fst_3577_);
lean_inc_ref(v_params_x27_3576_);
lean_inc_ref(v_matcherLevels_3575_);
lean_inc(v_matcherName_3574_);
lean_inc_ref(v_overlaps_3573_);
lean_inc_ref(v_snd_3572_);
lean_inc(v_uElimPos_x3f_3571_);
lean_inc_ref(v_altInfos_3570_);
lean_inc(v_numDiscrs_3569_);
lean_inc(v_numParams_3568_);
lean_inc(v_fst_3602_);
v___f_3610_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__21___boxed), 17, 16);
lean_closure_set(v___f_3610_, 0, v_fst_3602_);
lean_closure_set(v___f_3610_, 1, v_numParams_3568_);
lean_closure_set(v___f_3610_, 2, v_numDiscrs_3569_);
lean_closure_set(v___f_3610_, 3, v_altInfos_3570_);
lean_closure_set(v___f_3610_, 4, v_uElimPos_x3f_3571_);
lean_closure_set(v___f_3610_, 5, v_snd_3572_);
lean_closure_set(v___f_3610_, 6, v_overlaps_3573_);
lean_closure_set(v___f_3610_, 7, v_matcherName_3574_);
lean_closure_set(v___f_3610_, 8, v_matcherLevels_3575_);
lean_closure_set(v___f_3610_, 9, v_params_x27_3576_);
lean_closure_set(v___f_3610_, 10, v_fst_3577_);
lean_closure_set(v___f_3610_, 11, v_discrs_x27_3578_);
lean_closure_set(v___f_3610_, 12, v_toPure_3579_);
lean_closure_set(v___f_3610_, 13, v_onRemaining_3580_);
lean_closure_set(v___f_3610_, 14, v_remaining_3581_);
lean_closure_set(v___f_3610_, 15, v_toBind_3582_);
if (v_useSplitter_3594_ == 0)
{
lean_del_object(v___x_3604_);
lean_dec(v_fst_3602_);
lean_dec(v_numDiscrEqs_3599_);
lean_dec(v___f_3598_);
lean_dec_ref(v_inst_3597_);
lean_dec(v___f_3596_);
lean_dec_ref(v_remaining_3581_);
lean_dec(v_onRemaining_3580_);
lean_dec_ref(v_overlaps_3573_);
lean_dec_ref(v_snd_3572_);
lean_dec(v_uElimPos_x3f_3571_);
lean_dec_ref(v_altInfos_3570_);
lean_dec(v_numDiscrs_3569_);
lean_dec(v_numParams_3568_);
goto v___jp_3611_;
}
else
{
uint8_t v___x_3638_; 
v___x_3638_ = lean_bool_not(v_isCasesOn_3595_);
if (v___x_3638_ == 0)
{
lean_del_object(v___x_3604_);
lean_dec(v_fst_3602_);
lean_dec(v_numDiscrEqs_3599_);
lean_dec(v___f_3598_);
lean_dec_ref(v_inst_3597_);
lean_dec(v___f_3596_);
lean_dec_ref(v_remaining_3581_);
lean_dec(v_onRemaining_3580_);
lean_dec_ref(v_overlaps_3573_);
lean_dec_ref(v_snd_3572_);
lean_dec(v_uElimPos_x3f_3571_);
lean_dec_ref(v_altInfos_3570_);
lean_dec(v_numDiscrs_3569_);
lean_dec(v_numParams_3568_);
goto v___jp_3611_;
}
else
{
lean_object* v_liftWith_3639_; lean_object* v_restoreM_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v_aux1_3643_; lean_object* v_aux1_3644_; lean_object* v_aux1_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
lean_dec_ref(v___f_3610_);
lean_del_object(v___x_3608_);
lean_dec_ref(v_matcherApp_3592_);
lean_dec(v___f_3591_);
lean_dec(v___f_3585_);
v_liftWith_3639_ = lean_ctor_get(v_inst_3583_, 0);
lean_inc(v_liftWith_3639_);
v_restoreM_3640_ = lean_ctor_get(v_inst_3583_, 1);
lean_inc(v_restoreM_3640_);
lean_inc_ref(v_matcherLevels_3575_);
v___x_3641_ = lean_array_to_list(v_matcherLevels_3575_);
lean_inc(v___x_3641_);
lean_inc(v_matcherName_3574_);
v___x_3642_ = l_Lean_mkConst(v_matcherName_3574_, v___x_3641_);
v_aux1_3643_ = l_Lean_mkAppN(v___x_3642_, v_params_x27_3576_);
lean_inc_ref(v_fst_3577_);
v_aux1_3644_ = l_Lean_Expr_app___override(v_aux1_3643_, v_fst_3577_);
v_aux1_3645_ = l_Lean_mkAppN(v_aux1_3644_, v_discrs_x27_3578_);
lean_inc_ref(v_aux1_3645_);
v___x_3646_ = l_Lean_indentExpr(v_aux1_3645_);
v___x_3647_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 7);
lean_ctor_set(v___x_3604_, 1, v___x_3646_);
lean_ctor_set(v___x_3604_, 0, v___x_3647_);
v___x_3649_ = v___x_3604_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3647_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3646_);
v___x_3649_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___f_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___f_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___f_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3650_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___f_3652_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3652_, 0, v___x_3651_);
v___x_3653_ = 0;
v___x_3654_ = lean_box(v___x_3586_);
v___x_3655_ = lean_box(v_useSplitter_3594_);
v___x_3656_ = lean_box(v___x_3653_);
lean_inc_ref(v_aux1_3645_);
lean_inc(v_restoreM_3640_);
lean_inc(v_liftWith_3639_);
lean_inc(v_inst_3587_);
lean_inc_n(v_toBind_3582_, 2);
v___f_3657_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__52___boxed), 37, 36);
lean_closure_set(v___f_3657_, 0, v_alts_3584_);
lean_closure_set(v___f_3657_, 1, v_toPure_3579_);
lean_closure_set(v___f_3657_, 2, v_toBind_3582_);
lean_closure_set(v___f_3657_, 3, v___f_3596_);
lean_closure_set(v___f_3657_, 4, v___x_3593_);
lean_closure_set(v___f_3657_, 5, v_inst_3590_);
lean_closure_set(v___f_3657_, 6, v_inst_3587_);
lean_closure_set(v___f_3657_, 7, v_inst_3597_);
lean_closure_set(v___f_3657_, 8, v___x_3654_);
lean_closure_set(v___f_3657_, 9, v___x_3655_);
lean_closure_set(v___f_3657_, 10, v_onAlt_3589_);
lean_closure_set(v___f_3657_, 11, v___f_3598_);
lean_closure_set(v___f_3657_, 12, v_fst_3606_);
lean_closure_set(v___f_3657_, 13, v_inst_3583_);
lean_closure_set(v___f_3657_, 14, v_numDiscrEqs_3599_);
lean_closure_set(v___f_3657_, 15, v___x_3641_);
lean_closure_set(v___f_3657_, 16, v_params_x27_3576_);
lean_closure_set(v___f_3657_, 17, v_fst_3577_);
lean_closure_set(v___f_3657_, 18, v_discrs_x27_3578_);
lean_closure_set(v___f_3657_, 19, v_fst_3602_);
lean_closure_set(v___f_3657_, 20, v_numParams_3568_);
lean_closure_set(v___f_3657_, 21, v_numDiscrs_3569_);
lean_closure_set(v___f_3657_, 22, v_altInfos_3570_);
lean_closure_set(v___f_3657_, 23, v_uElimPos_x3f_3571_);
lean_closure_set(v___f_3657_, 24, v_snd_3572_);
lean_closure_set(v___f_3657_, 25, v_overlaps_3573_);
lean_closure_set(v___f_3657_, 26, v_matcherLevels_3575_);
lean_closure_set(v___f_3657_, 27, v_onRemaining_3580_);
lean_closure_set(v___f_3657_, 28, v_remaining_3581_);
lean_closure_set(v___f_3657_, 29, v_remaining_x27_3588_);
lean_closure_set(v___f_3657_, 30, v___x_3650_);
lean_closure_set(v___f_3657_, 31, v___x_3656_);
lean_closure_set(v___f_3657_, 32, v_liftWith_3639_);
lean_closure_set(v___f_3657_, 33, v_restoreM_3640_);
lean_closure_set(v___f_3657_, 34, v_matcherName_3574_);
lean_closure_set(v___f_3657_, 35, v_aux1_3645_);
v___x_3658_ = lean_box(v___x_3653_);
v___x_3659_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3659_, 0, v_aux1_3645_);
lean_closure_set(v___x_3659_, 1, v___x_3658_);
v___x_3660_ = lean_apply_2(v_inst_3587_, lean_box(0), v___x_3659_);
v___f_3661_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3661_, 0, v___x_3660_);
lean_closure_set(v___f_3661_, 1, v___f_3652_);
v___x_3662_ = lean_apply_2(v_liftWith_3639_, lean_box(0), v___f_3661_);
v___x_3663_ = lean_apply_1(v_restoreM_3640_, lean_box(0));
v___x_3664_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3662_, v___x_3663_);
v___x_3665_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3664_, v___f_3657_);
return v___x_3665_;
}
}
}
v___jp_3611_:
{
lean_object* v_liftWith_3612_; lean_object* v_restoreM_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v_aux_3616_; lean_object* v_aux_3617_; lean_object* v_aux_3618_; lean_object* v___x_3619_; uint8_t v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___f_3623_; lean_object* v___x_3624_; lean_object* v___x_3626_; 
v_liftWith_3612_ = lean_ctor_get(v_inst_3583_, 0);
lean_inc(v_liftWith_3612_);
v_restoreM_3613_ = lean_ctor_get(v_inst_3583_, 1);
lean_inc(v_restoreM_3613_);
v___x_3614_ = lean_array_to_list(v_matcherLevels_3575_);
v___x_3615_ = l_Lean_mkConst(v_matcherName_3574_, v___x_3614_);
v_aux_3616_ = l_Lean_mkAppN(v___x_3615_, v_params_x27_3576_);
lean_dec_ref(v_params_x27_3576_);
v_aux_3617_ = l_Lean_Expr_app___override(v_aux_3616_, v_fst_3577_);
v_aux_3618_ = l_Lean_mkAppN(v_aux_3617_, v_discrs_x27_3578_);
lean_dec_ref(v_discrs_x27_3578_);
lean_inc_ref_n(v_aux_3618_, 2);
v___x_3619_ = l_Lean_indentExpr(v_aux_3618_);
v___x_3620_ = 1;
v___x_3621_ = lean_box(v___x_3586_);
v___x_3622_ = lean_box(v___x_3620_);
lean_inc(v_inst_3587_);
lean_inc(v_toBind_3582_);
v___f_3623_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_3623_, 0, v_alts_3584_);
lean_closure_set(v___f_3623_, 1, v_toPure_3579_);
lean_closure_set(v___f_3623_, 2, v_toBind_3582_);
lean_closure_set(v___f_3623_, 3, v___f_3585_);
lean_closure_set(v___f_3623_, 4, v___x_3621_);
lean_closure_set(v___f_3623_, 5, v___x_3622_);
lean_closure_set(v___f_3623_, 6, v_inst_3587_);
lean_closure_set(v___f_3623_, 7, v_remaining_x27_3588_);
lean_closure_set(v___f_3623_, 8, v_onAlt_3589_);
lean_closure_set(v___f_3623_, 9, v_inst_3583_);
lean_closure_set(v___f_3623_, 10, v_inst_3590_);
lean_closure_set(v___f_3623_, 11, v___f_3591_);
lean_closure_set(v___f_3623_, 12, v_fst_3606_);
lean_closure_set(v___f_3623_, 13, v_matcherApp_3592_);
lean_closure_set(v___f_3623_, 14, v___x_3593_);
lean_closure_set(v___f_3623_, 15, v___f_3610_);
lean_closure_set(v___f_3623_, 16, v_aux_3618_);
v___x_3624_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
if (v_isShared_3609_ == 0)
{
lean_ctor_set_tag(v___x_3608_, 7);
lean_ctor_set(v___x_3608_, 1, v___x_3619_);
lean_ctor_set(v___x_3608_, 0, v___x_3624_);
v___x_3626_ = v___x_3608_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3624_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v___x_3619_);
v___x_3626_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___f_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___f_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___f_3627_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_3627_, 0, v___x_3626_);
v___x_3628_ = 0;
v___x_3629_ = lean_box(v___x_3628_);
v___x_3630_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_3630_, 0, v_aux_3618_);
lean_closure_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_apply_2(v_inst_3587_, lean_box(0), v___x_3630_);
v___f_3632_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__33___boxed), 8, 2);
lean_closure_set(v___f_3632_, 0, v___x_3631_);
lean_closure_set(v___f_3632_, 1, v___f_3627_);
v___x_3633_ = lean_apply_2(v_liftWith_3612_, lean_box(0), v___f_3632_);
v___x_3634_ = lean_apply_1(v_restoreM_3613_, lean_box(0));
lean_inc(v_toBind_3582_);
v___x_3635_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3633_, v___x_3634_);
v___x_3636_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3635_, v___f_3623_);
return v___x_3636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed(lean_object** _args){
lean_object* v_numParams_3670_ = _args[0];
lean_object* v_numDiscrs_3671_ = _args[1];
lean_object* v_altInfos_3672_ = _args[2];
lean_object* v_uElimPos_x3f_3673_ = _args[3];
lean_object* v_snd_3674_ = _args[4];
lean_object* v_overlaps_3675_ = _args[5];
lean_object* v_matcherName_3676_ = _args[6];
lean_object* v_matcherLevels_3677_ = _args[7];
lean_object* v_params_x27_3678_ = _args[8];
lean_object* v_fst_3679_ = _args[9];
lean_object* v_discrs_x27_3680_ = _args[10];
lean_object* v_toPure_3681_ = _args[11];
lean_object* v_onRemaining_3682_ = _args[12];
lean_object* v_remaining_3683_ = _args[13];
lean_object* v_toBind_3684_ = _args[14];
lean_object* v_inst_3685_ = _args[15];
lean_object* v_alts_3686_ = _args[16];
lean_object* v___f_3687_ = _args[17];
lean_object* v___x_3688_ = _args[18];
lean_object* v_inst_3689_ = _args[19];
lean_object* v_remaining_x27_3690_ = _args[20];
lean_object* v_onAlt_3691_ = _args[21];
lean_object* v_inst_3692_ = _args[22];
lean_object* v___f_3693_ = _args[23];
lean_object* v_matcherApp_3694_ = _args[24];
lean_object* v___x_3695_ = _args[25];
lean_object* v_useSplitter_3696_ = _args[26];
lean_object* v_isCasesOn_3697_ = _args[27];
lean_object* v___f_3698_ = _args[28];
lean_object* v_inst_3699_ = _args[29];
lean_object* v___f_3700_ = _args[30];
lean_object* v_numDiscrEqs_3701_ = _args[31];
lean_object* v_____s_3702_ = _args[32];
_start:
{
uint8_t v___x_16219__boxed_3703_; uint8_t v_useSplitter_boxed_3704_; uint8_t v_isCasesOn_boxed_3705_; lean_object* v_res_3706_; 
v___x_16219__boxed_3703_ = lean_unbox(v___x_3688_);
v_useSplitter_boxed_3704_ = lean_unbox(v_useSplitter_3696_);
v_isCasesOn_boxed_3705_ = lean_unbox(v_isCasesOn_3697_);
v_res_3706_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__55(v_numParams_3670_, v_numDiscrs_3671_, v_altInfos_3672_, v_uElimPos_x3f_3673_, v_snd_3674_, v_overlaps_3675_, v_matcherName_3676_, v_matcherLevels_3677_, v_params_x27_3678_, v_fst_3679_, v_discrs_x27_3680_, v_toPure_3681_, v_onRemaining_3682_, v_remaining_3683_, v_toBind_3684_, v_inst_3685_, v_alts_3686_, v___f_3687_, v___x_16219__boxed_3703_, v_inst_3689_, v_remaining_x27_3690_, v_onAlt_3691_, v_inst_3692_, v___f_3693_, v_matcherApp_3694_, v___x_3695_, v_useSplitter_boxed_3704_, v_isCasesOn_boxed_3705_, v___f_3698_, v_inst_3699_, v___f_3700_, v_numDiscrEqs_3701_, v_____s_3702_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54(lean_object* v_numParams_3707_, lean_object* v_numDiscrs_3708_, lean_object* v_altInfos_3709_, lean_object* v_uElimPos_x3f_3710_, lean_object* v_snd_3711_, lean_object* v_overlaps_3712_, lean_object* v_matcherName_3713_, lean_object* v_params_x27_3714_, lean_object* v_fst_3715_, lean_object* v_discrs_x27_3716_, lean_object* v_toPure_3717_, lean_object* v_onRemaining_3718_, lean_object* v_remaining_3719_, lean_object* v_toBind_3720_, lean_object* v_inst_3721_, lean_object* v_alts_3722_, lean_object* v___f_3723_, uint8_t v___x_3724_, lean_object* v_inst_3725_, lean_object* v_onAlt_3726_, lean_object* v_inst_3727_, lean_object* v___f_3728_, lean_object* v_matcherApp_3729_, uint8_t v_useSplitter_3730_, uint8_t v_isCasesOn_3731_, lean_object* v___f_3732_, lean_object* v_inst_3733_, lean_object* v___f_3734_, lean_object* v_numDiscrEqs_3735_, lean_object* v_fst_3736_, lean_object* v___f_3737_, lean_object* v_matcherLevels_3738_){
_start:
{
lean_object* v___x_3739_; lean_object* v_remaining_x27_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___f_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; size_t v_sz_3751_; size_t v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3739_ = lean_unsigned_to_nat(0u);
v_remaining_x27_3740_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_3741_ = lean_box(v___x_3724_);
v___x_3742_ = lean_box(v_useSplitter_3730_);
v___x_3743_ = lean_box(v_isCasesOn_3731_);
lean_inc_ref(v_inst_3727_);
lean_inc(v_toBind_3720_);
lean_inc_ref(v_discrs_x27_3716_);
v___f_3744_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__55___boxed), 33, 32);
lean_closure_set(v___f_3744_, 0, v_numParams_3707_);
lean_closure_set(v___f_3744_, 1, v_numDiscrs_3708_);
lean_closure_set(v___f_3744_, 2, v_altInfos_3709_);
lean_closure_set(v___f_3744_, 3, v_uElimPos_x3f_3710_);
lean_closure_set(v___f_3744_, 4, v_snd_3711_);
lean_closure_set(v___f_3744_, 5, v_overlaps_3712_);
lean_closure_set(v___f_3744_, 6, v_matcherName_3713_);
lean_closure_set(v___f_3744_, 7, v_matcherLevels_3738_);
lean_closure_set(v___f_3744_, 8, v_params_x27_3714_);
lean_closure_set(v___f_3744_, 9, v_fst_3715_);
lean_closure_set(v___f_3744_, 10, v_discrs_x27_3716_);
lean_closure_set(v___f_3744_, 11, v_toPure_3717_);
lean_closure_set(v___f_3744_, 12, v_onRemaining_3718_);
lean_closure_set(v___f_3744_, 13, v_remaining_3719_);
lean_closure_set(v___f_3744_, 14, v_toBind_3720_);
lean_closure_set(v___f_3744_, 15, v_inst_3721_);
lean_closure_set(v___f_3744_, 16, v_alts_3722_);
lean_closure_set(v___f_3744_, 17, v___f_3723_);
lean_closure_set(v___f_3744_, 18, v___x_3741_);
lean_closure_set(v___f_3744_, 19, v_inst_3725_);
lean_closure_set(v___f_3744_, 20, v_remaining_x27_3740_);
lean_closure_set(v___f_3744_, 21, v_onAlt_3726_);
lean_closure_set(v___f_3744_, 22, v_inst_3727_);
lean_closure_set(v___f_3744_, 23, v___f_3728_);
lean_closure_set(v___f_3744_, 24, v_matcherApp_3729_);
lean_closure_set(v___f_3744_, 25, v___x_3739_);
lean_closure_set(v___f_3744_, 26, v___x_3742_);
lean_closure_set(v___f_3744_, 27, v___x_3743_);
lean_closure_set(v___f_3744_, 28, v___f_3732_);
lean_closure_set(v___f_3744_, 29, v_inst_3733_);
lean_closure_set(v___f_3744_, 30, v___f_3734_);
lean_closure_set(v___f_3744_, 31, v_numDiscrEqs_3735_);
v___x_3745_ = l_Array_reverse___redArg(v_fst_3736_);
v___x_3746_ = lean_array_get_size(v___x_3745_);
v___x_3747_ = l_Array_toSubarray___redArg(v___x_3745_, v___x_3739_, v___x_3746_);
v___x_3748_ = l_Array_reverse___redArg(v_discrs_x27_3716_);
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3739_);
lean_ctor_set(v___x_3749_, 1, v___x_3747_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v_remaining_x27_3740_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v_sz_3751_ = lean_array_size(v___x_3748_);
v___x_3752_ = ((size_t)0ULL);
v___x_3753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_3727_, v___x_3748_, v___f_3737_, v_sz_3751_, v___x_3752_, v___x_3750_);
v___x_3754_ = lean_apply_4(v_toBind_3720_, lean_box(0), lean_box(0), v___x_3753_, v___f_3744_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed(lean_object** _args){
lean_object* v_numParams_3755_ = _args[0];
lean_object* v_numDiscrs_3756_ = _args[1];
lean_object* v_altInfos_3757_ = _args[2];
lean_object* v_uElimPos_x3f_3758_ = _args[3];
lean_object* v_snd_3759_ = _args[4];
lean_object* v_overlaps_3760_ = _args[5];
lean_object* v_matcherName_3761_ = _args[6];
lean_object* v_params_x27_3762_ = _args[7];
lean_object* v_fst_3763_ = _args[8];
lean_object* v_discrs_x27_3764_ = _args[9];
lean_object* v_toPure_3765_ = _args[10];
lean_object* v_onRemaining_3766_ = _args[11];
lean_object* v_remaining_3767_ = _args[12];
lean_object* v_toBind_3768_ = _args[13];
lean_object* v_inst_3769_ = _args[14];
lean_object* v_alts_3770_ = _args[15];
lean_object* v___f_3771_ = _args[16];
lean_object* v___x_3772_ = _args[17];
lean_object* v_inst_3773_ = _args[18];
lean_object* v_onAlt_3774_ = _args[19];
lean_object* v_inst_3775_ = _args[20];
lean_object* v___f_3776_ = _args[21];
lean_object* v_matcherApp_3777_ = _args[22];
lean_object* v_useSplitter_3778_ = _args[23];
lean_object* v_isCasesOn_3779_ = _args[24];
lean_object* v___f_3780_ = _args[25];
lean_object* v_inst_3781_ = _args[26];
lean_object* v___f_3782_ = _args[27];
lean_object* v_numDiscrEqs_3783_ = _args[28];
lean_object* v_fst_3784_ = _args[29];
lean_object* v___f_3785_ = _args[30];
lean_object* v_matcherLevels_3786_ = _args[31];
_start:
{
uint8_t v___x_16380__boxed_3787_; uint8_t v_useSplitter_boxed_3788_; uint8_t v_isCasesOn_boxed_3789_; lean_object* v_res_3790_; 
v___x_16380__boxed_3787_ = lean_unbox(v___x_3772_);
v_useSplitter_boxed_3788_ = lean_unbox(v_useSplitter_3778_);
v_isCasesOn_boxed_3789_ = lean_unbox(v_isCasesOn_3779_);
v_res_3790_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__54(v_numParams_3755_, v_numDiscrs_3756_, v_altInfos_3757_, v_uElimPos_x3f_3758_, v_snd_3759_, v_overlaps_3760_, v_matcherName_3761_, v_params_x27_3762_, v_fst_3763_, v_discrs_x27_3764_, v_toPure_3765_, v_onRemaining_3766_, v_remaining_3767_, v_toBind_3768_, v_inst_3769_, v_alts_3770_, v___f_3771_, v___x_16380__boxed_3787_, v_inst_3773_, v_onAlt_3774_, v_inst_3775_, v___f_3776_, v_matcherApp_3777_, v_useSplitter_boxed_3788_, v_isCasesOn_boxed_3789_, v___f_3780_, v_inst_3781_, v___f_3782_, v_numDiscrEqs_3783_, v_fst_3784_, v___f_3785_, v_matcherLevels_3786_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__56(lean_object* v___f_3791_, lean_object* v_matcherLevels_3792_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_apply_1(v___f_3791_, v_matcherLevels_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58(lean_object* v_toMatcherInfo_3794_, lean_object* v_matcherName_3795_, lean_object* v_params_x27_3796_, lean_object* v_discrs_x27_3797_, lean_object* v_toPure_3798_, lean_object* v_onRemaining_3799_, lean_object* v_remaining_3800_, lean_object* v_toBind_3801_, lean_object* v_inst_3802_, lean_object* v_alts_3803_, lean_object* v___f_3804_, uint8_t v___x_3805_, lean_object* v_inst_3806_, lean_object* v_onAlt_3807_, lean_object* v_inst_3808_, lean_object* v___f_3809_, lean_object* v_matcherApp_3810_, uint8_t v_useSplitter_3811_, uint8_t v_isCasesOn_3812_, lean_object* v___f_3813_, lean_object* v_inst_3814_, lean_object* v___f_3815_, lean_object* v_numDiscrEqs_3816_, lean_object* v___f_3817_, lean_object* v_matcherLevels_3818_, lean_object* v_____x_3819_){
_start:
{
lean_object* v_snd_3820_; lean_object* v_snd_3821_; lean_object* v_fst_3822_; lean_object* v_fst_3823_; lean_object* v_fst_3824_; lean_object* v_snd_3825_; lean_object* v_numParams_3826_; lean_object* v_numDiscrs_3827_; lean_object* v_altInfos_3828_; lean_object* v_uElimPos_x3f_3829_; lean_object* v_overlaps_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___f_3834_; 
v_snd_3820_ = lean_ctor_get(v_____x_3819_, 1);
lean_inc(v_snd_3820_);
v_snd_3821_ = lean_ctor_get(v_snd_3820_, 1);
lean_inc(v_snd_3821_);
v_fst_3822_ = lean_ctor_get(v_____x_3819_, 0);
lean_inc(v_fst_3822_);
lean_dec_ref(v_____x_3819_);
v_fst_3823_ = lean_ctor_get(v_snd_3820_, 0);
lean_inc(v_fst_3823_);
lean_dec(v_snd_3820_);
v_fst_3824_ = lean_ctor_get(v_snd_3821_, 0);
lean_inc(v_fst_3824_);
v_snd_3825_ = lean_ctor_get(v_snd_3821_, 1);
lean_inc(v_snd_3825_);
lean_dec(v_snd_3821_);
v_numParams_3826_ = lean_ctor_get(v_toMatcherInfo_3794_, 0);
lean_inc(v_numParams_3826_);
v_numDiscrs_3827_ = lean_ctor_get(v_toMatcherInfo_3794_, 1);
lean_inc(v_numDiscrs_3827_);
v_altInfos_3828_ = lean_ctor_get(v_toMatcherInfo_3794_, 2);
lean_inc_ref(v_altInfos_3828_);
v_uElimPos_x3f_3829_ = lean_ctor_get(v_toMatcherInfo_3794_, 3);
lean_inc_n(v_uElimPos_x3f_3829_, 2);
v_overlaps_3830_ = lean_ctor_get(v_toMatcherInfo_3794_, 5);
lean_inc_ref(v_overlaps_3830_);
lean_dec_ref(v_toMatcherInfo_3794_);
v___x_3831_ = lean_box(v___x_3805_);
v___x_3832_ = lean_box(v_useSplitter_3811_);
v___x_3833_ = lean_box(v_isCasesOn_3812_);
lean_inc(v_toBind_3801_);
lean_inc(v_toPure_3798_);
v___f_3834_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__54___boxed), 32, 31);
lean_closure_set(v___f_3834_, 0, v_numParams_3826_);
lean_closure_set(v___f_3834_, 1, v_numDiscrs_3827_);
lean_closure_set(v___f_3834_, 2, v_altInfos_3828_);
lean_closure_set(v___f_3834_, 3, v_uElimPos_x3f_3829_);
lean_closure_set(v___f_3834_, 4, v_snd_3825_);
lean_closure_set(v___f_3834_, 5, v_overlaps_3830_);
lean_closure_set(v___f_3834_, 6, v_matcherName_3795_);
lean_closure_set(v___f_3834_, 7, v_params_x27_3796_);
lean_closure_set(v___f_3834_, 8, v_fst_3822_);
lean_closure_set(v___f_3834_, 9, v_discrs_x27_3797_);
lean_closure_set(v___f_3834_, 10, v_toPure_3798_);
lean_closure_set(v___f_3834_, 11, v_onRemaining_3799_);
lean_closure_set(v___f_3834_, 12, v_remaining_3800_);
lean_closure_set(v___f_3834_, 13, v_toBind_3801_);
lean_closure_set(v___f_3834_, 14, v_inst_3802_);
lean_closure_set(v___f_3834_, 15, v_alts_3803_);
lean_closure_set(v___f_3834_, 16, v___f_3804_);
lean_closure_set(v___f_3834_, 17, v___x_3831_);
lean_closure_set(v___f_3834_, 18, v_inst_3806_);
lean_closure_set(v___f_3834_, 19, v_onAlt_3807_);
lean_closure_set(v___f_3834_, 20, v_inst_3808_);
lean_closure_set(v___f_3834_, 21, v___f_3809_);
lean_closure_set(v___f_3834_, 22, v_matcherApp_3810_);
lean_closure_set(v___f_3834_, 23, v___x_3832_);
lean_closure_set(v___f_3834_, 24, v___x_3833_);
lean_closure_set(v___f_3834_, 25, v___f_3813_);
lean_closure_set(v___f_3834_, 26, v_inst_3814_);
lean_closure_set(v___f_3834_, 27, v___f_3815_);
lean_closure_set(v___f_3834_, 28, v_numDiscrEqs_3816_);
lean_closure_set(v___f_3834_, 29, v_fst_3824_);
lean_closure_set(v___f_3834_, 30, v___f_3817_);
if (lean_obj_tag(v_uElimPos_x3f_3829_) == 0)
{
lean_object* v___f_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_dec(v_fst_3823_);
v___f_3835_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3835_, 0, v___f_3834_);
v___x_3836_ = lean_apply_2(v_toPure_3798_, lean_box(0), v_matcherLevels_3818_);
v___x_3837_ = lean_apply_4(v_toBind_3801_, lean_box(0), lean_box(0), v___x_3836_, v___f_3835_);
return v___x_3837_;
}
else
{
lean_object* v_val_3838_; lean_object* v___f_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_val_3838_ = lean_ctor_get(v_uElimPos_x3f_3829_, 0);
lean_inc(v_val_3838_);
lean_dec_ref_known(v_uElimPos_x3f_3829_, 1);
v___f_3839_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__56), 2, 1);
lean_closure_set(v___f_3839_, 0, v___f_3834_);
v___x_3840_ = lean_array_set(v_matcherLevels_3818_, v_val_3838_, v_fst_3823_);
lean_dec(v_val_3838_);
v___x_3841_ = lean_apply_2(v_toPure_3798_, lean_box(0), v___x_3840_);
v___x_3842_ = lean_apply_4(v_toBind_3801_, lean_box(0), lean_box(0), v___x_3841_, v___f_3839_);
return v___x_3842_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_3843_ = _args[0];
lean_object* v_matcherName_3844_ = _args[1];
lean_object* v_params_x27_3845_ = _args[2];
lean_object* v_discrs_x27_3846_ = _args[3];
lean_object* v_toPure_3847_ = _args[4];
lean_object* v_onRemaining_3848_ = _args[5];
lean_object* v_remaining_3849_ = _args[6];
lean_object* v_toBind_3850_ = _args[7];
lean_object* v_inst_3851_ = _args[8];
lean_object* v_alts_3852_ = _args[9];
lean_object* v___f_3853_ = _args[10];
lean_object* v___x_3854_ = _args[11];
lean_object* v_inst_3855_ = _args[12];
lean_object* v_onAlt_3856_ = _args[13];
lean_object* v_inst_3857_ = _args[14];
lean_object* v___f_3858_ = _args[15];
lean_object* v_matcherApp_3859_ = _args[16];
lean_object* v_useSplitter_3860_ = _args[17];
lean_object* v_isCasesOn_3861_ = _args[18];
lean_object* v___f_3862_ = _args[19];
lean_object* v_inst_3863_ = _args[20];
lean_object* v___f_3864_ = _args[21];
lean_object* v_numDiscrEqs_3865_ = _args[22];
lean_object* v___f_3866_ = _args[23];
lean_object* v_matcherLevels_3867_ = _args[24];
lean_object* v_____x_3868_ = _args[25];
_start:
{
uint8_t v___x_16449__boxed_3869_; uint8_t v_useSplitter_boxed_3870_; uint8_t v_isCasesOn_boxed_3871_; lean_object* v_res_3872_; 
v___x_16449__boxed_3869_ = lean_unbox(v___x_3854_);
v_useSplitter_boxed_3870_ = lean_unbox(v_useSplitter_3860_);
v_isCasesOn_boxed_3871_ = lean_unbox(v_isCasesOn_3861_);
v_res_3872_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__58(v_toMatcherInfo_3843_, v_matcherName_3844_, v_params_x27_3845_, v_discrs_x27_3846_, v_toPure_3847_, v_onRemaining_3848_, v_remaining_3849_, v_toBind_3850_, v_inst_3851_, v_alts_3852_, v___f_3853_, v___x_16449__boxed_3869_, v_inst_3855_, v_onAlt_3856_, v_inst_3857_, v___f_3858_, v_matcherApp_3859_, v_useSplitter_boxed_3870_, v_isCasesOn_boxed_3871_, v___f_3862_, v_inst_3863_, v___f_3864_, v_numDiscrEqs_3865_, v___f_3866_, v_matcherLevels_3867_, v_____x_3868_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57(lean_object* v_toPure_3873_, lean_object* v_inst_3874_, lean_object* v_toBind_3875_, lean_object* v_toMatcherInfo_3876_, lean_object* v_inst_3877_, lean_object* v___f_3878_, lean_object* v_onMotive_3879_, lean_object* v_discrs_3880_, lean_object* v_inst_3881_, lean_object* v_matcherName_3882_, lean_object* v_params_x27_3883_, lean_object* v_onRemaining_3884_, lean_object* v_remaining_3885_, lean_object* v_inst_3886_, lean_object* v_alts_3887_, lean_object* v___f_3888_, lean_object* v_onAlt_3889_, lean_object* v___f_3890_, lean_object* v_matcherApp_3891_, uint8_t v_useSplitter_3892_, uint8_t v_isCasesOn_3893_, lean_object* v___f_3894_, lean_object* v___f_3895_, lean_object* v_numDiscrEqs_3896_, lean_object* v___f_3897_, lean_object* v_matcherLevels_3898_, lean_object* v_motive_3899_, lean_object* v_discrs_x27_3900_){
_start:
{
lean_object* v___f_3901_; uint8_t v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___f_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_inc_ref(v_inst_3881_);
lean_inc_ref_n(v_inst_3877_, 2);
lean_inc_ref(v_discrs_x27_3900_);
lean_inc_ref(v_toMatcherInfo_3876_);
lean_inc_n(v_toBind_3875_, 2);
lean_inc(v_inst_3874_);
lean_inc(v_toPure_3873_);
v___f_3901_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__19___boxed), 12, 10);
lean_closure_set(v___f_3901_, 0, v_toPure_3873_);
lean_closure_set(v___f_3901_, 1, v_inst_3874_);
lean_closure_set(v___f_3901_, 2, v_toBind_3875_);
lean_closure_set(v___f_3901_, 3, v_toMatcherInfo_3876_);
lean_closure_set(v___f_3901_, 4, v_discrs_x27_3900_);
lean_closure_set(v___f_3901_, 5, v_inst_3877_);
lean_closure_set(v___f_3901_, 6, v___f_3878_);
lean_closure_set(v___f_3901_, 7, v_onMotive_3879_);
lean_closure_set(v___f_3901_, 8, v_discrs_3880_);
lean_closure_set(v___f_3901_, 9, v_inst_3881_);
v___x_3902_ = 0;
v___x_3903_ = lean_box(v___x_3902_);
v___x_3904_ = lean_box(v_useSplitter_3892_);
v___x_3905_ = lean_box(v_isCasesOn_3893_);
lean_inc_ref(v_inst_3886_);
v___f_3906_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__58___boxed), 26, 25);
lean_closure_set(v___f_3906_, 0, v_toMatcherInfo_3876_);
lean_closure_set(v___f_3906_, 1, v_matcherName_3882_);
lean_closure_set(v___f_3906_, 2, v_params_x27_3883_);
lean_closure_set(v___f_3906_, 3, v_discrs_x27_3900_);
lean_closure_set(v___f_3906_, 4, v_toPure_3873_);
lean_closure_set(v___f_3906_, 5, v_onRemaining_3884_);
lean_closure_set(v___f_3906_, 6, v_remaining_3885_);
lean_closure_set(v___f_3906_, 7, v_toBind_3875_);
lean_closure_set(v___f_3906_, 8, v_inst_3886_);
lean_closure_set(v___f_3906_, 9, v_alts_3887_);
lean_closure_set(v___f_3906_, 10, v___f_3888_);
lean_closure_set(v___f_3906_, 11, v___x_3903_);
lean_closure_set(v___f_3906_, 12, v_inst_3874_);
lean_closure_set(v___f_3906_, 13, v_onAlt_3889_);
lean_closure_set(v___f_3906_, 14, v_inst_3877_);
lean_closure_set(v___f_3906_, 15, v___f_3890_);
lean_closure_set(v___f_3906_, 16, v_matcherApp_3891_);
lean_closure_set(v___f_3906_, 17, v___x_3904_);
lean_closure_set(v___f_3906_, 18, v___x_3905_);
lean_closure_set(v___f_3906_, 19, v___f_3894_);
lean_closure_set(v___f_3906_, 20, v_inst_3881_);
lean_closure_set(v___f_3906_, 21, v___f_3895_);
lean_closure_set(v___f_3906_, 22, v_numDiscrEqs_3896_);
lean_closure_set(v___f_3906_, 23, v___f_3897_);
lean_closure_set(v___f_3906_, 24, v_matcherLevels_3898_);
v___x_3907_ = l_Lean_Meta_lambdaTelescope___redArg(v_inst_3886_, v_inst_3877_, v_motive_3899_, v___f_3901_, v___x_3902_);
v___x_3908_ = lean_apply_4(v_toBind_3875_, lean_box(0), lean_box(0), v___x_3907_, v___f_3906_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed(lean_object** _args){
lean_object* v_toPure_3909_ = _args[0];
lean_object* v_inst_3910_ = _args[1];
lean_object* v_toBind_3911_ = _args[2];
lean_object* v_toMatcherInfo_3912_ = _args[3];
lean_object* v_inst_3913_ = _args[4];
lean_object* v___f_3914_ = _args[5];
lean_object* v_onMotive_3915_ = _args[6];
lean_object* v_discrs_3916_ = _args[7];
lean_object* v_inst_3917_ = _args[8];
lean_object* v_matcherName_3918_ = _args[9];
lean_object* v_params_x27_3919_ = _args[10];
lean_object* v_onRemaining_3920_ = _args[11];
lean_object* v_remaining_3921_ = _args[12];
lean_object* v_inst_3922_ = _args[13];
lean_object* v_alts_3923_ = _args[14];
lean_object* v___f_3924_ = _args[15];
lean_object* v_onAlt_3925_ = _args[16];
lean_object* v___f_3926_ = _args[17];
lean_object* v_matcherApp_3927_ = _args[18];
lean_object* v_useSplitter_3928_ = _args[19];
lean_object* v_isCasesOn_3929_ = _args[20];
lean_object* v___f_3930_ = _args[21];
lean_object* v___f_3931_ = _args[22];
lean_object* v_numDiscrEqs_3932_ = _args[23];
lean_object* v___f_3933_ = _args[24];
lean_object* v_matcherLevels_3934_ = _args[25];
lean_object* v_motive_3935_ = _args[26];
lean_object* v_discrs_x27_3936_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_3937_; uint8_t v_isCasesOn_boxed_3938_; lean_object* v_res_3939_; 
v_useSplitter_boxed_3937_ = lean_unbox(v_useSplitter_3928_);
v_isCasesOn_boxed_3938_ = lean_unbox(v_isCasesOn_3929_);
v_res_3939_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__57(v_toPure_3909_, v_inst_3910_, v_toBind_3911_, v_toMatcherInfo_3912_, v_inst_3913_, v___f_3914_, v_onMotive_3915_, v_discrs_3916_, v_inst_3917_, v_matcherName_3918_, v_params_x27_3919_, v_onRemaining_3920_, v_remaining_3921_, v_inst_3922_, v_alts_3923_, v___f_3924_, v_onAlt_3925_, v___f_3926_, v_matcherApp_3927_, v_useSplitter_boxed_3937_, v_isCasesOn_boxed_3938_, v___f_3930_, v___f_3931_, v_numDiscrEqs_3932_, v___f_3933_, v_matcherLevels_3934_, v_motive_3935_, v_discrs_x27_3936_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59(lean_object* v_toPure_3940_, lean_object* v_inst_3941_, lean_object* v_toBind_3942_, lean_object* v_toMatcherInfo_3943_, lean_object* v_inst_3944_, lean_object* v___f_3945_, lean_object* v_onMotive_3946_, lean_object* v_discrs_3947_, lean_object* v_inst_3948_, lean_object* v_matcherName_3949_, lean_object* v_onRemaining_3950_, lean_object* v_remaining_3951_, lean_object* v_inst_3952_, lean_object* v_alts_3953_, lean_object* v___f_3954_, lean_object* v_onAlt_3955_, lean_object* v___f_3956_, lean_object* v_matcherApp_3957_, uint8_t v_useSplitter_3958_, uint8_t v_isCasesOn_3959_, lean_object* v___f_3960_, lean_object* v___f_3961_, lean_object* v_numDiscrEqs_3962_, lean_object* v___f_3963_, lean_object* v_matcherLevels_3964_, lean_object* v_motive_3965_, lean_object* v_onParams_3966_, lean_object* v_params_x27_3967_){
_start:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___f_3970_; size_t v_sz_3971_; size_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3968_ = lean_box(v_useSplitter_3958_);
v___x_3969_ = lean_box(v_isCasesOn_3959_);
lean_inc_ref(v_discrs_3947_);
lean_inc_ref(v_inst_3944_);
lean_inc(v_toBind_3942_);
v___f_3970_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__57___boxed), 28, 27);
lean_closure_set(v___f_3970_, 0, v_toPure_3940_);
lean_closure_set(v___f_3970_, 1, v_inst_3941_);
lean_closure_set(v___f_3970_, 2, v_toBind_3942_);
lean_closure_set(v___f_3970_, 3, v_toMatcherInfo_3943_);
lean_closure_set(v___f_3970_, 4, v_inst_3944_);
lean_closure_set(v___f_3970_, 5, v___f_3945_);
lean_closure_set(v___f_3970_, 6, v_onMotive_3946_);
lean_closure_set(v___f_3970_, 7, v_discrs_3947_);
lean_closure_set(v___f_3970_, 8, v_inst_3948_);
lean_closure_set(v___f_3970_, 9, v_matcherName_3949_);
lean_closure_set(v___f_3970_, 10, v_params_x27_3967_);
lean_closure_set(v___f_3970_, 11, v_onRemaining_3950_);
lean_closure_set(v___f_3970_, 12, v_remaining_3951_);
lean_closure_set(v___f_3970_, 13, v_inst_3952_);
lean_closure_set(v___f_3970_, 14, v_alts_3953_);
lean_closure_set(v___f_3970_, 15, v___f_3954_);
lean_closure_set(v___f_3970_, 16, v_onAlt_3955_);
lean_closure_set(v___f_3970_, 17, v___f_3956_);
lean_closure_set(v___f_3970_, 18, v_matcherApp_3957_);
lean_closure_set(v___f_3970_, 19, v___x_3968_);
lean_closure_set(v___f_3970_, 20, v___x_3969_);
lean_closure_set(v___f_3970_, 21, v___f_3960_);
lean_closure_set(v___f_3970_, 22, v___f_3961_);
lean_closure_set(v___f_3970_, 23, v_numDiscrEqs_3962_);
lean_closure_set(v___f_3970_, 24, v___f_3963_);
lean_closure_set(v___f_3970_, 25, v_matcherLevels_3964_);
lean_closure_set(v___f_3970_, 26, v_motive_3965_);
v_sz_3971_ = lean_array_size(v_discrs_3947_);
v___x_3972_ = ((size_t)0ULL);
v___x_3973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_3944_, v_onParams_3966_, v_sz_3971_, v___x_3972_, v_discrs_3947_);
v___x_3974_ = lean_apply_4(v_toBind_3942_, lean_box(0), lean_box(0), v___x_3973_, v___f_3970_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed(lean_object** _args){
lean_object* v_toPure_3975_ = _args[0];
lean_object* v_inst_3976_ = _args[1];
lean_object* v_toBind_3977_ = _args[2];
lean_object* v_toMatcherInfo_3978_ = _args[3];
lean_object* v_inst_3979_ = _args[4];
lean_object* v___f_3980_ = _args[5];
lean_object* v_onMotive_3981_ = _args[6];
lean_object* v_discrs_3982_ = _args[7];
lean_object* v_inst_3983_ = _args[8];
lean_object* v_matcherName_3984_ = _args[9];
lean_object* v_onRemaining_3985_ = _args[10];
lean_object* v_remaining_3986_ = _args[11];
lean_object* v_inst_3987_ = _args[12];
lean_object* v_alts_3988_ = _args[13];
lean_object* v___f_3989_ = _args[14];
lean_object* v_onAlt_3990_ = _args[15];
lean_object* v___f_3991_ = _args[16];
lean_object* v_matcherApp_3992_ = _args[17];
lean_object* v_useSplitter_3993_ = _args[18];
lean_object* v_isCasesOn_3994_ = _args[19];
lean_object* v___f_3995_ = _args[20];
lean_object* v___f_3996_ = _args[21];
lean_object* v_numDiscrEqs_3997_ = _args[22];
lean_object* v___f_3998_ = _args[23];
lean_object* v_matcherLevels_3999_ = _args[24];
lean_object* v_motive_4000_ = _args[25];
lean_object* v_onParams_4001_ = _args[26];
lean_object* v_params_x27_4002_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_4003_; uint8_t v_isCasesOn_boxed_4004_; lean_object* v_res_4005_; 
v_useSplitter_boxed_4003_ = lean_unbox(v_useSplitter_3993_);
v_isCasesOn_boxed_4004_ = lean_unbox(v_isCasesOn_3994_);
v_res_4005_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__59(v_toPure_3975_, v_inst_3976_, v_toBind_3977_, v_toMatcherInfo_3978_, v_inst_3979_, v___f_3980_, v_onMotive_3981_, v_discrs_3982_, v_inst_3983_, v_matcherName_3984_, v_onRemaining_3985_, v_remaining_3986_, v_inst_3987_, v_alts_3988_, v___f_3989_, v_onAlt_3990_, v___f_3991_, v_matcherApp_3992_, v_useSplitter_boxed_4003_, v_isCasesOn_boxed_4004_, v___f_3995_, v___f_3996_, v_numDiscrEqs_3997_, v___f_3998_, v_matcherLevels_3999_, v_motive_4000_, v_onParams_4001_, v_params_x27_4002_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60(lean_object* v_toPure_4006_, lean_object* v_inst_4007_, lean_object* v_toBind_4008_, lean_object* v_toMatcherInfo_4009_, lean_object* v_inst_4010_, lean_object* v___f_4011_, lean_object* v_onMotive_4012_, lean_object* v_discrs_4013_, lean_object* v_inst_4014_, lean_object* v_matcherName_4015_, lean_object* v_onRemaining_4016_, lean_object* v_remaining_4017_, lean_object* v_inst_4018_, lean_object* v_alts_4019_, lean_object* v___f_4020_, lean_object* v_onAlt_4021_, lean_object* v___f_4022_, lean_object* v_matcherApp_4023_, uint8_t v_useSplitter_4024_, uint8_t v_isCasesOn_4025_, lean_object* v___f_4026_, lean_object* v___f_4027_, lean_object* v___f_4028_, lean_object* v_matcherLevels_4029_, lean_object* v_motive_4030_, lean_object* v_onParams_4031_, lean_object* v_params_4032_, lean_object* v_numDiscrEqs_4033_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___f_4036_; size_t v_sz_4037_; size_t v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4034_ = lean_box(v_useSplitter_4024_);
v___x_4035_ = lean_box(v_isCasesOn_4025_);
lean_inc(v_onParams_4031_);
lean_inc_ref(v_inst_4010_);
lean_inc(v_toBind_4008_);
v___f_4036_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__59___boxed), 28, 27);
lean_closure_set(v___f_4036_, 0, v_toPure_4006_);
lean_closure_set(v___f_4036_, 1, v_inst_4007_);
lean_closure_set(v___f_4036_, 2, v_toBind_4008_);
lean_closure_set(v___f_4036_, 3, v_toMatcherInfo_4009_);
lean_closure_set(v___f_4036_, 4, v_inst_4010_);
lean_closure_set(v___f_4036_, 5, v___f_4011_);
lean_closure_set(v___f_4036_, 6, v_onMotive_4012_);
lean_closure_set(v___f_4036_, 7, v_discrs_4013_);
lean_closure_set(v___f_4036_, 8, v_inst_4014_);
lean_closure_set(v___f_4036_, 9, v_matcherName_4015_);
lean_closure_set(v___f_4036_, 10, v_onRemaining_4016_);
lean_closure_set(v___f_4036_, 11, v_remaining_4017_);
lean_closure_set(v___f_4036_, 12, v_inst_4018_);
lean_closure_set(v___f_4036_, 13, v_alts_4019_);
lean_closure_set(v___f_4036_, 14, v___f_4020_);
lean_closure_set(v___f_4036_, 15, v_onAlt_4021_);
lean_closure_set(v___f_4036_, 16, v___f_4022_);
lean_closure_set(v___f_4036_, 17, v_matcherApp_4023_);
lean_closure_set(v___f_4036_, 18, v___x_4034_);
lean_closure_set(v___f_4036_, 19, v___x_4035_);
lean_closure_set(v___f_4036_, 20, v___f_4026_);
lean_closure_set(v___f_4036_, 21, v___f_4027_);
lean_closure_set(v___f_4036_, 22, v_numDiscrEqs_4033_);
lean_closure_set(v___f_4036_, 23, v___f_4028_);
lean_closure_set(v___f_4036_, 24, v_matcherLevels_4029_);
lean_closure_set(v___f_4036_, 25, v_motive_4030_);
lean_closure_set(v___f_4036_, 26, v_onParams_4031_);
v_sz_4037_ = lean_array_size(v_params_4032_);
v___x_4038_ = ((size_t)0ULL);
v___x_4039_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v_inst_4010_, v_onParams_4031_, v_sz_4037_, v___x_4038_, v_params_4032_);
v___x_4040_ = lean_apply_4(v_toBind_4008_, lean_box(0), lean_box(0), v___x_4039_, v___f_4036_);
return v___x_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed(lean_object** _args){
lean_object* v_toPure_4041_ = _args[0];
lean_object* v_inst_4042_ = _args[1];
lean_object* v_toBind_4043_ = _args[2];
lean_object* v_toMatcherInfo_4044_ = _args[3];
lean_object* v_inst_4045_ = _args[4];
lean_object* v___f_4046_ = _args[5];
lean_object* v_onMotive_4047_ = _args[6];
lean_object* v_discrs_4048_ = _args[7];
lean_object* v_inst_4049_ = _args[8];
lean_object* v_matcherName_4050_ = _args[9];
lean_object* v_onRemaining_4051_ = _args[10];
lean_object* v_remaining_4052_ = _args[11];
lean_object* v_inst_4053_ = _args[12];
lean_object* v_alts_4054_ = _args[13];
lean_object* v___f_4055_ = _args[14];
lean_object* v_onAlt_4056_ = _args[15];
lean_object* v___f_4057_ = _args[16];
lean_object* v_matcherApp_4058_ = _args[17];
lean_object* v_useSplitter_4059_ = _args[18];
lean_object* v_isCasesOn_4060_ = _args[19];
lean_object* v___f_4061_ = _args[20];
lean_object* v___f_4062_ = _args[21];
lean_object* v___f_4063_ = _args[22];
lean_object* v_matcherLevels_4064_ = _args[23];
lean_object* v_motive_4065_ = _args[24];
lean_object* v_onParams_4066_ = _args[25];
lean_object* v_params_4067_ = _args[26];
lean_object* v_numDiscrEqs_4068_ = _args[27];
_start:
{
uint8_t v_useSplitter_boxed_4069_; uint8_t v_isCasesOn_boxed_4070_; lean_object* v_res_4071_; 
v_useSplitter_boxed_4069_ = lean_unbox(v_useSplitter_4059_);
v_isCasesOn_boxed_4070_ = lean_unbox(v_isCasesOn_4060_);
v_res_4071_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__60(v_toPure_4041_, v_inst_4042_, v_toBind_4043_, v_toMatcherInfo_4044_, v_inst_4045_, v___f_4046_, v_onMotive_4047_, v_discrs_4048_, v_inst_4049_, v_matcherName_4050_, v_onRemaining_4051_, v_remaining_4052_, v_inst_4053_, v_alts_4054_, v___f_4055_, v_onAlt_4056_, v___f_4057_, v_matcherApp_4058_, v_useSplitter_boxed_4069_, v_isCasesOn_boxed_4070_, v___f_4061_, v___f_4062_, v___f_4063_, v_matcherLevels_4064_, v_motive_4065_, v_onParams_4066_, v_params_4067_, v_numDiscrEqs_4068_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__61(lean_object* v___f_4072_, lean_object* v_numDiscrEqs_4073_){
_start:
{
lean_object* v___x_4074_; 
v___x_4074_ = lean_apply_1(v___f_4072_, v_numDiscrEqs_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__0));
v___x_4077_ = l_Lean_stringToMessageData(v___x_4076_);
return v___x_4077_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__2));
v___x_4080_ = l_Lean_stringToMessageData(v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63(lean_object* v_matcherName_4081_, lean_object* v_inst_4082_, lean_object* v_inst_4083_, lean_object* v_toBind_4084_, lean_object* v___f_4085_, lean_object* v_toPure_4086_, lean_object* v___f_4087_, lean_object* v_____do__lift_4088_){
_start:
{
if (lean_obj_tag(v_____do__lift_4088_) == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
lean_dec(v___f_4087_);
lean_dec(v_toPure_4086_);
v___x_4089_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_4090_ = l_Lean_MessageData_ofName(v_matcherName_4081_);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_4093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4091_);
lean_ctor_set(v___x_4093_, 1, v___x_4092_);
v___x_4094_ = l_Lean_throwError___redArg(v_inst_4082_, v_inst_4083_, v___x_4093_);
v___x_4095_ = lean_apply_4(v_toBind_4084_, lean_box(0), lean_box(0), v___x_4094_, v___f_4085_);
return v___x_4095_;
}
else
{
lean_object* v_val_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
lean_dec(v___f_4085_);
lean_dec_ref(v_inst_4083_);
lean_dec_ref(v_inst_4082_);
lean_dec(v_matcherName_4081_);
v_val_4096_ = lean_ctor_get(v_____do__lift_4088_, 0);
v___x_4097_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_4096_);
v___x_4098_ = lean_apply_2(v_toPure_4086_, lean_box(0), v___x_4097_);
v___x_4099_ = lean_apply_4(v_toBind_4084_, lean_box(0), lean_box(0), v___x_4098_, v___f_4087_);
return v___x_4099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed(lean_object* v_matcherName_4100_, lean_object* v_inst_4101_, lean_object* v_inst_4102_, lean_object* v_toBind_4103_, lean_object* v___f_4104_, lean_object* v_toPure_4105_, lean_object* v___f_4106_, lean_object* v_____do__lift_4107_){
_start:
{
lean_object* v_res_4108_; 
v_res_4108_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__63(v_matcherName_4100_, v_inst_4101_, v_inst_4102_, v_toBind_4103_, v___f_4104_, v_toPure_4105_, v___f_4106_, v_____do__lift_4107_);
lean_dec(v_____do__lift_4107_);
return v_res_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___lam__64(lean_object* v_matcherApp_4109_, lean_object* v_toPure_4110_, lean_object* v_inst_4111_, lean_object* v_toBind_4112_, lean_object* v_inst_4113_, lean_object* v___f_4114_, lean_object* v_onMotive_4115_, lean_object* v_inst_4116_, lean_object* v_onRemaining_4117_, lean_object* v_inst_4118_, lean_object* v___f_4119_, lean_object* v_onAlt_4120_, lean_object* v___f_4121_, uint8_t v_useSplitter_4122_, lean_object* v___f_4123_, lean_object* v___f_4124_, lean_object* v___f_4125_, lean_object* v_onParams_4126_, lean_object* v_inst_4127_, lean_object* v_____do__lift_4128_){
_start:
{
lean_object* v_toMatcherInfo_4129_; lean_object* v_matcherName_4130_; lean_object* v_matcherLevels_4131_; lean_object* v_params_4132_; lean_object* v_motive_4133_; lean_object* v_discrs_4134_; lean_object* v_alts_4135_; lean_object* v_remaining_4136_; uint8_t v_isCasesOn_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___f_4140_; 
v_toMatcherInfo_4129_ = lean_ctor_get(v_matcherApp_4109_, 0);
lean_inc_ref(v_toMatcherInfo_4129_);
v_matcherName_4130_ = lean_ctor_get(v_matcherApp_4109_, 1);
lean_inc_n(v_matcherName_4130_, 3);
v_matcherLevels_4131_ = lean_ctor_get(v_matcherApp_4109_, 2);
lean_inc_ref(v_matcherLevels_4131_);
v_params_4132_ = lean_ctor_get(v_matcherApp_4109_, 3);
lean_inc_ref(v_params_4132_);
v_motive_4133_ = lean_ctor_get(v_matcherApp_4109_, 4);
lean_inc_ref(v_motive_4133_);
v_discrs_4134_ = lean_ctor_get(v_matcherApp_4109_, 5);
lean_inc_ref(v_discrs_4134_);
v_alts_4135_ = lean_ctor_get(v_matcherApp_4109_, 6);
lean_inc_ref(v_alts_4135_);
v_remaining_4136_ = lean_ctor_get(v_matcherApp_4109_, 7);
lean_inc_ref(v_remaining_4136_);
v_isCasesOn_4137_ = l_Lean_isCasesOnRecursor(v_____do__lift_4128_, v_matcherName_4130_);
v___x_4138_ = lean_box(v_useSplitter_4122_);
v___x_4139_ = lean_box(v_isCasesOn_4137_);
lean_inc_ref(v_inst_4116_);
lean_inc_ref(v_inst_4113_);
lean_inc(v_toBind_4112_);
lean_inc(v_toPure_4110_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__60___boxed), 28, 27);
lean_closure_set(v___f_4140_, 0, v_toPure_4110_);
lean_closure_set(v___f_4140_, 1, v_inst_4111_);
lean_closure_set(v___f_4140_, 2, v_toBind_4112_);
lean_closure_set(v___f_4140_, 3, v_toMatcherInfo_4129_);
lean_closure_set(v___f_4140_, 4, v_inst_4113_);
lean_closure_set(v___f_4140_, 5, v___f_4114_);
lean_closure_set(v___f_4140_, 6, v_onMotive_4115_);
lean_closure_set(v___f_4140_, 7, v_discrs_4134_);
lean_closure_set(v___f_4140_, 8, v_inst_4116_);
lean_closure_set(v___f_4140_, 9, v_matcherName_4130_);
lean_closure_set(v___f_4140_, 10, v_onRemaining_4117_);
lean_closure_set(v___f_4140_, 11, v_remaining_4136_);
lean_closure_set(v___f_4140_, 12, v_inst_4118_);
lean_closure_set(v___f_4140_, 13, v_alts_4135_);
lean_closure_set(v___f_4140_, 14, v___f_4119_);
lean_closure_set(v___f_4140_, 15, v_onAlt_4120_);
lean_closure_set(v___f_4140_, 16, v___f_4121_);
lean_closure_set(v___f_4140_, 17, v_matcherApp_4109_);
lean_closure_set(v___f_4140_, 18, v___x_4138_);
lean_closure_set(v___f_4140_, 19, v___x_4139_);
lean_closure_set(v___f_4140_, 20, v___f_4123_);
lean_closure_set(v___f_4140_, 21, v___f_4124_);
lean_closure_set(v___f_4140_, 22, v___f_4125_);
lean_closure_set(v___f_4140_, 23, v_matcherLevels_4131_);
lean_closure_set(v___f_4140_, 24, v_motive_4133_);
lean_closure_set(v___f_4140_, 25, v_onParams_4126_);
lean_closure_set(v___f_4140_, 26, v_params_4132_);
if (v_isCasesOn_4137_ == 0)
{
lean_object* v___f_4141_; lean_object* v___f_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___f_4141_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4141_, 0, v___f_4140_);
lean_inc_ref(v___f_4141_);
lean_inc(v_toBind_4112_);
lean_inc_ref(v_inst_4113_);
lean_inc(v_matcherName_4130_);
v___f_4142_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__63___boxed), 8, 7);
lean_closure_set(v___f_4142_, 0, v_matcherName_4130_);
lean_closure_set(v___f_4142_, 1, v_inst_4113_);
lean_closure_set(v___f_4142_, 2, v_inst_4116_);
lean_closure_set(v___f_4142_, 3, v_toBind_4112_);
lean_closure_set(v___f_4142_, 4, v___f_4141_);
lean_closure_set(v___f_4142_, 5, v_toPure_4110_);
lean_closure_set(v___f_4142_, 6, v___f_4141_);
v___x_4143_ = l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_4113_, v_inst_4127_, v_matcherName_4130_);
v___x_4144_ = lean_apply_4(v_toBind_4112_, lean_box(0), lean_box(0), v___x_4143_, v___f_4142_);
return v___x_4144_;
}
else
{
lean_object* v___f_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
lean_dec(v_matcherName_4130_);
lean_dec_ref(v_inst_4127_);
lean_dec_ref(v_inst_4116_);
lean_dec_ref(v_inst_4113_);
v___f_4145_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__61), 2, 1);
lean_closure_set(v___f_4145_, 0, v___f_4140_);
v___x_4146_ = lean_unsigned_to_nat(0u);
v___x_4147_ = lean_apply_2(v_toPure_4110_, lean_box(0), v___x_4146_);
v___x_4148_ = lean_apply_4(v_toBind_4112_, lean_box(0), lean_box(0), v___x_4147_, v___f_4145_);
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
lean_object* v___f_4164_ = _args[15];
lean_object* v___f_4165_ = _args[16];
lean_object* v_onParams_4166_ = _args[17];
lean_object* v_inst_4167_ = _args[18];
lean_object* v_____do__lift_4168_ = _args[19];
_start:
{
uint8_t v_useSplitter_boxed_4169_; lean_object* v_res_4170_; 
v_useSplitter_boxed_4169_ = lean_unbox(v_useSplitter_4162_);
v_res_4170_ = l_Lean_Meta_MatcherApp_transform___redArg___lam__64(v_matcherApp_4149_, v_toPure_4150_, v_inst_4151_, v_toBind_4152_, v_inst_4153_, v___f_4154_, v_onMotive_4155_, v_inst_4156_, v_onRemaining_4157_, v_inst_4158_, v___f_4159_, v_onAlt_4160_, v___f_4161_, v_useSplitter_boxed_4169_, v___f_4163_, v___f_4164_, v___f_4165_, v_onParams_4166_, v_inst_4167_, v_____do__lift_4168_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object* v_inst_4171_, lean_object* v_inst_4172_, lean_object* v_inst_4173_, lean_object* v_inst_4174_, lean_object* v_inst_4175_, lean_object* v_matcherApp_4176_, uint8_t v_useSplitter_4177_, uint8_t v_addEqualities_4178_, lean_object* v_onParams_4179_, lean_object* v_onMotive_4180_, lean_object* v_onAlt_4181_, lean_object* v_onRemaining_4182_){
_start:
{
lean_object* v_toApplicative_4183_; lean_object* v_toBind_4184_; lean_object* v_getEnv_4185_; lean_object* v_toPure_4186_; lean_object* v___f_4187_; lean_object* v___f_4188_; lean_object* v___f_4189_; lean_object* v___f_4190_; lean_object* v___f_4191_; lean_object* v___f_4192_; lean_object* v___x_4193_; lean_object* v___f_4194_; lean_object* v___x_4195_; lean_object* v___f_4196_; lean_object* v___x_4197_; 
v_toApplicative_4183_ = lean_ctor_get(v_inst_4173_, 0);
v_toBind_4184_ = lean_ctor_get(v_inst_4173_, 1);
lean_inc_n(v_toBind_4184_, 4);
v_getEnv_4185_ = lean_ctor_get(v_inst_4175_, 0);
lean_inc(v_getEnv_4185_);
v_toPure_4186_ = lean_ctor_get(v_toApplicative_4183_, 1);
lean_inc_n(v_toPure_4186_, 5);
lean_inc_ref(v_inst_4174_);
lean_inc_ref_n(v_inst_4173_, 2);
v___f_4187_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4187_, 0, v_inst_4173_);
lean_closure_set(v___f_4187_, 1, v_inst_4174_);
lean_inc_n(v_inst_4171_, 3);
v___f_4188_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_4188_, 0, v_inst_4171_);
v___f_4189_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_4189_, 0, v_inst_4173_);
lean_closure_set(v___f_4189_, 1, v___f_4188_);
v___f_4190_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__3), 2, 1);
lean_closure_set(v___f_4190_, 0, v_toPure_4186_);
v___f_4191_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__4), 2, 1);
lean_closure_set(v___f_4191_, 0, v_toPure_4186_);
v___f_4192_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__7), 6, 3);
lean_closure_set(v___f_4192_, 0, v_toPure_4186_);
lean_closure_set(v___f_4192_, 1, v_inst_4171_);
lean_closure_set(v___f_4192_, 2, v_toBind_4184_);
v___x_4193_ = lean_box(v_addEqualities_4178_);
v___f_4194_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__12___boxed), 7, 4);
lean_closure_set(v___f_4194_, 0, v_toPure_4186_);
lean_closure_set(v___f_4194_, 1, v___x_4193_);
lean_closure_set(v___f_4194_, 2, v_inst_4171_);
lean_closure_set(v___f_4194_, 3, v_toBind_4184_);
v___x_4195_ = lean_box(v_useSplitter_4177_);
v___f_4196_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__64___boxed), 20, 19);
lean_closure_set(v___f_4196_, 0, v_matcherApp_4176_);
lean_closure_set(v___f_4196_, 1, v_toPure_4186_);
lean_closure_set(v___f_4196_, 2, v_inst_4171_);
lean_closure_set(v___f_4196_, 3, v_toBind_4184_);
lean_closure_set(v___f_4196_, 4, v_inst_4173_);
lean_closure_set(v___f_4196_, 5, v___f_4194_);
lean_closure_set(v___f_4196_, 6, v_onMotive_4180_);
lean_closure_set(v___f_4196_, 7, v_inst_4174_);
lean_closure_set(v___f_4196_, 8, v_onRemaining_4182_);
lean_closure_set(v___f_4196_, 9, v_inst_4172_);
lean_closure_set(v___f_4196_, 10, v___f_4190_);
lean_closure_set(v___f_4196_, 11, v_onAlt_4181_);
lean_closure_set(v___f_4196_, 12, v___f_4189_);
lean_closure_set(v___f_4196_, 13, v___x_4195_);
lean_closure_set(v___f_4196_, 14, v___f_4191_);
lean_closure_set(v___f_4196_, 15, v___f_4187_);
lean_closure_set(v___f_4196_, 16, v___f_4192_);
lean_closure_set(v___f_4196_, 17, v_onParams_4179_);
lean_closure_set(v___f_4196_, 18, v_inst_4175_);
v___x_4197_ = lean_apply_4(v_toBind_4184_, lean_box(0), lean_box(0), v_getEnv_4185_, v___f_4196_);
return v___x_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___redArg___boxed(lean_object* v_inst_4198_, lean_object* v_inst_4199_, lean_object* v_inst_4200_, lean_object* v_inst_4201_, lean_object* v_inst_4202_, lean_object* v_matcherApp_4203_, lean_object* v_useSplitter_4204_, lean_object* v_addEqualities_4205_, lean_object* v_onParams_4206_, lean_object* v_onMotive_4207_, lean_object* v_onAlt_4208_, lean_object* v_onRemaining_4209_){
_start:
{
uint8_t v_useSplitter_boxed_4210_; uint8_t v_addEqualities_boxed_4211_; lean_object* v_res_4212_; 
v_useSplitter_boxed_4210_ = lean_unbox(v_useSplitter_4204_);
v_addEqualities_boxed_4211_ = lean_unbox(v_addEqualities_4205_);
v_res_4212_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4198_, v_inst_4199_, v_inst_4200_, v_inst_4201_, v_inst_4202_, v_matcherApp_4203_, v_useSplitter_boxed_4210_, v_addEqualities_boxed_4211_, v_onParams_4206_, v_onMotive_4207_, v_onAlt_4208_, v_onRemaining_4209_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform(lean_object* v_n_4213_, lean_object* v_inst_4214_, lean_object* v_inst_4215_, lean_object* v_inst_4216_, lean_object* v_inst_4217_, lean_object* v_inst_4218_, lean_object* v_inst_4219_, lean_object* v_inst_4220_, lean_object* v_inst_4221_, lean_object* v_matcherApp_4222_, uint8_t v_useSplitter_4223_, uint8_t v_addEqualities_4224_, lean_object* v_onParams_4225_, lean_object* v_onMotive_4226_, lean_object* v_onAlt_4227_, lean_object* v_onRemaining_4228_){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_4214_, v_inst_4215_, v_inst_4216_, v_inst_4217_, v_inst_4218_, v_matcherApp_4222_, v_useSplitter_4223_, v_addEqualities_4224_, v_onParams_4225_, v_onMotive_4226_, v_onAlt_4227_, v_onRemaining_4228_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___boxed(lean_object* v_n_4230_, lean_object* v_inst_4231_, lean_object* v_inst_4232_, lean_object* v_inst_4233_, lean_object* v_inst_4234_, lean_object* v_inst_4235_, lean_object* v_inst_4236_, lean_object* v_inst_4237_, lean_object* v_inst_4238_, lean_object* v_matcherApp_4239_, lean_object* v_useSplitter_4240_, lean_object* v_addEqualities_4241_, lean_object* v_onParams_4242_, lean_object* v_onMotive_4243_, lean_object* v_onAlt_4244_, lean_object* v_onRemaining_4245_){
_start:
{
uint8_t v_useSplitter_boxed_4246_; uint8_t v_addEqualities_boxed_4247_; lean_object* v_res_4248_; 
v_useSplitter_boxed_4246_ = lean_unbox(v_useSplitter_4240_);
v_addEqualities_boxed_4247_ = lean_unbox(v_addEqualities_4241_);
v_res_4248_ = l_Lean_Meta_MatcherApp_transform(v_n_4230_, v_inst_4231_, v_inst_4232_, v_inst_4233_, v_inst_4234_, v_inst_4235_, v_inst_4236_, v_inst_4237_, v_inst_4238_, v_matcherApp_4239_, v_useSplitter_boxed_4246_, v_addEqualities_boxed_4247_, v_onParams_4242_, v_onMotive_4243_, v_onAlt_4244_, v_onRemaining_4245_);
lean_dec(v_inst_4238_);
lean_dec(v_inst_4237_);
lean_dec_ref(v_inst_4236_);
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0(lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v___x_4255_; 
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___y_4249_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__0___boxed(lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__0(v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1(lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_){
_start:
{
lean_object* v___x_4269_; 
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v___y_4263_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__1___boxed(lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__1(v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
return v_res_4276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(lean_object* v_opts_4277_, lean_object* v_opt_4278_){
_start:
{
lean_object* v_name_4279_; lean_object* v_defValue_4280_; lean_object* v_map_4281_; lean_object* v___x_4282_; 
v_name_4279_ = lean_ctor_get(v_opt_4278_, 0);
v_defValue_4280_ = lean_ctor_get(v_opt_4278_, 1);
v_map_4281_ = lean_ctor_get(v_opts_4277_, 0);
v___x_4282_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4281_, v_name_4279_);
if (lean_obj_tag(v___x_4282_) == 0)
{
uint8_t v___x_4283_; 
v___x_4283_ = lean_unbox(v_defValue_4280_);
return v___x_4283_;
}
else
{
lean_object* v_val_4284_; 
v_val_4284_ = lean_ctor_get(v___x_4282_, 0);
lean_inc(v_val_4284_);
lean_dec_ref_known(v___x_4282_, 1);
if (lean_obj_tag(v_val_4284_) == 1)
{
uint8_t v_v_4285_; 
v_v_4285_ = lean_ctor_get_uint8(v_val_4284_, 0);
lean_dec_ref_known(v_val_4284_, 0);
return v_v_4285_;
}
else
{
uint8_t v___x_4286_; 
lean_dec(v_val_4284_);
v___x_4286_ = lean_unbox(v_defValue_4280_);
return v___x_4286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11___boxed(lean_object* v_opts_4287_, lean_object* v_opt_4288_){
_start:
{
uint8_t v_res_4289_; lean_object* v_r_4290_; 
v_res_4289_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_opts_4287_, v_opt_4288_);
lean_dec_ref(v_opt_4288_);
lean_dec_ref(v_opts_4287_);
v_r_4290_ = lean_box(v_res_4289_);
return v_r_4290_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_4299_, uint8_t v_suppressElabErrors_4300_, lean_object* v_x_4301_){
_start:
{
if (lean_obj_tag(v_x_4301_) == 1)
{
lean_object* v_pre_4302_; 
v_pre_4302_ = lean_ctor_get(v_x_4301_, 0);
switch(lean_obj_tag(v_pre_4302_))
{
case 1:
{
lean_object* v_pre_4303_; 
v_pre_4303_ = lean_ctor_get(v_pre_4302_, 0);
switch(lean_obj_tag(v_pre_4303_))
{
case 0:
{
lean_object* v_str_4304_; lean_object* v_str_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v_str_4304_ = lean_ctor_get(v_x_4301_, 1);
v_str_4305_ = lean_ctor_get(v_pre_4302_, 1);
v___x_4306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_4307_ = lean_string_dec_eq(v_str_4305_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; uint8_t v___x_4309_; 
v___x_4308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_4309_ = lean_string_dec_eq(v_str_4305_, v___x_4308_);
if (v___x_4309_ == 0)
{
return v___y_4299_;
}
else
{
lean_object* v___x_4310_; uint8_t v___x_4311_; 
v___x_4310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_4311_ = lean_string_dec_eq(v_str_4304_, v___x_4310_);
if (v___x_4311_ == 0)
{
return v___y_4299_;
}
else
{
return v_suppressElabErrors_4300_;
}
}
}
else
{
lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4312_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_4313_ = lean_string_dec_eq(v_str_4304_, v___x_4312_);
if (v___x_4313_ == 0)
{
return v___y_4299_;
}
else
{
return v_suppressElabErrors_4300_;
}
}
}
case 1:
{
lean_object* v_pre_4314_; 
v_pre_4314_ = lean_ctor_get(v_pre_4303_, 0);
if (lean_obj_tag(v_pre_4314_) == 0)
{
lean_object* v_str_4315_; lean_object* v_str_4316_; lean_object* v_str_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v_str_4315_ = lean_ctor_get(v_x_4301_, 1);
v_str_4316_ = lean_ctor_get(v_pre_4302_, 1);
v_str_4317_ = lean_ctor_get(v_pre_4303_, 1);
v___x_4318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_4319_ = lean_string_dec_eq(v_str_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
return v___y_4299_;
}
else
{
lean_object* v___x_4320_; uint8_t v___x_4321_; 
v___x_4320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_4321_ = lean_string_dec_eq(v_str_4316_, v___x_4320_);
if (v___x_4321_ == 0)
{
return v___y_4299_;
}
else
{
lean_object* v___x_4322_; uint8_t v___x_4323_; 
v___x_4322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_4323_ = lean_string_dec_eq(v_str_4315_, v___x_4322_);
if (v___x_4323_ == 0)
{
return v___y_4299_;
}
else
{
return v_suppressElabErrors_4300_;
}
}
}
}
else
{
return v___y_4299_;
}
}
default: 
{
return v___y_4299_;
}
}
}
case 0:
{
lean_object* v_str_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v_str_4324_ = lean_ctor_get(v_x_4301_, 1);
v___x_4325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___closed__7));
v___x_4326_ = lean_string_dec_eq(v_str_4324_, v___x_4325_);
if (v___x_4326_ == 0)
{
return v___y_4299_;
}
else
{
return v_suppressElabErrors_4300_;
}
}
default: 
{
return v___y_4299_;
}
}
}
else
{
return v___y_4299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_4327_, lean_object* v_suppressElabErrors_4328_, lean_object* v_x_4329_){
_start:
{
uint8_t v___y_32033__boxed_4330_; uint8_t v_suppressElabErrors_boxed_4331_; uint8_t v_res_4332_; lean_object* v_r_4333_; 
v___y_32033__boxed_4330_ = lean_unbox(v___y_4327_);
v_suppressElabErrors_boxed_4331_ = lean_unbox(v_suppressElabErrors_4328_);
v_res_4332_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0(v___y_32033__boxed_4330_, v_suppressElabErrors_boxed_4331_, v_x_4329_);
lean_dec(v_x_4329_);
v_r_4333_ = lean_box(v_res_4332_);
return v_r_4333_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(lean_object* v_ref_4335_, lean_object* v_msgData_4336_, uint8_t v_severity_4337_, uint8_t v_isSilent_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_){
_start:
{
uint8_t v___y_4345_; lean_object* v___y_4346_; uint8_t v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4381_; uint8_t v___y_4382_; lean_object* v___y_4383_; lean_object* v___y_4384_; uint8_t v___y_4385_; uint8_t v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4406_; lean_object* v___y_4407_; uint8_t v___y_4408_; uint8_t v___y_4409_; lean_object* v___y_4410_; uint8_t v___y_4411_; lean_object* v___y_4412_; lean_object* v___y_4413_; lean_object* v___y_4417_; lean_object* v___y_4418_; uint8_t v___y_4419_; uint8_t v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; uint8_t v___y_4423_; uint8_t v___x_4428_; lean_object* v___y_4430_; lean_object* v___y_4431_; uint8_t v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; uint8_t v___y_4435_; uint8_t v___y_4436_; uint8_t v___y_4438_; uint8_t v___x_4453_; 
v___x_4428_ = 2;
v___x_4453_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4337_, v___x_4428_);
if (v___x_4453_ == 0)
{
v___y_4438_ = v___x_4453_;
goto v___jp_4437_;
}
else
{
uint8_t v___x_4454_; 
lean_inc_ref(v_msgData_4336_);
v___x_4454_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4336_);
v___y_4438_ = v___x_4454_;
goto v___jp_4437_;
}
v___jp_4344_:
{
lean_object* v___x_4354_; lean_object* v_currNamespace_4355_; lean_object* v_openDecls_4356_; lean_object* v_env_4357_; lean_object* v_nextMacroScope_4358_; lean_object* v_ngen_4359_; lean_object* v_auxDeclNGen_4360_; lean_object* v_traceState_4361_; lean_object* v_cache_4362_; lean_object* v_messages_4363_; lean_object* v_infoState_4364_; lean_object* v_snapshotTasks_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4379_; 
v___x_4354_ = lean_st_ref_take(v___y_4353_);
v_currNamespace_4355_ = lean_ctor_get(v___y_4352_, 6);
v_openDecls_4356_ = lean_ctor_get(v___y_4352_, 7);
v_env_4357_ = lean_ctor_get(v___x_4354_, 0);
v_nextMacroScope_4358_ = lean_ctor_get(v___x_4354_, 1);
v_ngen_4359_ = lean_ctor_get(v___x_4354_, 2);
v_auxDeclNGen_4360_ = lean_ctor_get(v___x_4354_, 3);
v_traceState_4361_ = lean_ctor_get(v___x_4354_, 4);
v_cache_4362_ = lean_ctor_get(v___x_4354_, 5);
v_messages_4363_ = lean_ctor_get(v___x_4354_, 6);
v_infoState_4364_ = lean_ctor_get(v___x_4354_, 7);
v_snapshotTasks_4365_ = lean_ctor_get(v___x_4354_, 8);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4367_ = v___x_4354_;
v_isShared_4368_ = v_isSharedCheck_4379_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_snapshotTasks_4365_);
lean_inc(v_infoState_4364_);
lean_inc(v_messages_4363_);
lean_inc(v_cache_4362_);
lean_inc(v_traceState_4361_);
lean_inc(v_auxDeclNGen_4360_);
lean_inc(v_ngen_4359_);
lean_inc(v_nextMacroScope_4358_);
lean_inc(v_env_4357_);
lean_dec(v___x_4354_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4379_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4374_; 
lean_inc(v_openDecls_4356_);
lean_inc(v_currNamespace_4355_);
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v_currNamespace_4355_);
lean_ctor_set(v___x_4369_, 1, v_openDecls_4356_);
v___x_4370_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4370_, 0, v___x_4369_);
lean_ctor_set(v___x_4370_, 1, v___y_4350_);
lean_inc_ref(v___y_4349_);
lean_inc_ref(v___y_4348_);
v___x_4371_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4371_, 0, v___y_4348_);
lean_ctor_set(v___x_4371_, 1, v___y_4351_);
lean_ctor_set(v___x_4371_, 2, v___y_4346_);
lean_ctor_set(v___x_4371_, 3, v___y_4349_);
lean_ctor_set(v___x_4371_, 4, v___x_4370_);
lean_ctor_set_uint8(v___x_4371_, sizeof(void*)*5, v___y_4347_);
lean_ctor_set_uint8(v___x_4371_, sizeof(void*)*5 + 1, v___y_4345_);
lean_ctor_set_uint8(v___x_4371_, sizeof(void*)*5 + 2, v_isSilent_4338_);
v___x_4372_ = l_Lean_MessageLog_add(v___x_4371_, v_messages_4363_);
if (v_isShared_4368_ == 0)
{
lean_ctor_set(v___x_4367_, 6, v___x_4372_);
v___x_4374_ = v___x_4367_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_env_4357_);
lean_ctor_set(v_reuseFailAlloc_4378_, 1, v_nextMacroScope_4358_);
lean_ctor_set(v_reuseFailAlloc_4378_, 2, v_ngen_4359_);
lean_ctor_set(v_reuseFailAlloc_4378_, 3, v_auxDeclNGen_4360_);
lean_ctor_set(v_reuseFailAlloc_4378_, 4, v_traceState_4361_);
lean_ctor_set(v_reuseFailAlloc_4378_, 5, v_cache_4362_);
lean_ctor_set(v_reuseFailAlloc_4378_, 6, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4378_, 7, v_infoState_4364_);
lean_ctor_set(v_reuseFailAlloc_4378_, 8, v_snapshotTasks_4365_);
v___x_4374_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v___x_4375_ = lean_st_ref_set(v___y_4353_, v___x_4374_);
v___x_4376_ = lean_box(0);
v___x_4377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4377_, 0, v___x_4376_);
return v___x_4377_;
}
}
}
v___jp_4380_:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4404_; 
v___x_4389_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4336_);
v___x_4390_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0_spec__0(v___x_4389_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4393_ = v___x_4390_;
v_isShared_4394_ = v_isSharedCheck_4404_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4404_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
lean_inc_ref_n(v___y_4383_, 2);
v___x_4395_ = l_Lean_FileMap_toPosition(v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
v___x_4396_ = l_Lean_FileMap_toPosition(v___y_4383_, v___y_4388_);
lean_dec(v___y_4388_);
v___x_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4396_);
v___x_4398_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___closed__0));
if (v___y_4385_ == 0)
{
lean_del_object(v___x_4393_);
lean_dec_ref(v___y_4381_);
v___y_4345_ = v___y_4382_;
v___y_4346_ = v___x_4397_;
v___y_4347_ = v___y_4386_;
v___y_4348_ = v___y_4387_;
v___y_4349_ = v___x_4398_;
v___y_4350_ = v_a_4391_;
v___y_4351_ = v___x_4395_;
v___y_4352_ = v___y_4341_;
v___y_4353_ = v___y_4342_;
goto v___jp_4344_;
}
else
{
uint8_t v___x_4399_; 
lean_inc(v_a_4391_);
v___x_4399_ = l_Lean_MessageData_hasTag(v___y_4381_, v_a_4391_);
if (v___x_4399_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4402_; 
lean_dec_ref_known(v___x_4397_, 1);
lean_dec_ref(v___x_4395_);
lean_dec(v_a_4391_);
v___x_4400_ = lean_box(0);
if (v_isShared_4394_ == 0)
{
lean_ctor_set(v___x_4393_, 0, v___x_4400_);
v___x_4402_ = v___x_4393_;
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
lean_del_object(v___x_4393_);
v___y_4345_ = v___y_4382_;
v___y_4346_ = v___x_4397_;
v___y_4347_ = v___y_4386_;
v___y_4348_ = v___y_4387_;
v___y_4349_ = v___x_4398_;
v___y_4350_ = v_a_4391_;
v___y_4351_ = v___x_4395_;
v___y_4352_ = v___y_4341_;
v___y_4353_ = v___y_4342_;
goto v___jp_4344_;
}
}
}
}
v___jp_4405_:
{
lean_object* v___x_4414_; 
v___x_4414_ = l_Lean_Syntax_getTailPos_x3f(v___y_4410_, v___y_4411_);
lean_dec(v___y_4410_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_inc(v___y_4413_);
v___y_4381_ = v___y_4406_;
v___y_4382_ = v___y_4408_;
v___y_4383_ = v___y_4407_;
v___y_4384_ = v___y_4413_;
v___y_4385_ = v___y_4409_;
v___y_4386_ = v___y_4411_;
v___y_4387_ = v___y_4412_;
v___y_4388_ = v___y_4413_;
goto v___jp_4380_;
}
else
{
lean_object* v_val_4415_; 
v_val_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_val_4415_);
lean_dec_ref_known(v___x_4414_, 1);
v___y_4381_ = v___y_4406_;
v___y_4382_ = v___y_4408_;
v___y_4383_ = v___y_4407_;
v___y_4384_ = v___y_4413_;
v___y_4385_ = v___y_4409_;
v___y_4386_ = v___y_4411_;
v___y_4387_ = v___y_4412_;
v___y_4388_ = v_val_4415_;
goto v___jp_4380_;
}
}
v___jp_4416_:
{
lean_object* v_ref_4424_; lean_object* v___x_4425_; 
v_ref_4424_ = l_Lean_replaceRef(v_ref_4335_, v___y_4421_);
v___x_4425_ = l_Lean_Syntax_getPos_x3f(v_ref_4424_, v___y_4420_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v___x_4426_; 
v___x_4426_ = lean_unsigned_to_nat(0u);
v___y_4406_ = v___y_4417_;
v___y_4407_ = v___y_4418_;
v___y_4408_ = v___y_4423_;
v___y_4409_ = v___y_4419_;
v___y_4410_ = v_ref_4424_;
v___y_4411_ = v___y_4420_;
v___y_4412_ = v___y_4422_;
v___y_4413_ = v___x_4426_;
goto v___jp_4405_;
}
else
{
lean_object* v_val_4427_; 
v_val_4427_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_val_4427_);
lean_dec_ref_known(v___x_4425_, 1);
v___y_4406_ = v___y_4417_;
v___y_4407_ = v___y_4418_;
v___y_4408_ = v___y_4423_;
v___y_4409_ = v___y_4419_;
v___y_4410_ = v_ref_4424_;
v___y_4411_ = v___y_4420_;
v___y_4412_ = v___y_4422_;
v___y_4413_ = v_val_4427_;
goto v___jp_4405_;
}
}
v___jp_4429_:
{
if (v___y_4436_ == 0)
{
v___y_4417_ = v___y_4431_;
v___y_4418_ = v___y_4430_;
v___y_4419_ = v___y_4432_;
v___y_4420_ = v___y_4435_;
v___y_4421_ = v___y_4433_;
v___y_4422_ = v___y_4434_;
v___y_4423_ = v_severity_4337_;
goto v___jp_4416_;
}
else
{
v___y_4417_ = v___y_4431_;
v___y_4418_ = v___y_4430_;
v___y_4419_ = v___y_4432_;
v___y_4420_ = v___y_4435_;
v___y_4421_ = v___y_4433_;
v___y_4422_ = v___y_4434_;
v___y_4423_ = v___x_4428_;
goto v___jp_4416_;
}
}
v___jp_4437_:
{
if (v___y_4438_ == 0)
{
lean_object* v_fileName_4439_; lean_object* v_fileMap_4440_; lean_object* v_options_4441_; lean_object* v_ref_4442_; uint8_t v_suppressElabErrors_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___f_4446_; uint8_t v___x_4447_; uint8_t v___x_4448_; 
v_fileName_4439_ = lean_ctor_get(v___y_4341_, 0);
v_fileMap_4440_ = lean_ctor_get(v___y_4341_, 1);
v_options_4441_ = lean_ctor_get(v___y_4341_, 2);
v_ref_4442_ = lean_ctor_get(v___y_4341_, 5);
v_suppressElabErrors_4443_ = lean_ctor_get_uint8(v___y_4341_, sizeof(void*)*14 + 1);
v___x_4444_ = lean_box(v___y_4438_);
v___x_4445_ = lean_box(v_suppressElabErrors_4443_);
v___f_4446_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4446_, 0, v___x_4444_);
lean_closure_set(v___f_4446_, 1, v___x_4445_);
v___x_4447_ = 1;
v___x_4448_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4337_, v___x_4447_);
if (v___x_4448_ == 0)
{
v___y_4430_ = v_fileMap_4440_;
v___y_4431_ = v___f_4446_;
v___y_4432_ = v_suppressElabErrors_4443_;
v___y_4433_ = v_ref_4442_;
v___y_4434_ = v_fileName_4439_;
v___y_4435_ = v___y_4438_;
v___y_4436_ = v___x_4448_;
goto v___jp_4429_;
}
else
{
lean_object* v___x_4449_; uint8_t v___x_4450_; 
v___x_4449_ = l_Lean_warningAsError;
v___x_4450_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1_spec__11(v_options_4441_, v___x_4449_);
v___y_4430_ = v_fileMap_4440_;
v___y_4431_ = v___f_4446_;
v___y_4432_ = v_suppressElabErrors_4443_;
v___y_4433_ = v_ref_4442_;
v___y_4434_ = v_fileName_4439_;
v___y_4435_ = v___y_4438_;
v___y_4436_ = v___x_4450_;
goto v___jp_4429_;
}
}
else
{
lean_object* v___x_4451_; lean_object* v___x_4452_; 
lean_dec_ref(v_msgData_4336_);
v___x_4451_ = lean_box(0);
v___x_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4452_, 0, v___x_4451_);
return v___x_4452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4455_, lean_object* v_msgData_4456_, lean_object* v_severity_4457_, lean_object* v_isSilent_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
uint8_t v_severity_boxed_4464_; uint8_t v_isSilent_boxed_4465_; lean_object* v_res_4466_; 
v_severity_boxed_4464_ = lean_unbox(v_severity_4457_);
v_isSilent_boxed_4465_ = lean_unbox(v_isSilent_4458_);
v_res_4466_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4455_, v_msgData_4456_, v_severity_boxed_4464_, v_isSilent_boxed_4465_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v_ref_4455_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(lean_object* v_msgData_4467_, uint8_t v_severity_4468_, uint8_t v_isSilent_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v_ref_4475_; lean_object* v___x_4476_; 
v_ref_4475_ = lean_ctor_get(v___y_4472_, 5);
v___x_4476_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0_spec__1(v_ref_4475_, v_msgData_4467_, v_severity_4468_, v_isSilent_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
return v___x_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0___boxed(lean_object* v_msgData_4477_, lean_object* v_severity_4478_, lean_object* v_isSilent_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
uint8_t v_severity_boxed_4485_; uint8_t v_isSilent_boxed_4486_; lean_object* v_res_4487_; 
v_severity_boxed_4485_ = lean_unbox(v_severity_4478_);
v_isSilent_boxed_4486_ = lean_unbox(v_isSilent_4479_);
v_res_4487_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4477_, v_severity_boxed_4485_, v_isSilent_boxed_4486_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(lean_object* v_msgData_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
uint8_t v___x_4494_; uint8_t v___x_4495_; lean_object* v___x_4496_; 
v___x_4494_ = 0;
v___x_4495_ = 0;
v___x_4496_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0_spec__0(v_msgData_4488_, v___x_4494_, v___x_4495_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0___boxed(lean_object* v_msgData_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v_msgData_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
return v_res_4503_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4505_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__0));
v___x_4506_ = l_Lean_stringToMessageData(v___x_4505_);
return v___x_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2(uint8_t v___x_4507_, lean_object* v___altIdx_4508_, lean_object* v_expAltType_4509_, lean_object* v___altFVars_4510_, lean_object* v_alt_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v___x_4517_; 
lean_inc(v___y_4515_);
lean_inc_ref(v___y_4514_);
lean_inc(v___y_4513_);
lean_inc_ref(v___y_4512_);
lean_inc_ref(v_alt_4511_);
v___x_4517_ = lean_infer_type(v_alt_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4517_) == 0)
{
lean_object* v_a_4518_; lean_object* v___x_4519_; 
v_a_4518_ = lean_ctor_get(v___x_4517_, 0);
lean_inc(v_a_4518_);
lean_dec_ref_known(v___x_4517_, 1);
v___x_4519_ = l_Lean_Meta_mkEq(v_expAltType_4509_, v_a_4518_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v_a_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_a_4520_ = lean_ctor_get(v___x_4519_, 0);
lean_inc(v_a_4520_);
lean_dec_ref_known(v___x_4519_, 1);
v___x_4521_ = lean_box(0);
v___x_4522_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_4520_, v___x_4521_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4522_) == 0)
{
lean_object* v_a_4523_; lean_object* v___y_4525_; lean_object* v___x_4535_; lean_object* v___x_4536_; 
v_a_4523_ = lean_ctor_get(v___x_4522_, 0);
lean_inc(v_a_4523_);
lean_dec_ref_known(v___x_4522_, 1);
v___x_4535_ = l_Lean_Expr_mvarId_x21(v_a_4523_);
v___x_4536_ = l_Lean_Meta_Split_simpMatchTarget(v___x_4535_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4538_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc_n(v_a_4537_, 2);
lean_dec_ref_known(v___x_4536_, 1);
v___x_4538_ = l_Lean_MVarId_refl(v_a_4537_, v___x_4507_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4538_) == 0)
{
lean_dec(v_a_4537_);
v___y_4525_ = v___x_4538_;
goto v___jp_4524_;
}
else
{
lean_object* v_a_4539_; uint8_t v___y_4541_; uint8_t v___x_4554_; 
v_a_4539_ = lean_ctor_get(v___x_4538_, 0);
lean_inc(v_a_4539_);
v___x_4554_ = l_Lean_Exception_isInterrupt(v_a_4539_);
if (v___x_4554_ == 0)
{
uint8_t v___x_4555_; 
v___x_4555_ = l_Lean_Exception_isRuntime(v_a_4539_);
v___y_4541_ = v___x_4555_;
goto v___jp_4540_;
}
else
{
lean_dec(v_a_4539_);
v___y_4541_ = v___x_4554_;
goto v___jp_4540_;
}
v___jp_4540_:
{
if (v___y_4541_ == 0)
{
lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4552_; 
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4538_);
if (v_isSharedCheck_4552_ == 0)
{
lean_object* v_unused_4553_; 
v_unused_4553_ = lean_ctor_get(v___x_4538_, 0);
lean_dec(v_unused_4553_);
v___x_4543_ = v___x_4538_;
v_isShared_4544_ = v_isSharedCheck_4552_;
goto v_resetjp_4542_;
}
else
{
lean_dec(v___x_4538_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4552_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4545_; lean_object* v___x_4547_; 
v___x_4545_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__2___closed__1);
lean_inc(v_a_4537_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v_a_4537_);
v___x_4547_ = v___x_4543_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4537_);
v___x_4547_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4548_, 0, v___x_4545_);
lean_ctor_set(v___x_4548_, 1, v___x_4547_);
v___x_4549_ = l_Lean_logInfo___at___00Lean_Meta_MatcherApp_inferMatchType_spec__0(v___x_4548_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v___x_4550_; 
lean_dec_ref_known(v___x_4549_, 1);
v___x_4550_ = l_Lean_MVarId_admit(v_a_4537_, v___x_4507_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
v___y_4525_ = v___x_4550_;
goto v___jp_4524_;
}
else
{
lean_dec(v_a_4537_);
v___y_4525_ = v___x_4549_;
goto v___jp_4524_;
}
}
}
}
else
{
lean_dec(v_a_4537_);
v___y_4525_ = v___x_4538_;
goto v___jp_4524_;
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v_a_4523_);
lean_dec_ref(v_alt_4511_);
v_a_4556_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4558_ = v___x_4536_;
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4536_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4563_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
v___x_4561_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
return v___x_4561_;
}
}
}
v___jp_4524_:
{
if (lean_obj_tag(v___y_4525_) == 0)
{
lean_object* v___x_4526_; 
lean_dec_ref_known(v___y_4525_, 1);
v___x_4526_ = l_Lean_Meta_mkEqMPR(v_a_4523_, v_alt_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
return v___x_4526_;
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
lean_dec(v_a_4523_);
lean_dec_ref(v_alt_4511_);
v_a_4527_ = lean_ctor_get(v___y_4525_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___y_4525_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v___y_4525_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___y_4525_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
else
{
lean_dec_ref(v_alt_4511_);
return v___x_4522_;
}
}
else
{
lean_dec_ref(v_alt_4511_);
return v___x_4519_;
}
}
else
{
lean_dec_ref(v_alt_4511_);
lean_dec_ref(v_expAltType_4509_);
return v___x_4517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__2___boxed(lean_object* v___x_4564_, lean_object* v___altIdx_4565_, lean_object* v_expAltType_4566_, lean_object* v___altFVars_4567_, lean_object* v_alt_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_){
_start:
{
uint8_t v___x_32356__boxed_4574_; lean_object* v_res_4575_; 
v___x_32356__boxed_4574_ = lean_unbox(v___x_4564_);
v_res_4575_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__2(v___x_32356__boxed_4574_, v___altIdx_4565_, v_expAltType_4566_, v___altFVars_4567_, v_alt_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
lean_dec(v___y_4572_);
lean_dec_ref(v___y_4571_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v___altFVars_4567_);
lean_dec(v___altIdx_4565_);
return v_res_4575_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(lean_object* v___x_4576_, lean_object* v_e_4577_){
_start:
{
uint8_t v___x_4578_; uint8_t v___x_4579_; 
v___x_4578_ = l_Lean_Expr_hasFVar(v_e_4577_);
v___x_4579_ = lean_bool_not(v___x_4578_);
if (v___x_4579_ == 0)
{
uint8_t v___x_4580_; lean_object* v_d_4582_; lean_object* v_b_4583_; 
v___x_4580_ = 1;
switch(lean_obj_tag(v_e_4577_))
{
case 7:
{
lean_object* v_binderType_4586_; lean_object* v_body_4587_; 
v_binderType_4586_ = lean_ctor_get(v_e_4577_, 1);
v_body_4587_ = lean_ctor_get(v_e_4577_, 2);
v_d_4582_ = v_binderType_4586_;
v_b_4583_ = v_body_4587_;
goto v___jp_4581_;
}
case 6:
{
lean_object* v_binderType_4588_; lean_object* v_body_4589_; 
v_binderType_4588_ = lean_ctor_get(v_e_4577_, 1);
v_body_4589_ = lean_ctor_get(v_e_4577_, 2);
v_d_4582_ = v_binderType_4588_;
v_b_4583_ = v_body_4589_;
goto v___jp_4581_;
}
case 10:
{
lean_object* v_expr_4590_; 
v_expr_4590_ = lean_ctor_get(v_e_4577_, 1);
v_e_4577_ = v_expr_4590_;
goto _start;
}
case 8:
{
lean_object* v_type_4592_; lean_object* v_value_4593_; lean_object* v_body_4594_; uint8_t v___x_4595_; 
v_type_4592_ = lean_ctor_get(v_e_4577_, 1);
v_value_4593_ = lean_ctor_get(v_e_4577_, 2);
v_body_4594_ = lean_ctor_get(v_e_4577_, 3);
v___x_4595_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4576_, v_type_4592_);
if (v___x_4595_ == 0)
{
uint8_t v___x_4596_; 
v___x_4596_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4576_, v_value_4593_);
if (v___x_4596_ == 0)
{
v_e_4577_ = v_body_4594_;
goto _start;
}
else
{
return v___x_4580_;
}
}
else
{
return v___x_4580_;
}
}
case 5:
{
lean_object* v_fn_4598_; lean_object* v_arg_4599_; uint8_t v___x_4600_; 
v_fn_4598_ = lean_ctor_get(v_e_4577_, 0);
v_arg_4599_ = lean_ctor_get(v_e_4577_, 1);
v___x_4600_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4576_, v_fn_4598_);
if (v___x_4600_ == 0)
{
v_e_4577_ = v_arg_4599_;
goto _start;
}
else
{
return v___x_4580_;
}
}
case 11:
{
lean_object* v_struct_4602_; 
v_struct_4602_ = lean_ctor_get(v_e_4577_, 2);
v_e_4577_ = v_struct_4602_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_4604_; lean_object* v___x_4605_; uint8_t v___x_4606_; 
v_fvarId_4604_ = lean_ctor_get(v_e_4577_, 0);
v___x_4605_ = l_Lean_Expr_fvarId_x21(v___x_4576_);
v___x_4606_ = l_Lean_instBEqFVarId_beq(v_fvarId_4604_, v___x_4605_);
lean_dec(v___x_4605_);
return v___x_4606_;
}
default: 
{
return v___x_4579_;
}
}
v___jp_4581_:
{
uint8_t v___x_4584_; 
v___x_4584_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4576_, v_d_4582_);
if (v___x_4584_ == 0)
{
v_e_4577_ = v_b_4583_;
goto _start;
}
else
{
return v___x_4580_;
}
}
}
else
{
uint8_t v___x_4607_; 
v___x_4607_ = 0;
return v___x_4607_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1___boxed(lean_object* v___x_4608_, lean_object* v_e_4609_){
_start:
{
uint8_t v_res_4610_; lean_object* v_r_4611_; 
v_res_4610_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4608_, v_e_4609_);
lean_dec_ref(v_e_4609_);
lean_dec_ref(v___x_4608_);
v_r_4611_ = lean_box(v_res_4610_);
return v_r_4611_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__0));
v___x_4614_ = l_Lean_stringToMessageData(v___x_4613_);
return v___x_4614_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__2));
v___x_4617_ = l_Lean_stringToMessageData(v___x_4616_);
return v___x_4617_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; 
v___x_4619_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__4));
v___x_4620_ = l_Lean_stringToMessageData(v___x_4619_);
return v___x_4620_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(lean_object* v_a_4621_, lean_object* v_termAlt_4622_, lean_object* v_a_4623_, lean_object* v_b_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v_array_4630_; lean_object* v_start_4631_; lean_object* v_stop_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4660_; 
v_array_4630_ = lean_ctor_get(v_a_4623_, 0);
v_start_4631_ = lean_ctor_get(v_a_4623_, 1);
v_stop_4632_ = lean_ctor_get(v_a_4623_, 2);
v_isSharedCheck_4660_ = !lean_is_exclusive(v_a_4623_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4634_ = v_a_4623_;
v_isShared_4635_ = v_isSharedCheck_4660_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_stop_4632_);
lean_inc(v_start_4631_);
lean_inc(v_array_4630_);
lean_dec(v_a_4623_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4660_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
uint8_t v___x_4636_; 
v___x_4636_ = lean_nat_dec_lt(v_start_4631_, v_stop_4632_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
lean_del_object(v___x_4634_);
lean_dec(v_stop_4632_);
lean_dec(v_start_4631_);
lean_dec_ref(v_array_4630_);
lean_dec_ref(v_termAlt_4622_);
lean_dec_ref(v_a_4621_);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v_b_4624_);
return v___x_4637_;
}
else
{
lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4642_; 
v___x_4638_ = lean_box(0);
v___x_4639_ = lean_unsigned_to_nat(1u);
v___x_4640_ = lean_nat_add(v_start_4631_, v___x_4639_);
lean_inc_ref(v_array_4630_);
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 1, v___x_4640_);
v___x_4642_ = v___x_4634_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v_array_4630_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v___x_4640_);
lean_ctor_set(v_reuseFailAlloc_4659_, 2, v_stop_4632_);
v___x_4642_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
lean_object* v___x_4643_; uint8_t v___x_4644_; 
v___x_4643_ = lean_array_fget(v_array_4630_, v_start_4631_);
lean_dec(v_start_4631_);
lean_dec_ref(v_array_4630_);
v___x_4644_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00Lean_Meta_MatcherApp_inferMatchType_spec__1(v___x_4643_, v_a_4621_);
if (v___x_4644_ == 0)
{
lean_dec(v___x_4643_);
v_a_4623_ = v___x_4642_;
v_b_4624_ = v___x_4638_;
goto _start;
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4646_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__1);
lean_inc_ref(v_a_4621_);
v___x_4647_ = l_Lean_MessageData_ofExpr(v_a_4621_);
v___x_4648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4648_, 0, v___x_4646_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
v___x_4649_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__3);
v___x_4650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4648_);
lean_ctor_set(v___x_4650_, 1, v___x_4649_);
lean_inc_ref(v_termAlt_4622_);
v___x_4651_ = l_Lean_MessageData_ofExpr(v_termAlt_4622_);
v___x_4652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4652_, 0, v___x_4650_);
lean_ctor_set(v___x_4652_, 1, v___x_4651_);
v___x_4653_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___closed__5);
v___x_4654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4652_);
lean_ctor_set(v___x_4654_, 1, v___x_4653_);
v___x_4655_ = l_Lean_MessageData_ofExpr(v___x_4643_);
v___x_4656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4656_, 0, v___x_4654_);
lean_ctor_set(v___x_4656_, 1, v___x_4655_);
v___x_4657_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_4656_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_dec_ref_known(v___x_4657_, 1);
v_a_4623_ = v___x_4642_;
v_b_4624_ = v___x_4638_;
goto _start;
}
else
{
lean_dec_ref(v___x_4642_);
lean_dec_ref(v_termAlt_4622_);
lean_dec_ref(v_a_4621_);
return v___x_4657_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg___boxed(lean_object* v_a_4661_, lean_object* v_termAlt_4662_, lean_object* v_a_4663_, lean_object* v_b_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4661_, v_termAlt_4662_, v_a_4663_, v_b_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(lean_object* v_nExtra_4671_, lean_object* v_v_4672_, uint8_t v___x_4673_, uint8_t v___x_4674_, uint8_t v___x_4675_, lean_object* v_xs_4676_, lean_object* v_termAltBody_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v___x_4683_; 
lean_inc(v___y_4681_);
lean_inc_ref(v___y_4680_);
lean_inc(v___y_4679_);
lean_inc_ref(v___y_4678_);
v___x_4683_ = lean_infer_type(v_termAltBody_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_object* v_a_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc_n(v_a_4684_, 2);
lean_dec_ref_known(v___x_4683_, 1);
v___x_4685_ = lean_array_get_size(v_xs_4676_);
v___x_4686_ = lean_nat_sub(v___x_4685_, v_nExtra_4671_);
v___x_4687_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_4686_);
lean_inc_ref(v_xs_4676_);
v___x_4688_ = l_Array_toSubarray___redArg(v_xs_4676_, v___x_4687_, v___x_4686_);
v___x_4689_ = l_Array_toSubarray___redArg(v_xs_4676_, v___x_4686_, v___x_4685_);
v___x_4690_ = lean_box(0);
v___x_4691_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_4684_, v_v_4672_, v___x_4689_, v___x_4690_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
lean_dec_ref_known(v___x_4691_, 1);
v___x_4692_ = l_Subarray_copy___redArg(v___x_4688_);
v___x_4693_ = l_Lean_Meta_mkLambdaFVars(v___x_4692_, v_a_4684_, v___x_4673_, v___x_4674_, v___x_4673_, v___x_4674_, v___x_4675_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
lean_dec_ref(v___x_4692_);
return v___x_4693_;
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec_ref(v___x_4688_);
lean_dec(v_a_4684_);
v_a_4694_ = lean_ctor_get(v___x_4691_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4691_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4691_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4691_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
else
{
lean_dec_ref(v_xs_4676_);
lean_dec(v_v_4672_);
return v___x_4683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed(lean_object* v_nExtra_4702_, lean_object* v_v_4703_, lean_object* v___x_4704_, lean_object* v___x_4705_, lean_object* v___x_4706_, lean_object* v_xs_4707_, lean_object* v_termAltBody_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
uint8_t v___x_32649__boxed_4714_; uint8_t v___x_32650__boxed_4715_; uint8_t v___x_32651__boxed_4716_; lean_object* v_res_4717_; 
v___x_32649__boxed_4714_ = lean_unbox(v___x_4704_);
v___x_32650__boxed_4715_ = lean_unbox(v___x_4705_);
v___x_32651__boxed_4716_ = lean_unbox(v___x_4706_);
v_res_4717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0(v_nExtra_4702_, v_v_4703_, v___x_32649__boxed_4714_, v___x_32650__boxed_4715_, v___x_32651__boxed_4716_, v_xs_4707_, v_termAltBody_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v_nExtra_4702_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(lean_object* v_nExtra_4718_, size_t v_sz_4719_, size_t v_i_4720_, lean_object* v_bs_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
uint8_t v___x_4727_; 
v___x_4727_ = lean_usize_dec_lt(v_i_4720_, v_sz_4719_);
if (v___x_4727_ == 0)
{
lean_object* v___x_4728_; 
lean_dec(v_nExtra_4718_);
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v_bs_4721_);
return v___x_4728_;
}
else
{
uint8_t v___x_4729_; uint8_t v___x_4730_; lean_object* v_v_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___f_4735_; lean_object* v___x_4736_; 
v___x_4729_ = 0;
v___x_4730_ = 1;
v_v_4731_ = lean_array_uget_borrowed(v_bs_4721_, v_i_4720_);
v___x_4732_ = lean_box(v___x_4729_);
v___x_4733_ = lean_box(v___x_4727_);
v___x_4734_ = lean_box(v___x_4730_);
lean_inc_n(v_v_4731_, 2);
lean_inc(v_nExtra_4718_);
v___f_4735_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___lam__0___boxed), 12, 5);
lean_closure_set(v___f_4735_, 0, v_nExtra_4718_);
lean_closure_set(v___f_4735_, 1, v_v_4731_);
lean_closure_set(v___f_4735_, 2, v___x_4732_);
lean_closure_set(v___f_4735_, 3, v___x_4733_);
lean_closure_set(v___f_4735_, 4, v___x_4734_);
v___x_4736_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_v_4731_, v___f_4735_, v___x_4729_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_);
if (lean_obj_tag(v___x_4736_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4738_; lean_object* v_bs_x27_4739_; size_t v___x_4740_; size_t v___x_4741_; lean_object* v___x_4742_; 
v_a_4737_ = lean_ctor_get(v___x_4736_, 0);
lean_inc(v_a_4737_);
lean_dec_ref_known(v___x_4736_, 1);
v___x_4738_ = lean_unsigned_to_nat(0u);
v_bs_x27_4739_ = lean_array_uset(v_bs_4721_, v_i_4720_, v___x_4738_);
v___x_4740_ = ((size_t)1ULL);
v___x_4741_ = lean_usize_add(v_i_4720_, v___x_4740_);
v___x_4742_ = lean_array_uset(v_bs_x27_4739_, v_i_4720_, v_a_4737_);
v_i_4720_ = v___x_4741_;
v_bs_4721_ = v___x_4742_;
goto _start;
}
else
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
lean_dec_ref(v_bs_4721_);
lean_dec(v_nExtra_4718_);
v_a_4744_ = lean_ctor_get(v___x_4736_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4736_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4736_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4736_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3___boxed(lean_object* v_nExtra_4752_, lean_object* v_sz_4753_, lean_object* v_i_4754_, lean_object* v_bs_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
size_t v_sz_boxed_4761_; size_t v_i_boxed_4762_; lean_object* v_res_4763_; 
v_sz_boxed_4761_ = lean_unbox_usize(v_sz_4753_);
lean_dec(v_sz_4753_);
v_i_boxed_4762_ = lean_unbox_usize(v_i_4754_);
lean_dec(v_i_4754_);
v_res_4763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4752_, v_sz_boxed_4761_, v_i_boxed_4762_, v_bs_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
return v_res_4763_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0(void){
_start:
{
lean_object* v___x_4764_; lean_object* v___x_4765_; 
v___x_4764_ = lean_box(0);
v___x_4765_ = l_Lean_Expr_sort___override(v___x_4764_);
return v___x_4765_;
}
}
static lean_object* _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1(void){
_start:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4766_ = lean_box(0);
v___x_4767_ = l_Lean_Level_succ___override(v___x_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3(lean_object* v_nExtra_4768_, uint8_t v___x_4769_, uint8_t v___x_4770_, lean_object* v_alts_4771_, lean_object* v_toMatcherInfo_4772_, lean_object* v_matcherName_4773_, lean_object* v_params_4774_, lean_object* v_matcherLevels_4775_, lean_object* v_motiveArgs_4776_, lean_object* v_body_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v___x_4783_; 
lean_inc(v_nExtra_4768_);
v___x_4783_ = l_Lean_Meta_arrowDomainsN(v_nExtra_4768_, v_body_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_object* v_a_4784_; lean_object* v___x_4785_; uint8_t v___x_4786_; lean_object* v___x_4787_; 
v_a_4784_ = lean_ctor_get(v___x_4783_, 0);
lean_inc(v_a_4784_);
lean_dec_ref_known(v___x_4783_, 1);
v___x_4785_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__0);
v___x_4786_ = 1;
v___x_4787_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_4776_, v___x_4785_, v___x_4769_, v___x_4770_, v___x_4769_, v___x_4770_, v___x_4786_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; size_t v_sz_4789_; size_t v___x_4790_; lean_object* v___x_4791_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc(v_a_4788_);
lean_dec_ref_known(v___x_4787_, 1);
v_sz_4789_ = lean_array_size(v_alts_4771_);
v___x_4790_ = ((size_t)0ULL);
v___x_4791_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_inferMatchType_spec__3(v_nExtra_4768_, v_sz_4789_, v___x_4790_, v_alts_4771_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v_matcherLevels_4794_; lean_object* v___y_4795_; lean_object* v___y_4796_; lean_object* v_uElimPos_x3f_4801_; 
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
lean_inc(v_a_4792_);
lean_dec_ref_known(v___x_4791_, 1);
v_uElimPos_x3f_4801_ = lean_ctor_get(v_toMatcherInfo_4772_, 3);
if (lean_obj_tag(v_uElimPos_x3f_4801_) == 0)
{
v_matcherLevels_4794_ = v_matcherLevels_4775_;
v___y_4795_ = v___y_4780_;
v___y_4796_ = v___y_4781_;
goto v___jp_4793_;
}
else
{
lean_object* v_val_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v_val_4802_ = lean_ctor_get(v_uElimPos_x3f_4801_, 0);
v___x_4803_ = lean_obj_once(&l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1, &l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1_once, _init_l_Lean_Meta_MatcherApp_inferMatchType___lam__3___closed__1);
v___x_4804_ = lean_array_set(v_matcherLevels_4775_, v_val_4802_, v___x_4803_);
v_matcherLevels_4794_ = v___x_4804_;
v___y_4795_ = v___y_4780_;
v___y_4796_ = v___y_4781_;
goto v___jp_4793_;
}
v___jp_4793_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4797_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_4798_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4798_, 0, v_toMatcherInfo_4772_);
lean_ctor_set(v___x_4798_, 1, v_matcherName_4773_);
lean_ctor_set(v___x_4798_, 2, v_matcherLevels_4794_);
lean_ctor_set(v___x_4798_, 3, v_params_4774_);
lean_ctor_set(v___x_4798_, 4, v_a_4788_);
lean_ctor_set(v___x_4798_, 5, v_motiveArgs_4776_);
lean_ctor_set(v___x_4798_, 6, v_a_4792_);
lean_ctor_set(v___x_4798_, 7, v___x_4797_);
v___x_4799_ = l_Lean_Meta_MatcherApp_toExpr(v___x_4798_);
v___x_4800_ = l_Lean_mkArrowN(v_a_4784_, v___x_4799_, v___y_4795_, v___y_4796_);
lean_dec(v_a_4784_);
return v___x_4800_;
}
}
else
{
lean_object* v_a_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4812_; 
lean_dec(v_a_4788_);
lean_dec(v_a_4784_);
lean_dec_ref(v_motiveArgs_4776_);
lean_dec_ref(v_matcherLevels_4775_);
lean_dec_ref(v_params_4774_);
lean_dec(v_matcherName_4773_);
lean_dec_ref(v_toMatcherInfo_4772_);
v_a_4805_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4807_ = v___x_4791_;
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_a_4805_);
lean_dec(v___x_4791_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4812_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4810_; 
if (v_isShared_4808_ == 0)
{
v___x_4810_ = v___x_4807_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_a_4805_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
else
{
lean_dec(v_a_4784_);
lean_dec_ref(v_motiveArgs_4776_);
lean_dec_ref(v_matcherLevels_4775_);
lean_dec_ref(v_params_4774_);
lean_dec(v_matcherName_4773_);
lean_dec_ref(v_toMatcherInfo_4772_);
lean_dec_ref(v_alts_4771_);
lean_dec(v_nExtra_4768_);
return v___x_4787_;
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec_ref(v_motiveArgs_4776_);
lean_dec_ref(v_matcherLevels_4775_);
lean_dec_ref(v_params_4774_);
lean_dec(v_matcherName_4773_);
lean_dec_ref(v_toMatcherInfo_4772_);
lean_dec_ref(v_alts_4771_);
lean_dec(v_nExtra_4768_);
v_a_4813_ = lean_ctor_get(v___x_4783_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4783_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4783_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4783_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed(lean_object* v_nExtra_4821_, lean_object* v___x_4822_, lean_object* v___x_4823_, lean_object* v_alts_4824_, lean_object* v_toMatcherInfo_4825_, lean_object* v_matcherName_4826_, lean_object* v_params_4827_, lean_object* v_matcherLevels_4828_, lean_object* v_motiveArgs_4829_, lean_object* v_body_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
uint8_t v___x_32784__boxed_4836_; uint8_t v___x_32785__boxed_4837_; lean_object* v_res_4838_; 
v___x_32784__boxed_4836_ = lean_unbox(v___x_4822_);
v___x_32785__boxed_4837_ = lean_unbox(v___x_4823_);
v_res_4838_ = l_Lean_Meta_MatcherApp_inferMatchType___lam__3(v_nExtra_4821_, v___x_32784__boxed_4836_, v___x_32785__boxed_4837_, v_alts_4824_, v_toMatcherInfo_4825_, v_matcherName_4826_, v_params_4827_, v_matcherLevels_4828_, v_motiveArgs_4829_, v_body_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_);
lean_dec(v___y_4834_);
lean_dec_ref(v___y_4833_);
lean_dec(v___y_4832_);
lean_dec_ref(v___y_4831_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(lean_object* v_k_4839_, lean_object* v_ys_4840_, lean_object* v_args_4841_, lean_object* v___mask_4842_, lean_object* v___bodyType_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
lean_inc(v___y_4847_);
lean_inc_ref(v___y_4846_);
lean_inc(v___y_4845_);
lean_inc_ref(v___y_4844_);
v___x_4849_ = lean_apply_7(v_k_4839_, v_ys_4840_, v_args_4841_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_, lean_box(0));
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed(lean_object* v_k_4850_, lean_object* v_ys_4851_, lean_object* v_args_4852_, lean_object* v___mask_4853_, lean_object* v___bodyType_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0(v_k_4850_, v_ys_4851_, v_args_4852_, v___mask_4853_, v___bodyType_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec_ref(v___bodyType_4854_);
lean_dec_ref(v___mask_4853_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(lean_object* v_origAltType_4861_, lean_object* v_altInfo_4862_, lean_object* v_k_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
lean_object* v___f_4869_; lean_object* v___x_4870_; 
v___f_4869_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___lam__0___boxed), 10, 1);
lean_closure_set(v___f_4869_, 0, v_k_4863_);
v___x_4870_ = l_Lean_Meta_Match_forallAltVarsTelescope___redArg(v_origAltType_4861_, v_altInfo_4862_, v___f_4869_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
else
{
lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
v_a_4879_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4870_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4870_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg___boxed(lean_object* v_origAltType_4887_, lean_object* v_altInfo_4888_, lean_object* v_k_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_4887_, v_altInfo_4888_, v_k_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
lean_dec(v___y_4891_);
lean_dec_ref(v___y_4890_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(lean_object* v___x_4896_, lean_object* v___x_4897_, lean_object* v___f_4898_, lean_object* v_fst_4899_, lean_object* v___x_4900_, lean_object* v___x_4901_, lean_object* v___x_4902_, lean_object* v___x_4903_, lean_object* v___x_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_){
_start:
{
lean_object* v___x_4910_; 
v___x_4910_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v___x_4896_, v___x_4897_, v___f_4898_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4925_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4913_ = v___x_4910_;
v_isShared_4914_ = v_isSharedCheck_4925_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4910_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4925_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4923_; 
v___x_4915_ = lean_array_push(v_fst_4899_, v_a_4911_);
v___x_4916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4900_);
lean_ctor_set(v___x_4916_, 1, v___x_4901_);
v___x_4917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4917_, 0, v___x_4902_);
lean_ctor_set(v___x_4917_, 1, v___x_4916_);
v___x_4918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4903_);
lean_ctor_set(v___x_4918_, 1, v___x_4917_);
v___x_4919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4919_, 0, v___x_4904_);
lean_ctor_set(v___x_4919_, 1, v___x_4918_);
v___x_4920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4920_, 0, v___x_4915_);
lean_ctor_set(v___x_4920_, 1, v___x_4919_);
v___x_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4921_, 0, v___x_4920_);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v___x_4921_);
v___x_4923_ = v___x_4913_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v___x_4921_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
lean_dec_ref(v___x_4904_);
lean_dec_ref(v___x_4903_);
lean_dec_ref(v___x_4902_);
lean_dec_ref(v___x_4901_);
lean_dec_ref(v___x_4900_);
lean_dec(v_fst_4899_);
v_a_4926_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4910_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4910_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed(lean_object* v___x_4934_, lean_object* v___x_4935_, lean_object* v___f_4936_, lean_object* v_fst_4937_, lean_object* v___x_4938_, lean_object* v___x_4939_, lean_object* v___x_4940_, lean_object* v___x_4941_, lean_object* v___x_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v_res_4948_; 
v_res_4948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4(v___x_4934_, v___x_4935_, v___f_4936_, v_fst_4937_, v___x_4938_, v___x_4939_, v___x_4940_, v___x_4941_, v___x_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
return v_res_4948_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0(void){
_start:
{
lean_object* v___x_4949_; 
v___x_4949_ = l_instMonadEIO(lean_box(0));
return v___x_4949_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(lean_object* v_msg_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v_toApplicative_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_5023_; 
v___x_4960_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
v___x_4961_ = l_StateRefT_x27_instMonad___redArg(v___x_4960_);
v_toApplicative_4962_ = lean_ctor_get(v___x_4961_, 0);
v_isSharedCheck_5023_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_5023_ == 0)
{
lean_object* v_unused_5024_; 
v_unused_5024_ = lean_ctor_get(v___x_4961_, 1);
lean_dec(v_unused_5024_);
v___x_4964_ = v___x_4961_;
v_isShared_4965_ = v_isSharedCheck_5023_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_toApplicative_4962_);
lean_dec(v___x_4961_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_5023_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v_toFunctor_4966_; lean_object* v_toSeq_4967_; lean_object* v_toSeqLeft_4968_; lean_object* v_toSeqRight_4969_; lean_object* v___x_4971_; uint8_t v_isShared_4972_; uint8_t v_isSharedCheck_5021_; 
v_toFunctor_4966_ = lean_ctor_get(v_toApplicative_4962_, 0);
v_toSeq_4967_ = lean_ctor_get(v_toApplicative_4962_, 2);
v_toSeqLeft_4968_ = lean_ctor_get(v_toApplicative_4962_, 3);
v_toSeqRight_4969_ = lean_ctor_get(v_toApplicative_4962_, 4);
v_isSharedCheck_5021_ = !lean_is_exclusive(v_toApplicative_4962_);
if (v_isSharedCheck_5021_ == 0)
{
lean_object* v_unused_5022_; 
v_unused_5022_ = lean_ctor_get(v_toApplicative_4962_, 1);
lean_dec(v_unused_5022_);
v___x_4971_ = v_toApplicative_4962_;
v_isShared_4972_ = v_isSharedCheck_5021_;
goto v_resetjp_4970_;
}
else
{
lean_inc(v_toSeqRight_4969_);
lean_inc(v_toSeqLeft_4968_);
lean_inc(v_toSeq_4967_);
lean_inc(v_toFunctor_4966_);
lean_dec(v_toApplicative_4962_);
v___x_4971_ = lean_box(0);
v_isShared_4972_ = v_isSharedCheck_5021_;
goto v_resetjp_4970_;
}
v_resetjp_4970_:
{
lean_object* v___f_4973_; lean_object* v___f_4974_; lean_object* v___f_4975_; lean_object* v___f_4976_; lean_object* v___x_4977_; lean_object* v___f_4978_; lean_object* v___f_4979_; lean_object* v___f_4980_; lean_object* v___x_4982_; 
v___f_4973_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_4974_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
lean_inc_ref(v_toFunctor_4966_);
v___f_4975_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4975_, 0, v_toFunctor_4966_);
v___f_4976_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4976_, 0, v_toFunctor_4966_);
v___x_4977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4977_, 0, v___f_4975_);
lean_ctor_set(v___x_4977_, 1, v___f_4976_);
v___f_4978_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_4978_, 0, v_toSeqRight_4969_);
v___f_4979_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_4979_, 0, v_toSeqLeft_4968_);
v___f_4980_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_4980_, 0, v_toSeq_4967_);
if (v_isShared_4972_ == 0)
{
lean_ctor_set(v___x_4971_, 4, v___f_4978_);
lean_ctor_set(v___x_4971_, 3, v___f_4979_);
lean_ctor_set(v___x_4971_, 2, v___f_4980_);
lean_ctor_set(v___x_4971_, 1, v___f_4973_);
lean_ctor_set(v___x_4971_, 0, v___x_4977_);
v___x_4982_ = v___x_4971_;
goto v_reusejp_4981_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_4977_);
lean_ctor_set(v_reuseFailAlloc_5020_, 1, v___f_4973_);
lean_ctor_set(v_reuseFailAlloc_5020_, 2, v___f_4980_);
lean_ctor_set(v_reuseFailAlloc_5020_, 3, v___f_4979_);
lean_ctor_set(v_reuseFailAlloc_5020_, 4, v___f_4978_);
v___x_4982_ = v_reuseFailAlloc_5020_;
goto v_reusejp_4981_;
}
v_reusejp_4981_:
{
lean_object* v___x_4984_; 
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 1, v___f_4974_);
lean_ctor_set(v___x_4964_, 0, v___x_4982_);
v___x_4984_ = v___x_4964_;
goto v_reusejp_4983_;
}
else
{
lean_object* v_reuseFailAlloc_5019_; 
v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5019_, 0, v___x_4982_);
lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___f_4974_);
v___x_4984_ = v_reuseFailAlloc_5019_;
goto v_reusejp_4983_;
}
v_reusejp_4983_:
{
lean_object* v___x_4985_; lean_object* v_toApplicative_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5017_; 
v___x_4985_ = l_StateRefT_x27_instMonad___redArg(v___x_4984_);
v_toApplicative_4986_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5017_ == 0)
{
lean_object* v_unused_5018_; 
v_unused_5018_ = lean_ctor_get(v___x_4985_, 1);
lean_dec(v_unused_5018_);
v___x_4988_ = v___x_4985_;
v_isShared_4989_ = v_isSharedCheck_5017_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_toApplicative_4986_);
lean_dec(v___x_4985_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5017_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v_toFunctor_4990_; lean_object* v_toSeq_4991_; lean_object* v_toSeqLeft_4992_; lean_object* v_toSeqRight_4993_; lean_object* v___x_4995_; uint8_t v_isShared_4996_; uint8_t v_isSharedCheck_5015_; 
v_toFunctor_4990_ = lean_ctor_get(v_toApplicative_4986_, 0);
v_toSeq_4991_ = lean_ctor_get(v_toApplicative_4986_, 2);
v_toSeqLeft_4992_ = lean_ctor_get(v_toApplicative_4986_, 3);
v_toSeqRight_4993_ = lean_ctor_get(v_toApplicative_4986_, 4);
v_isSharedCheck_5015_ = !lean_is_exclusive(v_toApplicative_4986_);
if (v_isSharedCheck_5015_ == 0)
{
lean_object* v_unused_5016_; 
v_unused_5016_ = lean_ctor_get(v_toApplicative_4986_, 1);
lean_dec(v_unused_5016_);
v___x_4995_ = v_toApplicative_4986_;
v_isShared_4996_ = v_isSharedCheck_5015_;
goto v_resetjp_4994_;
}
else
{
lean_inc(v_toSeqRight_4993_);
lean_inc(v_toSeqLeft_4992_);
lean_inc(v_toSeq_4991_);
lean_inc(v_toFunctor_4990_);
lean_dec(v_toApplicative_4986_);
v___x_4995_ = lean_box(0);
v_isShared_4996_ = v_isSharedCheck_5015_;
goto v_resetjp_4994_;
}
v_resetjp_4994_:
{
lean_object* v___f_4997_; lean_object* v___f_4998_; lean_object* v___f_4999_; lean_object* v___f_5000_; lean_object* v___x_5001_; lean_object* v___f_5002_; lean_object* v___f_5003_; lean_object* v___f_5004_; lean_object* v___x_5006_; 
v___f_4997_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_4998_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
lean_inc_ref(v_toFunctor_4990_);
v___f_4999_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_4999_, 0, v_toFunctor_4990_);
v___f_5000_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5000_, 0, v_toFunctor_4990_);
v___x_5001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5001_, 0, v___f_4999_);
lean_ctor_set(v___x_5001_, 1, v___f_5000_);
v___f_5002_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_5002_, 0, v_toSeqRight_4993_);
v___f_5003_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_5003_, 0, v_toSeqLeft_4992_);
v___f_5004_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_5004_, 0, v_toSeq_4991_);
if (v_isShared_4996_ == 0)
{
lean_ctor_set(v___x_4995_, 4, v___f_5002_);
lean_ctor_set(v___x_4995_, 3, v___f_5003_);
lean_ctor_set(v___x_4995_, 2, v___f_5004_);
lean_ctor_set(v___x_4995_, 1, v___f_4997_);
lean_ctor_set(v___x_4995_, 0, v___x_5001_);
v___x_5006_ = v___x_4995_;
goto v_reusejp_5005_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v___x_5001_);
lean_ctor_set(v_reuseFailAlloc_5014_, 1, v___f_4997_);
lean_ctor_set(v_reuseFailAlloc_5014_, 2, v___f_5004_);
lean_ctor_set(v_reuseFailAlloc_5014_, 3, v___f_5003_);
lean_ctor_set(v_reuseFailAlloc_5014_, 4, v___f_5002_);
v___x_5006_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5005_;
}
v_reusejp_5005_:
{
lean_object* v___x_5008_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v___f_4998_);
lean_ctor_set(v___x_4988_, 0, v___x_5006_);
v___x_5008_ = v___x_4988_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5013_; 
v_reuseFailAlloc_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5013_, 0, v___x_5006_);
lean_ctor_set(v_reuseFailAlloc_5013_, 1, v___f_4998_);
v___x_5008_ = v_reuseFailAlloc_5013_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_27531__overap_5011_; lean_object* v___x_5012_; 
v___x_5009_ = l_Lean_instInhabitedExpr;
v___x_5010_ = l_instInhabitedOfMonad___redArg(v___x_5008_, v___x_5009_);
v___x_27531__overap_5011_ = lean_panic_fn_borrowed(v___x_5010_, v_msg_4954_);
lean_dec(v___x_5010_);
lean_inc(v___y_4958_);
lean_inc_ref(v___y_4957_);
lean_inc(v___y_4956_);
lean_inc_ref(v___y_4955_);
v___x_5012_ = lean_apply_5(v___x_27531__overap_5011_, v___y_4955_, v___y_4956_, v___y_4957_, v___y_4958_, lean_box(0));
return v___x_5012_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___boxed(lean_object* v_msg_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v_msg_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
lean_dec(v___y_5027_);
lean_dec_ref(v___y_5026_);
return v_res_5031_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(lean_object* v_args_5032_, lean_object* v_ys_5033_, lean_object* v_ys2_5034_, lean_object* v_ys3_5035_, lean_object* v_onAlt_5036_, lean_object* v_a_5037_, uint8_t v___x_5038_, uint8_t v_useSplitter_5039_, lean_object* v___x_5040_, lean_object* v_ys4_5041_, lean_object* v_altType_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
lean_object* v___y_5049_; lean_object* v___x_5059_; lean_object* v___x_5060_; 
lean_inc_ref(v_args_5032_);
v___x_5059_ = l_Array_append___redArg(v_args_5032_, v_ys3_5035_);
v___x_5060_ = l_Lean_Meta_instantiateLambda(v___x_5040_, v___x_5059_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_);
lean_dec_ref(v___x_5059_);
if (lean_obj_tag(v___x_5060_) == 0)
{
v___y_5049_ = v___x_5060_;
goto v___jp_5048_;
}
else
{
lean_object* v_a_5061_; uint8_t v___y_5063_; uint8_t v___x_5066_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
v___x_5066_ = l_Lean_Exception_isInterrupt(v_a_5061_);
if (v___x_5066_ == 0)
{
uint8_t v___x_5067_; 
v___x_5067_ = l_Lean_Exception_isRuntime(v_a_5061_);
v___y_5063_ = v___x_5067_;
goto v___jp_5062_;
}
else
{
lean_dec(v_a_5061_);
v___y_5063_ = v___x_5066_;
goto v___jp_5062_;
}
v___jp_5062_:
{
if (v___y_5063_ == 0)
{
lean_object* v___x_5064_; lean_object* v___x_5065_; 
lean_dec_ref_known(v___x_5060_, 1);
v___x_5064_ = lean_obj_once(&l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2, &l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2_once, _init_l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts___lam__1___closed__2);
v___x_5065_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5064_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_);
v___y_5049_ = v___x_5065_;
goto v___jp_5048_;
}
else
{
v___y_5049_ = v___x_5060_;
goto v___jp_5048_;
}
}
}
v___jp_5048_:
{
if (lean_obj_tag(v___y_5049_) == 0)
{
lean_object* v_a_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v_a_5050_ = lean_ctor_get(v___y_5049_, 0);
lean_inc(v_a_5050_);
lean_dec_ref_known(v___y_5049_, 1);
lean_inc_ref(v_ys4_5041_);
lean_inc_ref(v_ys3_5035_);
lean_inc_ref(v_ys2_5034_);
lean_inc_ref(v_ys_5033_);
v___x_5051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5051_, 0, v_args_5032_);
lean_ctor_set(v___x_5051_, 1, v_ys_5033_);
lean_ctor_set(v___x_5051_, 2, v_ys2_5034_);
lean_ctor_set(v___x_5051_, 3, v_ys3_5035_);
lean_ctor_set(v___x_5051_, 4, v_ys4_5041_);
lean_inc(v___y_5046_);
lean_inc_ref(v___y_5045_);
lean_inc(v___y_5044_);
lean_inc_ref(v___y_5043_);
v___x_5052_ = lean_apply_9(v_onAlt_5036_, v_a_5037_, v_altType_5042_, v___x_5051_, v_a_5050_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, lean_box(0));
if (lean_obj_tag(v___x_5052_) == 0)
{
lean_object* v_a_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; uint8_t v___x_5057_; lean_object* v___x_5058_; 
v_a_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc(v_a_5053_);
lean_dec_ref_known(v___x_5052_, 1);
v___x_5054_ = l_Array_append___redArg(v_ys_5033_, v_ys2_5034_);
lean_dec_ref(v_ys2_5034_);
v___x_5055_ = l_Array_append___redArg(v___x_5054_, v_ys3_5035_);
lean_dec_ref(v_ys3_5035_);
v___x_5056_ = l_Array_append___redArg(v___x_5055_, v_ys4_5041_);
lean_dec_ref(v_ys4_5041_);
v___x_5057_ = 1;
v___x_5058_ = l_Lean_Meta_mkLambdaFVars(v___x_5056_, v_a_5053_, v___x_5038_, v_useSplitter_5039_, v___x_5038_, v_useSplitter_5039_, v___x_5057_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_);
lean_dec_ref(v___x_5056_);
return v___x_5058_;
}
else
{
lean_dec_ref(v_ys4_5041_);
lean_dec_ref(v_ys3_5035_);
lean_dec_ref(v_ys2_5034_);
lean_dec_ref(v_ys_5033_);
return v___x_5052_;
}
}
else
{
lean_dec_ref(v_altType_5042_);
lean_dec_ref(v_ys4_5041_);
lean_dec(v_a_5037_);
lean_dec_ref(v_onAlt_5036_);
lean_dec_ref(v_ys3_5035_);
lean_dec_ref(v_ys2_5034_);
lean_dec_ref(v_ys_5033_);
lean_dec_ref(v_args_5032_);
return v___y_5049_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed(lean_object* v_args_5068_, lean_object* v_ys_5069_, lean_object* v_ys2_5070_, lean_object* v_ys3_5071_, lean_object* v_onAlt_5072_, lean_object* v_a_5073_, lean_object* v___x_5074_, lean_object* v_useSplitter_5075_, lean_object* v___x_5076_, lean_object* v_ys4_5077_, lean_object* v_altType_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_, lean_object* v___y_5081_, lean_object* v___y_5082_, lean_object* v___y_5083_){
_start:
{
uint8_t v___x_33176__boxed_5084_; uint8_t v_useSplitter_boxed_5085_; lean_object* v_res_5086_; 
v___x_33176__boxed_5084_ = lean_unbox(v___x_5074_);
v_useSplitter_boxed_5085_ = lean_unbox(v_useSplitter_5075_);
v_res_5086_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5(v_args_5068_, v_ys_5069_, v_ys2_5070_, v_ys3_5071_, v_onAlt_5072_, v_a_5073_, v___x_33176__boxed_5084_, v_useSplitter_boxed_5085_, v___x_5076_, v_ys4_5077_, v_altType_5078_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
lean_dec(v___y_5082_);
lean_dec_ref(v___y_5081_);
lean_dec(v___y_5080_);
lean_dec_ref(v___y_5079_);
return v_res_5086_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(lean_object* v_args_5087_, lean_object* v_ys_5088_, lean_object* v_ys2_5089_, lean_object* v_onAlt_5090_, lean_object* v_a_5091_, uint8_t v___x_5092_, uint8_t v_useSplitter_5093_, lean_object* v___x_5094_, lean_object* v_extraEqualities_5095_, lean_object* v_ys3_5096_, lean_object* v_altType_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_){
_start:
{
lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___f_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5103_ = lean_box(v___x_5092_);
v___x_5104_ = lean_box(v_useSplitter_5093_);
v___f_5105_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__5___boxed), 16, 9);
lean_closure_set(v___f_5105_, 0, v_args_5087_);
lean_closure_set(v___f_5105_, 1, v_ys_5088_);
lean_closure_set(v___f_5105_, 2, v_ys2_5089_);
lean_closure_set(v___f_5105_, 3, v_ys3_5096_);
lean_closure_set(v___f_5105_, 4, v_onAlt_5090_);
lean_closure_set(v___f_5105_, 5, v_a_5091_);
lean_closure_set(v___f_5105_, 6, v___x_5103_);
lean_closure_set(v___f_5105_, 7, v___x_5104_);
lean_closure_set(v___f_5105_, 8, v___x_5094_);
v___x_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5106_, 0, v_extraEqualities_5095_);
v___x_5107_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5097_, v___x_5106_, v___f_5105_, v___x_5092_, v___x_5092_, v___y_5098_, v___y_5099_, v___y_5100_, v___y_5101_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed(lean_object* v_args_5108_, lean_object* v_ys_5109_, lean_object* v_ys2_5110_, lean_object* v_onAlt_5111_, lean_object* v_a_5112_, lean_object* v___x_5113_, lean_object* v_useSplitter_5114_, lean_object* v___x_5115_, lean_object* v_extraEqualities_5116_, lean_object* v_ys3_5117_, lean_object* v_altType_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
uint8_t v___x_33241__boxed_5124_; uint8_t v_useSplitter_boxed_5125_; lean_object* v_res_5126_; 
v___x_33241__boxed_5124_ = lean_unbox(v___x_5113_);
v_useSplitter_boxed_5125_ = lean_unbox(v_useSplitter_5114_);
v_res_5126_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1(v_args_5108_, v_ys_5109_, v_ys2_5110_, v_onAlt_5111_, v_a_5112_, v___x_33241__boxed_5124_, v_useSplitter_boxed_5125_, v___x_5115_, v_extraEqualities_5116_, v_ys3_5117_, v_altType_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_);
lean_dec(v___y_5122_);
lean_dec_ref(v___y_5121_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
return v_res_5126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(lean_object* v_args_5127_, lean_object* v_ys_5128_, lean_object* v_onAlt_5129_, lean_object* v_a_5130_, uint8_t v___x_5131_, uint8_t v_useSplitter_5132_, lean_object* v___x_5133_, lean_object* v_extraEqualities_5134_, lean_object* v_numDiscrEqs_5135_, lean_object* v_ys2_5136_, lean_object* v_altType_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_){
_start:
{
lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___f_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5143_ = lean_box(v___x_5131_);
v___x_5144_ = lean_box(v_useSplitter_5132_);
v___f_5145_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_5145_, 0, v_args_5127_);
lean_closure_set(v___f_5145_, 1, v_ys_5128_);
lean_closure_set(v___f_5145_, 2, v_ys2_5136_);
lean_closure_set(v___f_5145_, 3, v_onAlt_5129_);
lean_closure_set(v___f_5145_, 4, v_a_5130_);
lean_closure_set(v___f_5145_, 5, v___x_5143_);
lean_closure_set(v___f_5145_, 6, v___x_5144_);
lean_closure_set(v___f_5145_, 7, v___x_5133_);
lean_closure_set(v___f_5145_, 8, v_extraEqualities_5134_);
v___x_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5146_, 0, v_numDiscrEqs_5135_);
v___x_5147_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5137_, v___x_5146_, v___f_5145_, v___x_5131_, v___x_5131_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed(lean_object* v_args_5148_, lean_object* v_ys_5149_, lean_object* v_onAlt_5150_, lean_object* v_a_5151_, lean_object* v___x_5152_, lean_object* v_useSplitter_5153_, lean_object* v___x_5154_, lean_object* v_extraEqualities_5155_, lean_object* v_numDiscrEqs_5156_, lean_object* v_ys2_5157_, lean_object* v_altType_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
uint8_t v___x_33272__boxed_5164_; uint8_t v_useSplitter_boxed_5165_; lean_object* v_res_5166_; 
v___x_33272__boxed_5164_ = lean_unbox(v___x_5152_);
v_useSplitter_boxed_5165_ = lean_unbox(v_useSplitter_5153_);
v_res_5166_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2(v_args_5148_, v_ys_5149_, v_onAlt_5150_, v_a_5151_, v___x_33272__boxed_5164_, v_useSplitter_boxed_5165_, v___x_5154_, v_extraEqualities_5155_, v_numDiscrEqs_5156_, v_ys2_5157_, v_altType_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
return v_res_5166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(lean_object* v___x_5167_, lean_object* v___x_5168_, lean_object* v_onAlt_5169_, lean_object* v_a_5170_, uint8_t v___x_5171_, uint8_t v_useSplitter_5172_, lean_object* v___x_5173_, lean_object* v_extraEqualities_5174_, lean_object* v_numDiscrEqs_5175_, uint8_t v_hasUnitThunk_5176_, lean_object* v___x_5177_, lean_object* v_ys_5178_, lean_object* v_args_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
lean_object* v_numFields_5185_; lean_object* v_numOverlaps_5186_; uint8_t v_hasUnitThunk_5187_; lean_object* v___x_5188_; uint8_t v___x_5189_; 
v_numFields_5185_ = lean_ctor_get(v___x_5167_, 0);
v_numOverlaps_5186_ = lean_ctor_get(v___x_5167_, 1);
v_hasUnitThunk_5187_ = lean_ctor_get_uint8(v___x_5167_, sizeof(void*)*2);
v___x_5188_ = lean_array_get_size(v_ys_5178_);
v___x_5189_ = lean_nat_dec_eq(v___x_5188_, v_numFields_5185_);
if (v___x_5189_ == 0)
{
lean_object* v___x_5190_; lean_object* v___x_5191_; 
lean_dec_ref(v_args_5179_);
lean_dec_ref(v_ys_5178_);
lean_dec(v_numDiscrEqs_5175_);
lean_dec(v_extraEqualities_5174_);
lean_dec_ref(v___x_5173_);
lean_dec(v_a_5170_);
lean_dec_ref(v_onAlt_5169_);
lean_dec_ref(v___x_5168_);
v___x_5190_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__43___closed__3);
v___x_5191_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12(v___x_5190_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
return v___x_5191_;
}
else
{
lean_object* v___x_5192_; 
v___x_5192_ = l_Lean_Meta_instantiateForall(v___x_5168_, v_ys_5178_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
if (lean_obj_tag(v___x_5192_) == 0)
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5222_; 
v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
v_isSharedCheck_5222_ = !lean_is_exclusive(v___x_5192_);
if (v_isSharedCheck_5222_ == 0)
{
v___x_5195_ = v___x_5192_;
v_isShared_5196_ = v_isSharedCheck_5222_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5192_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5222_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___f_5199_; lean_object* v_altType_5201_; lean_object* v___y_5202_; lean_object* v___y_5203_; lean_object* v___y_5204_; lean_object* v___y_5205_; 
v___x_5197_ = lean_box(v___x_5171_);
v___x_5198_ = lean_box(v_useSplitter_5172_);
v___f_5199_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__2___boxed), 16, 9);
lean_closure_set(v___f_5199_, 0, v_args_5179_);
lean_closure_set(v___f_5199_, 1, v_ys_5178_);
lean_closure_set(v___f_5199_, 2, v_onAlt_5169_);
lean_closure_set(v___f_5199_, 3, v_a_5170_);
lean_closure_set(v___f_5199_, 4, v___x_5197_);
lean_closure_set(v___f_5199_, 5, v___x_5198_);
lean_closure_set(v___f_5199_, 6, v___x_5173_);
lean_closure_set(v___f_5199_, 7, v_extraEqualities_5174_);
lean_closure_set(v___f_5199_, 8, v_numDiscrEqs_5175_);
if (v_hasUnitThunk_5176_ == 0)
{
v_altType_5201_ = v_a_5193_;
v___y_5202_ = v___y_5180_;
v___y_5203_ = v___y_5181_;
v___y_5204_ = v___y_5182_;
v___y_5205_ = v___y_5183_;
goto v___jp_5200_;
}
else
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; 
v___x_5217_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2, &l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__44___closed__2);
v___x_5218_ = lean_mk_empty_array_with_capacity(v___x_5177_);
v___x_5219_ = lean_array_push(v___x_5218_, v___x_5217_);
v___x_5220_ = l_Lean_Meta_instantiateForall(v_a_5193_, v___x_5219_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
lean_dec_ref(v___x_5219_);
if (lean_obj_tag(v___x_5220_) == 0)
{
lean_object* v_a_5221_; 
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
lean_inc(v_a_5221_);
lean_dec_ref_known(v___x_5220_, 1);
v_altType_5201_ = v_a_5221_;
v___y_5202_ = v___y_5180_;
v___y_5203_ = v___y_5181_;
v___y_5204_ = v___y_5182_;
v___y_5205_ = v___y_5183_;
goto v___jp_5200_;
}
else
{
lean_dec_ref(v___f_5199_);
lean_del_object(v___x_5195_);
return v___x_5220_;
}
}
v___jp_5200_:
{
lean_object* v___x_5207_; 
lean_inc(v_numOverlaps_5186_);
if (v_isShared_5196_ == 0)
{
lean_ctor_set_tag(v___x_5195_, 1);
lean_ctor_set(v___x_5195_, 0, v_numOverlaps_5186_);
v___x_5207_ = v___x_5195_;
goto v_reusejp_5206_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_numOverlaps_5186_);
v___x_5207_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5206_;
}
v_reusejp_5206_:
{
lean_object* v___x_5208_; 
v___x_5208_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_5201_, v___x_5207_, v___f_5199_, v___x_5171_, v___x_5171_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
if (lean_obj_tag(v___x_5208_) == 0)
{
if (v_hasUnitThunk_5187_ == 0)
{
return v___x_5208_;
}
else
{
lean_object* v_a_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; 
v_a_5209_ = lean_ctor_get(v___x_5208_, 0);
lean_inc(v_a_5209_);
lean_dec_ref_known(v___x_5208_, 1);
v___x_5210_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__2));
v___x_5211_ = lean_unsigned_to_nat(2u);
v___x_5212_ = lean_mk_empty_array_with_capacity(v___x_5211_);
lean_dec_ref(v___x_5212_);
v___x_5213_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6, &l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__34___closed__6);
v___x_5214_ = lean_array_push(v___x_5213_, v_a_5209_);
v___x_5215_ = l_Lean_Meta_mkAppM(v___x_5210_, v___x_5214_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_);
return v___x_5215_;
}
}
else
{
return v___x_5208_;
}
}
}
}
}
else
{
lean_dec_ref(v_args_5179_);
lean_dec_ref(v_ys_5178_);
lean_dec(v_numDiscrEqs_5175_);
lean_dec(v_extraEqualities_5174_);
lean_dec_ref(v___x_5173_);
lean_dec(v_a_5170_);
lean_dec_ref(v_onAlt_5169_);
return v___x_5192_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed(lean_object** _args){
lean_object* v___x_5223_ = _args[0];
lean_object* v___x_5224_ = _args[1];
lean_object* v_onAlt_5225_ = _args[2];
lean_object* v_a_5226_ = _args[3];
lean_object* v___x_5227_ = _args[4];
lean_object* v_useSplitter_5228_ = _args[5];
lean_object* v___x_5229_ = _args[6];
lean_object* v_extraEqualities_5230_ = _args[7];
lean_object* v_numDiscrEqs_5231_ = _args[8];
lean_object* v_hasUnitThunk_5232_ = _args[9];
lean_object* v___x_5233_ = _args[10];
lean_object* v_ys_5234_ = _args[11];
lean_object* v_args_5235_ = _args[12];
lean_object* v___y_5236_ = _args[13];
lean_object* v___y_5237_ = _args[14];
lean_object* v___y_5238_ = _args[15];
lean_object* v___y_5239_ = _args[16];
lean_object* v___y_5240_ = _args[17];
_start:
{
uint8_t v___x_33337__boxed_5241_; uint8_t v_useSplitter_boxed_5242_; uint8_t v_hasUnitThunk_boxed_5243_; lean_object* v_res_5244_; 
v___x_33337__boxed_5241_ = lean_unbox(v___x_5227_);
v_useSplitter_boxed_5242_ = lean_unbox(v_useSplitter_5228_);
v_hasUnitThunk_boxed_5243_ = lean_unbox(v_hasUnitThunk_5232_);
v_res_5244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3(v___x_5223_, v___x_5224_, v_onAlt_5225_, v_a_5226_, v___x_33337__boxed_5241_, v_useSplitter_boxed_5242_, v___x_5229_, v_extraEqualities_5230_, v_numDiscrEqs_5231_, v_hasUnitThunk_boxed_5243_, v___x_5233_, v_ys_5234_, v_args_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v___x_5233_);
lean_dec_ref(v___x_5223_);
return v_res_5244_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(lean_object* v___x_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_){
_start:
{
lean_object* v___x_5251_; 
v___x_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5245_);
return v___x_5251_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed(lean_object* v___x_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
lean_object* v_res_5258_; 
v_res_5258_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0(v___x_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
return v_res_5258_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(lean_object* v_msg_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_){
_start:
{
lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v_toApplicative_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5328_; 
v___x_5265_ = lean_obj_once(&l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0, &l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0_once, _init_l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__0);
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
v___f_5278_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__1));
v___f_5279_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__2));
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
v___f_5302_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__3));
v___f_5303_ = ((lean_object*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__12___closed__4));
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
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_27519__overap_5316_; lean_object* v___x_5317_; 
v___x_5314_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__7);
v___x_5315_ = l_instInhabitedOfMonad___redArg(v___x_5313_, v___x_5314_);
v___x_27519__overap_5316_ = lean_panic_fn_borrowed(v___x_5315_, v_msg_5259_);
lean_dec(v___x_5315_);
lean_inc(v___y_5263_);
lean_inc_ref(v___y_5262_);
lean_inc(v___y_5261_);
lean_inc_ref(v___y_5260_);
v___x_5317_ = lean_apply_5(v___x_27519__overap_5316_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, lean_box(0));
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed(lean_object* v_msg_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_){
_start:
{
lean_object* v_res_5336_; 
v_res_5336_ = l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11(v_msg_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
return v_res_5336_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(lean_object* v_upperBound_5337_, lean_object* v_onAlt_5338_, uint8_t v_useSplitter_5339_, lean_object* v_extraEqualities_5340_, lean_object* v_numDiscrEqs_5341_, lean_object* v_a_5342_, lean_object* v_b_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v___y_5350_; uint8_t v___x_5373_; 
v___x_5373_ = lean_nat_dec_lt(v_a_5342_, v_upperBound_5337_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; 
lean_dec(v_a_5342_);
lean_dec(v_numDiscrEqs_5341_);
lean_dec(v_extraEqualities_5340_);
lean_dec_ref(v_onAlt_5338_);
v___x_5374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5374_, 0, v_b_5343_);
return v___x_5374_;
}
else
{
lean_object* v_snd_5375_; lean_object* v_snd_5376_; lean_object* v_snd_5377_; lean_object* v_snd_5378_; lean_object* v_snd_5379_; lean_object* v_fst_5380_; lean_object* v___x_5382_; uint8_t v_isShared_5383_; uint8_t v_isSharedCheck_5586_; 
v_snd_5375_ = lean_ctor_get(v_b_5343_, 1);
lean_inc(v_snd_5375_);
v_snd_5376_ = lean_ctor_get(v_snd_5375_, 1);
lean_inc(v_snd_5376_);
v_snd_5377_ = lean_ctor_get(v_snd_5376_, 1);
lean_inc(v_snd_5377_);
v_snd_5378_ = lean_ctor_get(v_snd_5377_, 1);
lean_inc(v_snd_5378_);
v_snd_5379_ = lean_ctor_get(v_snd_5378_, 1);
lean_inc(v_snd_5379_);
v_fst_5380_ = lean_ctor_get(v_b_5343_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v_b_5343_);
if (v_isSharedCheck_5586_ == 0)
{
lean_object* v_unused_5587_; 
v_unused_5587_ = lean_ctor_get(v_b_5343_, 1);
lean_dec(v_unused_5587_);
v___x_5382_ = v_b_5343_;
v_isShared_5383_ = v_isSharedCheck_5586_;
goto v_resetjp_5381_;
}
else
{
lean_inc(v_fst_5380_);
lean_dec(v_b_5343_);
v___x_5382_ = lean_box(0);
v_isShared_5383_ = v_isSharedCheck_5586_;
goto v_resetjp_5381_;
}
v_resetjp_5381_:
{
lean_object* v_fst_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5584_; 
v_fst_5384_ = lean_ctor_get(v_snd_5375_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v_snd_5375_);
if (v_isSharedCheck_5584_ == 0)
{
lean_object* v_unused_5585_; 
v_unused_5585_ = lean_ctor_get(v_snd_5375_, 1);
lean_dec(v_unused_5585_);
v___x_5386_ = v_snd_5375_;
v_isShared_5387_ = v_isSharedCheck_5584_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_fst_5384_);
lean_dec(v_snd_5375_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5584_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v_fst_5388_; lean_object* v___x_5390_; uint8_t v_isShared_5391_; uint8_t v_isSharedCheck_5582_; 
v_fst_5388_ = lean_ctor_get(v_snd_5376_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v_snd_5376_);
if (v_isSharedCheck_5582_ == 0)
{
lean_object* v_unused_5583_; 
v_unused_5583_ = lean_ctor_get(v_snd_5376_, 1);
lean_dec(v_unused_5583_);
v___x_5390_ = v_snd_5376_;
v_isShared_5391_ = v_isSharedCheck_5582_;
goto v_resetjp_5389_;
}
else
{
lean_inc(v_fst_5388_);
lean_dec(v_snd_5376_);
v___x_5390_ = lean_box(0);
v_isShared_5391_ = v_isSharedCheck_5582_;
goto v_resetjp_5389_;
}
v_resetjp_5389_:
{
lean_object* v_fst_5392_; lean_object* v___x_5394_; uint8_t v_isShared_5395_; uint8_t v_isSharedCheck_5580_; 
v_fst_5392_ = lean_ctor_get(v_snd_5377_, 0);
v_isSharedCheck_5580_ = !lean_is_exclusive(v_snd_5377_);
if (v_isSharedCheck_5580_ == 0)
{
lean_object* v_unused_5581_; 
v_unused_5581_ = lean_ctor_get(v_snd_5377_, 1);
lean_dec(v_unused_5581_);
v___x_5394_ = v_snd_5377_;
v_isShared_5395_ = v_isSharedCheck_5580_;
goto v_resetjp_5393_;
}
else
{
lean_inc(v_fst_5392_);
lean_dec(v_snd_5377_);
v___x_5394_ = lean_box(0);
v_isShared_5395_ = v_isSharedCheck_5580_;
goto v_resetjp_5393_;
}
v_resetjp_5393_:
{
lean_object* v_fst_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5578_; 
v_fst_5396_ = lean_ctor_get(v_snd_5378_, 0);
v_isSharedCheck_5578_ = !lean_is_exclusive(v_snd_5378_);
if (v_isSharedCheck_5578_ == 0)
{
lean_object* v_unused_5579_; 
v_unused_5579_ = lean_ctor_get(v_snd_5378_, 1);
lean_dec(v_unused_5579_);
v___x_5398_ = v_snd_5378_;
v_isShared_5399_ = v_isSharedCheck_5578_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_fst_5396_);
lean_dec(v_snd_5378_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5578_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v_array_5400_; lean_object* v_start_5401_; lean_object* v_stop_5402_; uint8_t v___x_5403_; 
v_array_5400_ = lean_ctor_get(v_snd_5379_, 0);
v_start_5401_ = lean_ctor_get(v_snd_5379_, 1);
v_stop_5402_ = lean_ctor_get(v_snd_5379_, 2);
v___x_5403_ = lean_nat_dec_lt(v_start_5401_, v_stop_5402_);
if (v___x_5403_ == 0)
{
lean_object* v___x_5405_; 
if (v_isShared_5399_ == 0)
{
v___x_5405_ = v___x_5398_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_fst_5396_);
lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_snd_5379_);
v___x_5405_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
lean_object* v___x_5407_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5405_);
v___x_5407_ = v___x_5394_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v___x_5405_);
v___x_5407_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
lean_object* v___x_5409_; 
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 1, v___x_5407_);
v___x_5409_ = v___x_5390_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v_fst_5388_);
lean_ctor_set(v_reuseFailAlloc_5418_, 1, v___x_5407_);
v___x_5409_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5411_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 1, v___x_5409_);
v___x_5411_ = v___x_5386_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_fst_5384_);
lean_ctor_set(v_reuseFailAlloc_5417_, 1, v___x_5409_);
v___x_5411_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
lean_object* v___x_5413_; 
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 1, v___x_5411_);
v___x_5413_ = v___x_5382_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v_fst_5380_);
lean_ctor_set(v_reuseFailAlloc_5416_, 1, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
lean_object* v___x_5414_; lean_object* v___f_5415_; 
v___x_5414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5413_);
v___f_5415_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5415_, 0, v___x_5414_);
v___y_5350_ = v___f_5415_;
goto v___jp_5349_;
}
}
}
}
}
}
else
{
lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5574_; 
lean_inc(v_stop_5402_);
lean_inc(v_start_5401_);
lean_inc_ref(v_array_5400_);
v_isSharedCheck_5574_ = !lean_is_exclusive(v_snd_5379_);
if (v_isSharedCheck_5574_ == 0)
{
lean_object* v_unused_5575_; lean_object* v_unused_5576_; lean_object* v_unused_5577_; 
v_unused_5575_ = lean_ctor_get(v_snd_5379_, 2);
lean_dec(v_unused_5575_);
v_unused_5576_ = lean_ctor_get(v_snd_5379_, 1);
lean_dec(v_unused_5576_);
v_unused_5577_ = lean_ctor_get(v_snd_5379_, 0);
lean_dec(v_unused_5577_);
v___x_5422_ = v_snd_5379_;
v_isShared_5423_ = v_isSharedCheck_5574_;
goto v_resetjp_5421_;
}
else
{
lean_dec(v_snd_5379_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5574_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v_array_5424_; lean_object* v_start_5425_; lean_object* v_stop_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; lean_object* v___x_5429_; lean_object* v___x_5431_; 
v_array_5424_ = lean_ctor_get(v_fst_5396_, 0);
v_start_5425_ = lean_ctor_get(v_fst_5396_, 1);
v_stop_5426_ = lean_ctor_get(v_fst_5396_, 2);
v___x_5427_ = lean_array_fget(v_array_5400_, v_start_5401_);
v___x_5428_ = lean_unsigned_to_nat(1u);
v___x_5429_ = lean_nat_add(v_start_5401_, v___x_5428_);
lean_dec(v_start_5401_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 1, v___x_5429_);
v___x_5431_ = v___x_5422_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v_array_5400_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v___x_5429_);
lean_ctor_set(v_reuseFailAlloc_5573_, 2, v_stop_5402_);
v___x_5431_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
uint8_t v___x_5432_; 
v___x_5432_ = lean_nat_dec_lt(v_start_5425_, v_stop_5426_);
if (v___x_5432_ == 0)
{
lean_object* v___x_5434_; 
lean_dec(v___x_5427_);
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5431_);
v___x_5434_ = v___x_5398_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_fst_5396_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v___x_5431_);
v___x_5434_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5436_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5434_);
v___x_5436_ = v___x_5394_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v___x_5434_);
v___x_5436_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
lean_object* v___x_5438_; 
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 1, v___x_5436_);
v___x_5438_ = v___x_5390_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_fst_5388_);
lean_ctor_set(v_reuseFailAlloc_5447_, 1, v___x_5436_);
v___x_5438_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
lean_object* v___x_5440_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 1, v___x_5438_);
v___x_5440_ = v___x_5386_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_fst_5384_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v___x_5438_);
v___x_5440_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
lean_object* v___x_5442_; 
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 1, v___x_5440_);
v___x_5442_ = v___x_5382_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_fst_5380_);
lean_ctor_set(v_reuseFailAlloc_5445_, 1, v___x_5440_);
v___x_5442_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
lean_object* v___x_5443_; lean_object* v___f_5444_; 
v___x_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
v___f_5444_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5444_, 0, v___x_5443_);
v___y_5350_ = v___f_5444_;
goto v___jp_5349_;
}
}
}
}
}
}
else
{
lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5569_; 
lean_inc(v_stop_5426_);
lean_inc(v_start_5425_);
lean_inc_ref(v_array_5424_);
v_isSharedCheck_5569_ = !lean_is_exclusive(v_fst_5396_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; lean_object* v_unused_5571_; lean_object* v_unused_5572_; 
v_unused_5570_ = lean_ctor_get(v_fst_5396_, 2);
lean_dec(v_unused_5570_);
v_unused_5571_ = lean_ctor_get(v_fst_5396_, 1);
lean_dec(v_unused_5571_);
v_unused_5572_ = lean_ctor_get(v_fst_5396_, 0);
lean_dec(v_unused_5572_);
v___x_5451_ = v_fst_5396_;
v_isShared_5452_ = v_isSharedCheck_5569_;
goto v_resetjp_5450_;
}
else
{
lean_dec(v_fst_5396_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5569_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v_array_5453_; lean_object* v_start_5454_; lean_object* v_stop_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; lean_object* v___x_5459_; 
v_array_5453_ = lean_ctor_get(v_fst_5392_, 0);
v_start_5454_ = lean_ctor_get(v_fst_5392_, 1);
v_stop_5455_ = lean_ctor_get(v_fst_5392_, 2);
v___x_5456_ = lean_array_fget(v_array_5424_, v_start_5425_);
v___x_5457_ = lean_nat_add(v_start_5425_, v___x_5428_);
lean_dec(v_start_5425_);
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 1, v___x_5457_);
v___x_5459_ = v___x_5451_;
goto v_reusejp_5458_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_array_5424_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v___x_5457_);
lean_ctor_set(v_reuseFailAlloc_5568_, 2, v_stop_5426_);
v___x_5459_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5458_;
}
v_reusejp_5458_:
{
uint8_t v___x_5460_; 
v___x_5460_ = lean_nat_dec_lt(v_start_5454_, v_stop_5455_);
if (v___x_5460_ == 0)
{
lean_object* v___x_5462_; 
lean_dec(v___x_5456_);
lean_dec(v___x_5427_);
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5431_);
lean_ctor_set(v___x_5398_, 0, v___x_5459_);
v___x_5462_ = v___x_5398_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5477_, 1, v___x_5431_);
v___x_5462_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
lean_object* v___x_5464_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5462_);
v___x_5464_ = v___x_5394_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_fst_5392_);
lean_ctor_set(v_reuseFailAlloc_5476_, 1, v___x_5462_);
v___x_5464_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
lean_object* v___x_5466_; 
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 1, v___x_5464_);
v___x_5466_ = v___x_5390_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_fst_5388_);
lean_ctor_set(v_reuseFailAlloc_5475_, 1, v___x_5464_);
v___x_5466_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
lean_object* v___x_5468_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 1, v___x_5466_);
v___x_5468_ = v___x_5386_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_fst_5384_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v___x_5466_);
v___x_5468_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5470_; 
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 1, v___x_5468_);
v___x_5470_ = v___x_5382_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_fst_5380_);
lean_ctor_set(v_reuseFailAlloc_5473_, 1, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
lean_object* v___x_5471_; lean_object* v___f_5472_; 
v___x_5471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5471_, 0, v___x_5470_);
v___f_5472_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5472_, 0, v___x_5471_);
v___y_5350_ = v___f_5472_;
goto v___jp_5349_;
}
}
}
}
}
}
else
{
lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5564_; 
lean_inc(v_stop_5455_);
lean_inc(v_start_5454_);
lean_inc_ref(v_array_5453_);
v_isSharedCheck_5564_ = !lean_is_exclusive(v_fst_5392_);
if (v_isSharedCheck_5564_ == 0)
{
lean_object* v_unused_5565_; lean_object* v_unused_5566_; lean_object* v_unused_5567_; 
v_unused_5565_ = lean_ctor_get(v_fst_5392_, 2);
lean_dec(v_unused_5565_);
v_unused_5566_ = lean_ctor_get(v_fst_5392_, 1);
lean_dec(v_unused_5566_);
v_unused_5567_ = lean_ctor_get(v_fst_5392_, 0);
lean_dec(v_unused_5567_);
v___x_5479_ = v_fst_5392_;
v_isShared_5480_ = v_isSharedCheck_5564_;
goto v_resetjp_5478_;
}
else
{
lean_dec(v_fst_5392_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5564_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v_array_5481_; lean_object* v_start_5482_; lean_object* v_stop_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5487_; 
v_array_5481_ = lean_ctor_get(v_fst_5388_, 0);
v_start_5482_ = lean_ctor_get(v_fst_5388_, 1);
v_stop_5483_ = lean_ctor_get(v_fst_5388_, 2);
v___x_5484_ = lean_array_fget(v_array_5453_, v_start_5454_);
v___x_5485_ = lean_nat_add(v_start_5454_, v___x_5428_);
lean_dec(v_start_5454_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 1, v___x_5485_);
v___x_5487_ = v___x_5479_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v_array_5453_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v___x_5485_);
lean_ctor_set(v_reuseFailAlloc_5563_, 2, v_stop_5455_);
v___x_5487_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
uint8_t v___x_5488_; 
v___x_5488_ = lean_nat_dec_lt(v_start_5482_, v_stop_5483_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5490_; 
lean_dec(v___x_5484_);
lean_dec(v___x_5456_);
lean_dec(v___x_5427_);
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5431_);
lean_ctor_set(v___x_5398_, 0, v___x_5459_);
v___x_5490_ = v___x_5398_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v___x_5431_);
v___x_5490_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5492_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5490_);
lean_ctor_set(v___x_5394_, 0, v___x_5487_);
v___x_5492_ = v___x_5394_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v___x_5487_);
lean_ctor_set(v_reuseFailAlloc_5504_, 1, v___x_5490_);
v___x_5492_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
lean_object* v___x_5494_; 
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 1, v___x_5492_);
v___x_5494_ = v___x_5390_;
goto v_reusejp_5493_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v_fst_5388_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v___x_5492_);
v___x_5494_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5493_;
}
v_reusejp_5493_:
{
lean_object* v___x_5496_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 1, v___x_5494_);
v___x_5496_ = v___x_5386_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_fst_5384_);
lean_ctor_set(v_reuseFailAlloc_5502_, 1, v___x_5494_);
v___x_5496_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
lean_object* v___x_5498_; 
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 1, v___x_5496_);
v___x_5498_ = v___x_5382_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v_fst_5380_);
lean_ctor_set(v_reuseFailAlloc_5501_, 1, v___x_5496_);
v___x_5498_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
lean_object* v___x_5499_; lean_object* v___f_5500_; 
v___x_5499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5498_);
v___f_5500_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5500_, 0, v___x_5499_);
v___y_5350_ = v___f_5500_;
goto v___jp_5349_;
}
}
}
}
}
}
else
{
lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5559_; 
lean_inc(v_stop_5483_);
lean_inc(v_start_5482_);
lean_inc_ref(v_array_5481_);
v_isSharedCheck_5559_ = !lean_is_exclusive(v_fst_5388_);
if (v_isSharedCheck_5559_ == 0)
{
lean_object* v_unused_5560_; lean_object* v_unused_5561_; lean_object* v_unused_5562_; 
v_unused_5560_ = lean_ctor_get(v_fst_5388_, 2);
lean_dec(v_unused_5560_);
v_unused_5561_ = lean_ctor_get(v_fst_5388_, 1);
lean_dec(v_unused_5561_);
v_unused_5562_ = lean_ctor_get(v_fst_5388_, 0);
lean_dec(v_unused_5562_);
v___x_5507_ = v_fst_5388_;
v_isShared_5508_ = v_isSharedCheck_5559_;
goto v_resetjp_5506_;
}
else
{
lean_dec(v_fst_5388_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5559_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v_array_5509_; lean_object* v_start_5510_; lean_object* v_stop_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5515_; 
v_array_5509_ = lean_ctor_get(v_fst_5384_, 0);
v_start_5510_ = lean_ctor_get(v_fst_5384_, 1);
v_stop_5511_ = lean_ctor_get(v_fst_5384_, 2);
v___x_5512_ = lean_array_fget(v_array_5481_, v_start_5482_);
v___x_5513_ = lean_nat_add(v_start_5482_, v___x_5428_);
lean_dec(v_start_5482_);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 1, v___x_5513_);
v___x_5515_ = v___x_5507_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v_array_5481_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v___x_5513_);
lean_ctor_set(v_reuseFailAlloc_5558_, 2, v_stop_5483_);
v___x_5515_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
uint8_t v___x_5516_; 
v___x_5516_ = lean_nat_dec_lt(v_start_5510_, v_stop_5511_);
if (v___x_5516_ == 0)
{
lean_object* v___x_5518_; 
lean_dec(v___x_5512_);
lean_dec(v___x_5484_);
lean_dec(v___x_5456_);
lean_dec(v___x_5427_);
if (v_isShared_5399_ == 0)
{
lean_ctor_set(v___x_5398_, 1, v___x_5431_);
lean_ctor_set(v___x_5398_, 0, v___x_5459_);
v___x_5518_ = v___x_5398_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5533_, 1, v___x_5431_);
v___x_5518_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
lean_object* v___x_5520_; 
if (v_isShared_5395_ == 0)
{
lean_ctor_set(v___x_5394_, 1, v___x_5518_);
lean_ctor_set(v___x_5394_, 0, v___x_5487_);
v___x_5520_ = v___x_5394_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v___x_5487_);
lean_ctor_set(v_reuseFailAlloc_5532_, 1, v___x_5518_);
v___x_5520_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
lean_object* v___x_5522_; 
if (v_isShared_5391_ == 0)
{
lean_ctor_set(v___x_5390_, 1, v___x_5520_);
lean_ctor_set(v___x_5390_, 0, v___x_5515_);
v___x_5522_ = v___x_5390_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v___x_5515_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v___x_5520_);
v___x_5522_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
lean_object* v___x_5524_; 
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 1, v___x_5522_);
v___x_5524_ = v___x_5386_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_fst_5384_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v___x_5522_);
v___x_5524_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
lean_object* v___x_5526_; 
if (v_isShared_5383_ == 0)
{
lean_ctor_set(v___x_5382_, 1, v___x_5524_);
v___x_5526_ = v___x_5382_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v_fst_5380_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v___x_5524_);
v___x_5526_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
lean_object* v___x_5527_; lean_object* v___f_5528_; 
v___x_5527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5527_, 0, v___x_5526_);
v___f_5528_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5528_, 0, v___x_5527_);
v___y_5350_ = v___f_5528_;
goto v___jp_5349_;
}
}
}
}
}
}
else
{
lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5554_; 
lean_inc(v_stop_5511_);
lean_inc(v_start_5510_);
lean_inc_ref(v_array_5509_);
lean_del_object(v___x_5398_);
lean_del_object(v___x_5394_);
lean_del_object(v___x_5390_);
lean_del_object(v___x_5386_);
lean_del_object(v___x_5382_);
v_isSharedCheck_5554_ = !lean_is_exclusive(v_fst_5384_);
if (v_isSharedCheck_5554_ == 0)
{
lean_object* v_unused_5555_; lean_object* v_unused_5556_; lean_object* v_unused_5557_; 
v_unused_5555_ = lean_ctor_get(v_fst_5384_, 2);
lean_dec(v_unused_5555_);
v_unused_5556_ = lean_ctor_get(v_fst_5384_, 1);
lean_dec(v_unused_5556_);
v_unused_5557_ = lean_ctor_get(v_fst_5384_, 0);
lean_dec(v_unused_5557_);
v___x_5535_ = v_fst_5384_;
v_isShared_5536_ = v_isSharedCheck_5554_;
goto v_resetjp_5534_;
}
else
{
lean_dec(v_fst_5384_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5554_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v_numOverlaps_5537_; uint8_t v_hasUnitThunk_5538_; lean_object* v___x_5539_; uint8_t v___x_5540_; 
v_numOverlaps_5537_ = lean_ctor_get(v___x_5512_, 1);
v_hasUnitThunk_5538_ = lean_ctor_get_uint8(v___x_5512_, sizeof(void*)*2);
v___x_5539_ = lean_unsigned_to_nat(0u);
v___x_5540_ = lean_nat_dec_eq(v_numOverlaps_5537_, v___x_5539_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5541_; lean_object* v___x_5542_; 
lean_del_object(v___x_5535_);
lean_dec_ref(v___x_5515_);
lean_dec(v___x_5512_);
lean_dec(v_stop_5511_);
lean_dec(v_start_5510_);
lean_dec_ref(v_array_5509_);
lean_dec_ref(v___x_5487_);
lean_dec(v___x_5484_);
lean_dec_ref(v___x_5459_);
lean_dec(v___x_5456_);
lean_dec_ref(v___x_5431_);
lean_dec(v___x_5427_);
lean_dec(v_fst_5380_);
v___x_5541_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9, &l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__46___closed__9);
v___x_5542_ = lean_alloc_closure((void*)(l_panic___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__11___boxed), 6, 1);
lean_closure_set(v___x_5542_, 0, v___x_5541_);
v___y_5350_ = v___x_5542_;
goto v___jp_5349_;
}
else
{
uint8_t v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___f_5548_; lean_object* v___x_5549_; lean_object* v___x_5551_; 
v___x_5543_ = 0;
v___x_5544_ = lean_array_fget_borrowed(v_array_5509_, v_start_5510_);
v___x_5545_ = lean_box(v___x_5543_);
v___x_5546_ = lean_box(v_useSplitter_5339_);
v___x_5547_ = lean_box(v_hasUnitThunk_5538_);
lean_inc(v_numDiscrEqs_5341_);
lean_inc(v_extraEqualities_5340_);
lean_inc(v___x_5544_);
lean_inc(v_a_5342_);
lean_inc_ref(v_onAlt_5338_);
v___f_5548_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__3___boxed), 18, 11);
lean_closure_set(v___f_5548_, 0, v___x_5484_);
lean_closure_set(v___f_5548_, 1, v___x_5427_);
lean_closure_set(v___f_5548_, 2, v_onAlt_5338_);
lean_closure_set(v___f_5548_, 3, v_a_5342_);
lean_closure_set(v___f_5548_, 4, v___x_5545_);
lean_closure_set(v___f_5548_, 5, v___x_5546_);
lean_closure_set(v___f_5548_, 6, v___x_5544_);
lean_closure_set(v___f_5548_, 7, v_extraEqualities_5340_);
lean_closure_set(v___f_5548_, 8, v_numDiscrEqs_5341_);
lean_closure_set(v___f_5548_, 9, v___x_5547_);
lean_closure_set(v___f_5548_, 10, v___x_5428_);
v___x_5549_ = lean_nat_add(v_start_5510_, v___x_5428_);
lean_dec(v_start_5510_);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 1, v___x_5549_);
v___x_5551_ = v___x_5535_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_array_5509_);
lean_ctor_set(v_reuseFailAlloc_5553_, 1, v___x_5549_);
lean_ctor_set(v_reuseFailAlloc_5553_, 2, v_stop_5511_);
v___x_5551_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
lean_object* v___f_5552_; 
v___f_5552_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___lam__4___boxed), 14, 9);
lean_closure_set(v___f_5552_, 0, v___x_5456_);
lean_closure_set(v___f_5552_, 1, v___x_5512_);
lean_closure_set(v___f_5552_, 2, v___f_5548_);
lean_closure_set(v___f_5552_, 3, v_fst_5380_);
lean_closure_set(v___f_5552_, 4, v___x_5459_);
lean_closure_set(v___f_5552_, 5, v___x_5431_);
lean_closure_set(v___f_5552_, 6, v___x_5487_);
lean_closure_set(v___f_5552_, 7, v___x_5515_);
lean_closure_set(v___f_5552_, 8, v___x_5551_);
v___y_5350_ = v___f_5552_;
goto v___jp_5349_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5349_:
{
lean_object* v___x_5351_; 
lean_inc(v___y_5347_);
lean_inc_ref(v___y_5346_);
lean_inc(v___y_5345_);
lean_inc_ref(v___y_5344_);
v___x_5351_ = lean_apply_5(v___y_5350_, v___y_5344_, v___y_5345_, v___y_5346_, v___y_5347_, lean_box(0));
if (lean_obj_tag(v___x_5351_) == 0)
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5364_; 
v_a_5352_ = lean_ctor_get(v___x_5351_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5354_ = v___x_5351_;
v_isShared_5355_ = v_isSharedCheck_5364_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5351_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5364_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
if (lean_obj_tag(v_a_5352_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5358_; 
lean_dec(v_a_5342_);
lean_dec(v_numDiscrEqs_5341_);
lean_dec(v_extraEqualities_5340_);
lean_dec_ref(v_onAlt_5338_);
v_a_5356_ = lean_ctor_get(v_a_5352_, 0);
lean_inc(v_a_5356_);
lean_dec_ref_known(v_a_5352_, 1);
if (v_isShared_5355_ == 0)
{
lean_ctor_set(v___x_5354_, 0, v_a_5356_);
v___x_5358_ = v___x_5354_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5359_; 
v_reuseFailAlloc_5359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5359_, 0, v_a_5356_);
v___x_5358_ = v_reuseFailAlloc_5359_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
return v___x_5358_;
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5361_; lean_object* v___x_5362_; 
lean_del_object(v___x_5354_);
v_a_5360_ = lean_ctor_get(v_a_5352_, 0);
lean_inc(v_a_5360_);
lean_dec_ref_known(v_a_5352_, 1);
v___x_5361_ = lean_unsigned_to_nat(1u);
v___x_5362_ = lean_nat_add(v_a_5342_, v___x_5361_);
lean_dec(v_a_5342_);
v_a_5342_ = v___x_5362_;
v_b_5343_ = v_a_5360_;
goto _start;
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec(v_a_5342_);
lean_dec(v_numDiscrEqs_5341_);
lean_dec(v_extraEqualities_5340_);
lean_dec_ref(v_onAlt_5338_);
v_a_5365_ = lean_ctor_get(v___x_5351_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5351_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5351_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5351_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg___boxed(lean_object* v_upperBound_5588_, lean_object* v_onAlt_5589_, lean_object* v_useSplitter_5590_, lean_object* v_extraEqualities_5591_, lean_object* v_numDiscrEqs_5592_, lean_object* v_a_5593_, lean_object* v_b_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_){
_start:
{
uint8_t v_useSplitter_boxed_5600_; lean_object* v_res_5601_; 
v_useSplitter_boxed_5600_ = lean_unbox(v_useSplitter_5590_);
v_res_5601_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_5588_, v_onAlt_5589_, v_useSplitter_boxed_5600_, v_extraEqualities_5591_, v_numDiscrEqs_5592_, v_a_5593_, v_b_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
lean_dec(v___y_5598_);
lean_dec_ref(v___y_5597_);
lean_dec(v___y_5596_);
lean_dec_ref(v___y_5595_);
lean_dec(v_upperBound_5588_);
return v_res_5601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(uint8_t v_addEqualities_5602_, lean_object* v_as_5603_, size_t v_sz_5604_, size_t v_i_5605_, lean_object* v_b_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_){
_start:
{
lean_object* v_a_5613_; uint8_t v___x_5617_; 
v___x_5617_ = lean_usize_dec_lt(v_i_5605_, v_sz_5604_);
if (v___x_5617_ == 0)
{
lean_object* v___x_5618_; 
v___x_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5618_, 0, v_b_5606_);
return v___x_5618_;
}
else
{
lean_object* v_snd_5619_; lean_object* v_snd_5620_; lean_object* v_snd_5621_; lean_object* v_snd_5622_; lean_object* v_fst_5623_; lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5769_; 
v_snd_5619_ = lean_ctor_get(v_b_5606_, 1);
lean_inc(v_snd_5619_);
v_snd_5620_ = lean_ctor_get(v_snd_5619_, 1);
lean_inc(v_snd_5620_);
v_snd_5621_ = lean_ctor_get(v_snd_5620_, 1);
lean_inc(v_snd_5621_);
v_snd_5622_ = lean_ctor_get(v_snd_5621_, 1);
lean_inc(v_snd_5622_);
v_fst_5623_ = lean_ctor_get(v_b_5606_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v_b_5606_);
if (v_isSharedCheck_5769_ == 0)
{
lean_object* v_unused_5770_; 
v_unused_5770_ = lean_ctor_get(v_b_5606_, 1);
lean_dec(v_unused_5770_);
v___x_5625_ = v_b_5606_;
v_isShared_5626_ = v_isSharedCheck_5769_;
goto v_resetjp_5624_;
}
else
{
lean_inc(v_fst_5623_);
lean_dec(v_b_5606_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5769_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v_fst_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5767_; 
v_fst_5627_ = lean_ctor_get(v_snd_5619_, 0);
v_isSharedCheck_5767_ = !lean_is_exclusive(v_snd_5619_);
if (v_isSharedCheck_5767_ == 0)
{
lean_object* v_unused_5768_; 
v_unused_5768_ = lean_ctor_get(v_snd_5619_, 1);
lean_dec(v_unused_5768_);
v___x_5629_ = v_snd_5619_;
v_isShared_5630_ = v_isSharedCheck_5767_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_fst_5627_);
lean_dec(v_snd_5619_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5767_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v_fst_5631_; lean_object* v___x_5633_; uint8_t v_isShared_5634_; uint8_t v_isSharedCheck_5765_; 
v_fst_5631_ = lean_ctor_get(v_snd_5620_, 0);
v_isSharedCheck_5765_ = !lean_is_exclusive(v_snd_5620_);
if (v_isSharedCheck_5765_ == 0)
{
lean_object* v_unused_5766_; 
v_unused_5766_ = lean_ctor_get(v_snd_5620_, 1);
lean_dec(v_unused_5766_);
v___x_5633_ = v_snd_5620_;
v_isShared_5634_ = v_isSharedCheck_5765_;
goto v_resetjp_5632_;
}
else
{
lean_inc(v_fst_5631_);
lean_dec(v_snd_5620_);
v___x_5633_ = lean_box(0);
v_isShared_5634_ = v_isSharedCheck_5765_;
goto v_resetjp_5632_;
}
v_resetjp_5632_:
{
lean_object* v_fst_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5763_; 
v_fst_5635_ = lean_ctor_get(v_snd_5621_, 0);
v_isSharedCheck_5763_ = !lean_is_exclusive(v_snd_5621_);
if (v_isSharedCheck_5763_ == 0)
{
lean_object* v_unused_5764_; 
v_unused_5764_ = lean_ctor_get(v_snd_5621_, 1);
lean_dec(v_unused_5764_);
v___x_5637_ = v_snd_5621_;
v_isShared_5638_ = v_isSharedCheck_5763_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_fst_5635_);
lean_dec(v_snd_5621_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5763_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v_array_5639_; lean_object* v_start_5640_; lean_object* v_stop_5641_; uint8_t v___x_5642_; 
v_array_5639_ = lean_ctor_get(v_snd_5622_, 0);
v_start_5640_ = lean_ctor_get(v_snd_5622_, 1);
v_stop_5641_ = lean_ctor_get(v_snd_5622_, 2);
v___x_5642_ = lean_nat_dec_lt(v_start_5640_, v_stop_5641_);
if (v___x_5642_ == 0)
{
lean_object* v___x_5644_; 
if (v_isShared_5638_ == 0)
{
v___x_5644_ = v___x_5637_;
goto v_reusejp_5643_;
}
else
{
lean_object* v_reuseFailAlloc_5655_; 
v_reuseFailAlloc_5655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_fst_5635_);
lean_ctor_set(v_reuseFailAlloc_5655_, 1, v_snd_5622_);
v___x_5644_ = v_reuseFailAlloc_5655_;
goto v_reusejp_5643_;
}
v_reusejp_5643_:
{
lean_object* v___x_5646_; 
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 1, v___x_5644_);
v___x_5646_ = v___x_5633_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5654_; 
v_reuseFailAlloc_5654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_fst_5631_);
lean_ctor_set(v_reuseFailAlloc_5654_, 1, v___x_5644_);
v___x_5646_ = v_reuseFailAlloc_5654_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5648_; 
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 1, v___x_5646_);
v___x_5648_ = v___x_5629_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5653_, 1, v___x_5646_);
v___x_5648_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
lean_object* v___x_5650_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5648_);
v___x_5650_ = v___x_5625_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v___x_5648_);
v___x_5650_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
lean_object* v___x_5651_; 
v___x_5651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5651_, 0, v___x_5650_);
return v___x_5651_;
}
}
}
}
}
else
{
lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5759_; 
lean_inc(v_stop_5641_);
lean_inc(v_start_5640_);
lean_inc_ref(v_array_5639_);
v_isSharedCheck_5759_ = !lean_is_exclusive(v_snd_5622_);
if (v_isSharedCheck_5759_ == 0)
{
lean_object* v_unused_5760_; lean_object* v_unused_5761_; lean_object* v_unused_5762_; 
v_unused_5760_ = lean_ctor_get(v_snd_5622_, 2);
lean_dec(v_unused_5760_);
v_unused_5761_ = lean_ctor_get(v_snd_5622_, 1);
lean_dec(v_unused_5761_);
v_unused_5762_ = lean_ctor_get(v_snd_5622_, 0);
lean_dec(v_unused_5762_);
v___x_5657_ = v_snd_5622_;
v_isShared_5658_ = v_isSharedCheck_5759_;
goto v_resetjp_5656_;
}
else
{
lean_dec(v_snd_5622_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5759_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v_array_5659_; lean_object* v_start_5660_; lean_object* v_stop_5661_; lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5666_; 
v_array_5659_ = lean_ctor_get(v_fst_5635_, 0);
v_start_5660_ = lean_ctor_get(v_fst_5635_, 1);
v_stop_5661_ = lean_ctor_get(v_fst_5635_, 2);
v___x_5662_ = lean_array_fget(v_array_5639_, v_start_5640_);
v___x_5663_ = lean_unsigned_to_nat(1u);
v___x_5664_ = lean_nat_add(v_start_5640_, v___x_5663_);
lean_dec(v_start_5640_);
if (v_isShared_5658_ == 0)
{
lean_ctor_set(v___x_5657_, 1, v___x_5664_);
v___x_5666_ = v___x_5657_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_array_5639_);
lean_ctor_set(v_reuseFailAlloc_5758_, 1, v___x_5664_);
lean_ctor_set(v_reuseFailAlloc_5758_, 2, v_stop_5641_);
v___x_5666_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
uint8_t v___x_5667_; 
v___x_5667_ = lean_nat_dec_lt(v_start_5660_, v_stop_5661_);
if (v___x_5667_ == 0)
{
lean_object* v___x_5669_; 
lean_dec(v___x_5662_);
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v___x_5666_);
v___x_5669_ = v___x_5637_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_fst_5635_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v___x_5666_);
v___x_5669_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
lean_object* v___x_5671_; 
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 1, v___x_5669_);
v___x_5671_ = v___x_5633_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_fst_5631_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v___x_5669_);
v___x_5671_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
lean_object* v___x_5673_; 
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 1, v___x_5671_);
v___x_5673_ = v___x_5629_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_fst_5627_);
lean_ctor_set(v_reuseFailAlloc_5678_, 1, v___x_5671_);
v___x_5673_ = v_reuseFailAlloc_5678_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
lean_object* v___x_5675_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5673_);
v___x_5675_ = v___x_5625_;
goto v_reusejp_5674_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5677_, 1, v___x_5673_);
v___x_5675_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5674_;
}
v_reusejp_5674_:
{
lean_object* v___x_5676_; 
v___x_5676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5676_, 0, v___x_5675_);
return v___x_5676_;
}
}
}
}
}
else
{
lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5754_; 
lean_inc(v_stop_5661_);
lean_inc(v_start_5660_);
lean_inc_ref(v_array_5659_);
v_isSharedCheck_5754_ = !lean_is_exclusive(v_fst_5635_);
if (v_isSharedCheck_5754_ == 0)
{
lean_object* v_unused_5755_; lean_object* v_unused_5756_; lean_object* v_unused_5757_; 
v_unused_5755_ = lean_ctor_get(v_fst_5635_, 2);
lean_dec(v_unused_5755_);
v_unused_5756_ = lean_ctor_get(v_fst_5635_, 1);
lean_dec(v_unused_5756_);
v_unused_5757_ = lean_ctor_get(v_fst_5635_, 0);
lean_dec(v_unused_5757_);
v___x_5682_ = v_fst_5635_;
v_isShared_5683_ = v_isSharedCheck_5754_;
goto v_resetjp_5681_;
}
else
{
lean_dec(v_fst_5635_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5754_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5684_; lean_object* v___x_5685_; lean_object* v___x_5687_; 
v___x_5684_ = lean_array_fget(v_array_5659_, v_start_5660_);
v___x_5685_ = lean_nat_add(v_start_5660_, v___x_5663_);
lean_dec(v_start_5660_);
if (v_isShared_5683_ == 0)
{
lean_ctor_set(v___x_5682_, 1, v___x_5685_);
v___x_5687_ = v___x_5682_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v_array_5659_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v___x_5685_);
lean_ctor_set(v_reuseFailAlloc_5753_, 2, v_stop_5661_);
v___x_5687_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
if (v_addEqualities_5602_ == 0)
{
lean_dec(v___x_5684_);
goto v___jp_5688_;
}
else
{
if (lean_obj_tag(v___x_5662_) == 0)
{
lean_object* v_a_5704_; lean_object* v___x_5705_; 
lean_del_object(v___x_5637_);
lean_del_object(v___x_5633_);
lean_del_object(v___x_5629_);
lean_del_object(v___x_5625_);
v_a_5704_ = lean_array_uget_borrowed(v_as_5603_, v_i_5605_);
lean_inc(v_a_5704_);
v___x_5705_ = l_Lean_Meta_isProof(v_a_5704_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
if (lean_obj_tag(v___x_5705_) == 0)
{
lean_object* v_a_5706_; uint8_t v___x_5707_; 
v_a_5706_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_a_5706_);
lean_dec_ref_known(v___x_5705_, 1);
v___x_5707_ = lean_unbox(v_a_5706_);
lean_dec(v_a_5706_);
if (v___x_5707_ == 0)
{
lean_object* v___x_5708_; 
lean_inc(v_a_5704_);
v___x_5708_ = l_Lean_Meta_mkEqHEq(v___x_5684_, v_a_5704_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
if (lean_obj_tag(v___x_5708_) == 0)
{
lean_object* v_a_5709_; lean_object* v___x_5710_; 
v_a_5709_ = lean_ctor_get(v___x_5708_, 0);
lean_inc_n(v_a_5709_, 2);
lean_dec_ref_known(v___x_5708_, 1);
v___x_5710_ = l_Lean_mkArrow(v_a_5709_, v_fst_5623_, v___y_5609_, v___y_5610_);
if (lean_obj_tag(v___x_5710_) == 0)
{
lean_object* v_a_5711_; uint8_t v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; lean_object* v___x_5720_; lean_object* v___x_5721_; 
v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
lean_inc(v_a_5711_);
lean_dec_ref_known(v___x_5710_, 1);
v___x_5712_ = l_Lean_Expr_isHEq(v_a_5709_);
lean_dec(v_a_5709_);
v___x_5713_ = lean_box(v___x_5712_);
v___x_5714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5714_, 0, v___x_5713_);
v___x_5715_ = lean_array_push(v_fst_5627_, v___x_5714_);
v___x_5716_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__9___closed__0));
v___x_5717_ = lean_array_push(v_fst_5631_, v___x_5716_);
v___x_5718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5718_, 0, v___x_5687_);
lean_ctor_set(v___x_5718_, 1, v___x_5666_);
v___x_5719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5717_);
lean_ctor_set(v___x_5719_, 1, v___x_5718_);
v___x_5720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5720_, 0, v___x_5715_);
lean_ctor_set(v___x_5720_, 1, v___x_5719_);
v___x_5721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5721_, 0, v_a_5711_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v_a_5613_ = v___x_5721_;
goto v___jp_5612_;
}
else
{
lean_object* v_a_5722_; lean_object* v___x_5724_; uint8_t v_isShared_5725_; uint8_t v_isSharedCheck_5729_; 
lean_dec(v_a_5709_);
lean_dec_ref(v___x_5687_);
lean_dec_ref(v___x_5666_);
lean_dec(v_fst_5631_);
lean_dec(v_fst_5627_);
v_a_5722_ = lean_ctor_get(v___x_5710_, 0);
v_isSharedCheck_5729_ = !lean_is_exclusive(v___x_5710_);
if (v_isSharedCheck_5729_ == 0)
{
v___x_5724_ = v___x_5710_;
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
else
{
lean_inc(v_a_5722_);
lean_dec(v___x_5710_);
v___x_5724_ = lean_box(0);
v_isShared_5725_ = v_isSharedCheck_5729_;
goto v_resetjp_5723_;
}
v_resetjp_5723_:
{
lean_object* v___x_5727_; 
if (v_isShared_5725_ == 0)
{
v___x_5727_ = v___x_5724_;
goto v_reusejp_5726_;
}
else
{
lean_object* v_reuseFailAlloc_5728_; 
v_reuseFailAlloc_5728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5728_, 0, v_a_5722_);
v___x_5727_ = v_reuseFailAlloc_5728_;
goto v_reusejp_5726_;
}
v_reusejp_5726_:
{
return v___x_5727_;
}
}
}
}
else
{
lean_object* v_a_5730_; lean_object* v___x_5732_; uint8_t v_isShared_5733_; uint8_t v_isSharedCheck_5737_; 
lean_dec_ref(v___x_5687_);
lean_dec_ref(v___x_5666_);
lean_dec(v_fst_5631_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
v_a_5730_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5737_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5737_ == 0)
{
v___x_5732_ = v___x_5708_;
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
else
{
lean_inc(v_a_5730_);
lean_dec(v___x_5708_);
v___x_5732_ = lean_box(0);
v_isShared_5733_ = v_isSharedCheck_5737_;
goto v_resetjp_5731_;
}
v_resetjp_5731_:
{
lean_object* v___x_5735_; 
if (v_isShared_5733_ == 0)
{
v___x_5735_ = v___x_5732_;
goto v_reusejp_5734_;
}
else
{
lean_object* v_reuseFailAlloc_5736_; 
v_reuseFailAlloc_5736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5730_);
v___x_5735_ = v_reuseFailAlloc_5736_;
goto v_reusejp_5734_;
}
v_reusejp_5734_:
{
return v___x_5735_;
}
}
}
}
else
{
lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5744_; 
lean_dec(v___x_5684_);
v___x_5738_ = lean_box(0);
v___x_5739_ = lean_array_push(v_fst_5627_, v___x_5738_);
v___x_5740_ = lean_array_push(v_fst_5631_, v___x_5662_);
v___x_5741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5741_, 0, v___x_5687_);
lean_ctor_set(v___x_5741_, 1, v___x_5666_);
v___x_5742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5740_);
lean_ctor_set(v___x_5742_, 1, v___x_5741_);
v___x_5743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5743_, 0, v___x_5739_);
lean_ctor_set(v___x_5743_, 1, v___x_5742_);
v___x_5744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5744_, 0, v_fst_5623_);
lean_ctor_set(v___x_5744_, 1, v___x_5743_);
v_a_5613_ = v___x_5744_;
goto v___jp_5612_;
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec_ref(v___x_5687_);
lean_dec(v___x_5684_);
lean_dec_ref(v___x_5666_);
lean_dec(v_fst_5631_);
lean_dec(v_fst_5627_);
lean_dec(v_fst_5623_);
v_a_5745_ = lean_ctor_get(v___x_5705_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5705_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5705_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5705_);
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
lean_dec(v___x_5684_);
goto v___jp_5688_;
}
}
v___jp_5688_:
{
lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5693_; 
v___x_5689_ = lean_box(0);
v___x_5690_ = lean_array_push(v_fst_5627_, v___x_5689_);
v___x_5691_ = lean_array_push(v_fst_5631_, v___x_5662_);
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v___x_5666_);
lean_ctor_set(v___x_5637_, 0, v___x_5687_);
v___x_5693_ = v___x_5637_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v___x_5687_);
lean_ctor_set(v_reuseFailAlloc_5703_, 1, v___x_5666_);
v___x_5693_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
lean_object* v___x_5695_; 
if (v_isShared_5634_ == 0)
{
lean_ctor_set(v___x_5633_, 1, v___x_5693_);
lean_ctor_set(v___x_5633_, 0, v___x_5691_);
v___x_5695_ = v___x_5633_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5691_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v___x_5693_);
v___x_5695_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5630_ == 0)
{
lean_ctor_set(v___x_5629_, 1, v___x_5695_);
lean_ctor_set(v___x_5629_, 0, v___x_5690_);
v___x_5697_ = v___x_5629_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5701_; 
v_reuseFailAlloc_5701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5701_, 0, v___x_5690_);
lean_ctor_set(v_reuseFailAlloc_5701_, 1, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5701_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
lean_object* v___x_5699_; 
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 1, v___x_5697_);
v___x_5699_ = v___x_5625_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v_fst_5623_);
lean_ctor_set(v_reuseFailAlloc_5700_, 1, v___x_5697_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
v_a_5613_ = v___x_5699_;
goto v___jp_5612_;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_5612_:
{
size_t v___x_5614_; size_t v___x_5615_; 
v___x_5614_ = ((size_t)1ULL);
v___x_5615_ = lean_usize_add(v_i_5605_, v___x_5614_);
v_i_5605_ = v___x_5615_;
v_b_5606_ = v_a_5613_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7___boxed(lean_object* v_addEqualities_5771_, lean_object* v_as_5772_, lean_object* v_sz_5773_, lean_object* v_i_5774_, lean_object* v_b_5775_, lean_object* v___y_5776_, lean_object* v___y_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_){
_start:
{
uint8_t v_addEqualities_boxed_5781_; size_t v_sz_boxed_5782_; size_t v_i_boxed_5783_; lean_object* v_res_5784_; 
v_addEqualities_boxed_5781_ = lean_unbox(v_addEqualities_5771_);
v_sz_boxed_5782_ = lean_unbox_usize(v_sz_5773_);
lean_dec(v_sz_5773_);
v_i_boxed_5783_ = lean_unbox_usize(v_i_5774_);
lean_dec(v_i_5774_);
v_res_5784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_boxed_5781_, v_as_5772_, v_sz_boxed_5782_, v_i_boxed_5783_, v_b_5775_, v___y_5776_, v___y_5777_, v___y_5778_, v___y_5779_);
lean_dec(v___y_5779_);
lean_dec_ref(v___y_5778_);
lean_dec(v___y_5777_);
lean_dec_ref(v___y_5776_);
lean_dec_ref(v_as_5772_);
return v_res_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(lean_object* v_onMotive_5785_, lean_object* v_toMatcherInfo_5786_, lean_object* v_a_5787_, uint8_t v_addEqualities_5788_, size_t v___x_5789_, lean_object* v_discrs_5790_, lean_object* v_motiveArgs_5791_, lean_object* v_motiveBody_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; uint8_t v___x_5892_; 
v___x_5890_ = lean_array_get_size(v_motiveArgs_5791_);
v___x_5891_ = lean_array_get_size(v_discrs_5790_);
v___x_5892_ = lean_nat_dec_eq(v___x_5890_, v___x_5891_);
if (v___x_5892_ == 0)
{
lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v_a_5901_; lean_object* v___x_5903_; uint8_t v_isShared_5904_; uint8_t v_isSharedCheck_5908_; 
lean_dec_ref(v_motiveBody_5792_);
lean_dec_ref(v_motiveArgs_5791_);
lean_dec_ref(v_a_5787_);
lean_dec_ref(v_toMatcherInfo_5786_);
lean_dec_ref(v_onMotive_5785_);
v___x_5893_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__3);
v___x_5894_ = l_Nat_reprFast(v___x_5891_);
v___x_5895_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5894_);
v___x_5896_ = l_Lean_MessageData_ofFormat(v___x_5895_);
v___x_5897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5893_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
v___x_5898_ = lean_obj_once(&l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5, &l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5_once, _init_l_Lean_Meta_MatcherApp_addArg___lam__0___closed__5);
v___x_5899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5897_);
lean_ctor_set(v___x_5899_, 1, v___x_5898_);
v___x_5900_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_5899_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
v_isSharedCheck_5908_ = !lean_is_exclusive(v___x_5900_);
if (v_isSharedCheck_5908_ == 0)
{
v___x_5903_ = v___x_5900_;
v_isShared_5904_ = v_isSharedCheck_5908_;
goto v_resetjp_5902_;
}
else
{
lean_inc(v_a_5901_);
lean_dec(v___x_5900_);
v___x_5903_ = lean_box(0);
v_isShared_5904_ = v_isSharedCheck_5908_;
goto v_resetjp_5902_;
}
v_resetjp_5902_:
{
lean_object* v___x_5906_; 
if (v_isShared_5904_ == 0)
{
v___x_5906_ = v___x_5903_;
goto v_reusejp_5905_;
}
else
{
lean_object* v_reuseFailAlloc_5907_; 
v_reuseFailAlloc_5907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5907_, 0, v_a_5901_);
v___x_5906_ = v_reuseFailAlloc_5907_;
goto v_reusejp_5905_;
}
v_reusejp_5905_:
{
return v___x_5906_;
}
}
}
else
{
goto v___jp_5798_;
}
v___jp_5798_:
{
lean_object* v___x_5799_; 
lean_inc(v___y_5796_);
lean_inc_ref(v___y_5795_);
lean_inc(v___y_5794_);
lean_inc_ref(v___y_5793_);
lean_inc_ref(v_motiveArgs_5791_);
v___x_5799_ = lean_apply_7(v_onMotive_5785_, v_motiveArgs_5791_, v_motiveBody_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_, lean_box(0));
if (lean_obj_tag(v___x_5799_) == 0)
{
lean_object* v_a_5800_; lean_object* v_discrInfos_5801_; lean_object* v___x_5802_; lean_object* v_addHEqualities_5803_; lean_object* v___x_5804_; lean_object* v___x_5805_; lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; size_t v_sz_5812_; lean_object* v___x_5813_; 
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
lean_inc(v_a_5800_);
lean_dec_ref_known(v___x_5799_, 1);
v_discrInfos_5801_ = lean_ctor_get(v_toMatcherInfo_5786_, 4);
lean_inc_ref(v_discrInfos_5801_);
lean_dec_ref(v_toMatcherInfo_5786_);
v___x_5802_ = lean_unsigned_to_nat(0u);
v_addHEqualities_5803_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__16___closed__0));
v___x_5804_ = lean_array_get_size(v_a_5787_);
v___x_5805_ = l_Array_toSubarray___redArg(v_a_5787_, v___x_5802_, v___x_5804_);
v___x_5806_ = lean_array_get_size(v_discrInfos_5801_);
v___x_5807_ = l_Array_toSubarray___redArg(v_discrInfos_5801_, v___x_5802_, v___x_5806_);
v___x_5808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5808_, 0, v___x_5805_);
lean_ctor_set(v___x_5808_, 1, v___x_5807_);
v___x_5809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5809_, 0, v_addHEqualities_5803_);
lean_ctor_set(v___x_5809_, 1, v___x_5808_);
v___x_5810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5810_, 0, v_addHEqualities_5803_);
lean_ctor_set(v___x_5810_, 1, v___x_5809_);
v___x_5811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5811_, 0, v_a_5800_);
lean_ctor_set(v___x_5811_, 1, v___x_5810_);
v_sz_5812_ = lean_array_size(v_motiveArgs_5791_);
v___x_5813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__7(v_addEqualities_5788_, v_motiveArgs_5791_, v_sz_5812_, v___x_5789_, v___x_5811_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v_snd_5815_; lean_object* v_snd_5816_; lean_object* v_fst_5817_; lean_object* v___x_5819_; uint8_t v_isShared_5820_; uint8_t v_isSharedCheck_5872_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
lean_inc(v_a_5814_);
lean_dec_ref_known(v___x_5813_, 1);
v_snd_5815_ = lean_ctor_get(v_a_5814_, 1);
lean_inc(v_snd_5815_);
v_snd_5816_ = lean_ctor_get(v_snd_5815_, 1);
lean_inc(v_snd_5816_);
v_fst_5817_ = lean_ctor_get(v_a_5814_, 0);
v_isSharedCheck_5872_ = !lean_is_exclusive(v_a_5814_);
if (v_isSharedCheck_5872_ == 0)
{
lean_object* v_unused_5873_; 
v_unused_5873_ = lean_ctor_get(v_a_5814_, 1);
lean_dec(v_unused_5873_);
v___x_5819_ = v_a_5814_;
v_isShared_5820_ = v_isSharedCheck_5872_;
goto v_resetjp_5818_;
}
else
{
lean_inc(v_fst_5817_);
lean_dec(v_a_5814_);
v___x_5819_ = lean_box(0);
v_isShared_5820_ = v_isSharedCheck_5872_;
goto v_resetjp_5818_;
}
v_resetjp_5818_:
{
lean_object* v_fst_5821_; lean_object* v___x_5823_; uint8_t v_isShared_5824_; uint8_t v_isSharedCheck_5870_; 
v_fst_5821_ = lean_ctor_get(v_snd_5815_, 0);
v_isSharedCheck_5870_ = !lean_is_exclusive(v_snd_5815_);
if (v_isSharedCheck_5870_ == 0)
{
lean_object* v_unused_5871_; 
v_unused_5871_ = lean_ctor_get(v_snd_5815_, 1);
lean_dec(v_unused_5871_);
v___x_5823_ = v_snd_5815_;
v_isShared_5824_ = v_isSharedCheck_5870_;
goto v_resetjp_5822_;
}
else
{
lean_inc(v_fst_5821_);
lean_dec(v_snd_5815_);
v___x_5823_ = lean_box(0);
v_isShared_5824_ = v_isSharedCheck_5870_;
goto v_resetjp_5822_;
}
v_resetjp_5822_:
{
lean_object* v_fst_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5868_; 
v_fst_5825_ = lean_ctor_get(v_snd_5816_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v_snd_5816_);
if (v_isSharedCheck_5868_ == 0)
{
lean_object* v_unused_5869_; 
v_unused_5869_ = lean_ctor_get(v_snd_5816_, 1);
lean_dec(v_unused_5869_);
v___x_5827_ = v_snd_5816_;
v_isShared_5828_ = v_isSharedCheck_5868_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_fst_5825_);
lean_dec(v_snd_5816_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5868_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
uint8_t v___x_5829_; uint8_t v___x_5830_; uint8_t v___x_5831_; lean_object* v___x_5832_; 
v___x_5829_ = 0;
v___x_5830_ = 1;
v___x_5831_ = 1;
lean_inc(v_fst_5817_);
v___x_5832_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_5791_, v_fst_5817_, v___x_5829_, v___x_5830_, v___x_5829_, v___x_5830_, v___x_5831_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
lean_dec_ref(v_motiveArgs_5791_);
if (lean_obj_tag(v___x_5832_) == 0)
{
lean_object* v_a_5833_; lean_object* v___x_5834_; 
v_a_5833_ = lean_ctor_get(v___x_5832_, 0);
lean_inc(v_a_5833_);
lean_dec_ref_known(v___x_5832_, 1);
v___x_5834_ = l_Lean_Meta_getLevel(v_fst_5817_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
if (lean_obj_tag(v___x_5834_) == 0)
{
lean_object* v_a_5835_; lean_object* v___x_5837_; uint8_t v_isShared_5838_; uint8_t v_isSharedCheck_5851_; 
v_a_5835_ = lean_ctor_get(v___x_5834_, 0);
v_isSharedCheck_5851_ = !lean_is_exclusive(v___x_5834_);
if (v_isSharedCheck_5851_ == 0)
{
v___x_5837_ = v___x_5834_;
v_isShared_5838_ = v_isSharedCheck_5851_;
goto v_resetjp_5836_;
}
else
{
lean_inc(v_a_5835_);
lean_dec(v___x_5834_);
v___x_5837_ = lean_box(0);
v_isShared_5838_ = v_isSharedCheck_5851_;
goto v_resetjp_5836_;
}
v_resetjp_5836_:
{
lean_object* v___x_5840_; 
if (v_isShared_5828_ == 0)
{
lean_ctor_set(v___x_5827_, 1, v_fst_5825_);
lean_ctor_set(v___x_5827_, 0, v_fst_5821_);
v___x_5840_ = v___x_5827_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5850_; 
v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5850_, 0, v_fst_5821_);
lean_ctor_set(v_reuseFailAlloc_5850_, 1, v_fst_5825_);
v___x_5840_ = v_reuseFailAlloc_5850_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
lean_object* v___x_5842_; 
if (v_isShared_5824_ == 0)
{
lean_ctor_set(v___x_5823_, 1, v___x_5840_);
lean_ctor_set(v___x_5823_, 0, v_a_5835_);
v___x_5842_ = v___x_5823_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5835_);
lean_ctor_set(v_reuseFailAlloc_5849_, 1, v___x_5840_);
v___x_5842_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
lean_object* v___x_5844_; 
if (v_isShared_5820_ == 0)
{
lean_ctor_set(v___x_5819_, 1, v___x_5842_);
lean_ctor_set(v___x_5819_, 0, v_a_5833_);
v___x_5844_ = v___x_5819_;
goto v_reusejp_5843_;
}
else
{
lean_object* v_reuseFailAlloc_5848_; 
v_reuseFailAlloc_5848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5848_, 0, v_a_5833_);
lean_ctor_set(v_reuseFailAlloc_5848_, 1, v___x_5842_);
v___x_5844_ = v_reuseFailAlloc_5848_;
goto v_reusejp_5843_;
}
v_reusejp_5843_:
{
lean_object* v___x_5846_; 
if (v_isShared_5838_ == 0)
{
lean_ctor_set(v___x_5837_, 0, v___x_5844_);
v___x_5846_ = v___x_5837_;
goto v_reusejp_5845_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v___x_5844_);
v___x_5846_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5845_;
}
v_reusejp_5845_:
{
return v___x_5846_;
}
}
}
}
}
}
else
{
lean_object* v_a_5852_; lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5859_; 
lean_dec(v_a_5833_);
lean_del_object(v___x_5827_);
lean_dec(v_fst_5825_);
lean_del_object(v___x_5823_);
lean_dec(v_fst_5821_);
lean_del_object(v___x_5819_);
v_a_5852_ = lean_ctor_get(v___x_5834_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v___x_5834_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5854_ = v___x_5834_;
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
else
{
lean_inc(v_a_5852_);
lean_dec(v___x_5834_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v___x_5857_; 
if (v_isShared_5855_ == 0)
{
v___x_5857_ = v___x_5854_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
v___x_5857_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
return v___x_5857_;
}
}
}
}
else
{
lean_object* v_a_5860_; lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5867_; 
lean_del_object(v___x_5827_);
lean_dec(v_fst_5825_);
lean_del_object(v___x_5823_);
lean_dec(v_fst_5821_);
lean_del_object(v___x_5819_);
lean_dec(v_fst_5817_);
v_a_5860_ = lean_ctor_get(v___x_5832_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5832_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5862_ = v___x_5832_;
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
else
{
lean_inc(v_a_5860_);
lean_dec(v___x_5832_);
v___x_5862_ = lean_box(0);
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
v_resetjp_5861_:
{
lean_object* v___x_5865_; 
if (v_isShared_5863_ == 0)
{
v___x_5865_ = v___x_5862_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
v___x_5865_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
return v___x_5865_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5874_; lean_object* v___x_5876_; uint8_t v_isShared_5877_; uint8_t v_isSharedCheck_5881_; 
lean_dec_ref(v_motiveArgs_5791_);
v_a_5874_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_5881_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_5881_ == 0)
{
v___x_5876_ = v___x_5813_;
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
else
{
lean_inc(v_a_5874_);
lean_dec(v___x_5813_);
v___x_5876_ = lean_box(0);
v_isShared_5877_ = v_isSharedCheck_5881_;
goto v_resetjp_5875_;
}
v_resetjp_5875_:
{
lean_object* v___x_5879_; 
if (v_isShared_5877_ == 0)
{
v___x_5879_ = v___x_5876_;
goto v_reusejp_5878_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_a_5874_);
v___x_5879_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5878_;
}
v_reusejp_5878_:
{
return v___x_5879_;
}
}
}
}
else
{
lean_object* v_a_5882_; lean_object* v___x_5884_; uint8_t v_isShared_5885_; uint8_t v_isSharedCheck_5889_; 
lean_dec_ref(v_motiveArgs_5791_);
lean_dec_ref(v_a_5787_);
lean_dec_ref(v_toMatcherInfo_5786_);
v_a_5882_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5889_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5889_ == 0)
{
v___x_5884_ = v___x_5799_;
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
else
{
lean_inc(v_a_5882_);
lean_dec(v___x_5799_);
v___x_5884_ = lean_box(0);
v_isShared_5885_ = v_isSharedCheck_5889_;
goto v_resetjp_5883_;
}
v_resetjp_5883_:
{
lean_object* v___x_5887_; 
if (v_isShared_5885_ == 0)
{
v___x_5887_ = v___x_5884_;
goto v_reusejp_5886_;
}
else
{
lean_object* v_reuseFailAlloc_5888_; 
v_reuseFailAlloc_5888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_a_5882_);
v___x_5887_ = v_reuseFailAlloc_5888_;
goto v_reusejp_5886_;
}
v_reusejp_5886_:
{
return v___x_5887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed(lean_object* v_onMotive_5909_, lean_object* v_toMatcherInfo_5910_, lean_object* v_a_5911_, lean_object* v_addEqualities_5912_, lean_object* v___x_5913_, lean_object* v_discrs_5914_, lean_object* v_motiveArgs_5915_, lean_object* v_motiveBody_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_){
_start:
{
uint8_t v_addEqualities_boxed_5922_; size_t v___x_34396__boxed_5923_; lean_object* v_res_5924_; 
v_addEqualities_boxed_5922_ = lean_unbox(v_addEqualities_5912_);
v___x_34396__boxed_5923_ = lean_unbox_usize(v___x_5913_);
lean_dec(v___x_5913_);
v_res_5924_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3(v_onMotive_5909_, v_toMatcherInfo_5910_, v_a_5911_, v_addEqualities_boxed_5922_, v___x_34396__boxed_5923_, v_discrs_5914_, v_motiveArgs_5915_, v_motiveBody_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_);
lean_dec(v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec_ref(v_discrs_5914_);
return v_res_5924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(lean_object* v_as_5925_, size_t v_sz_5926_, size_t v_i_5927_, lean_object* v_b_5928_, lean_object* v___y_5929_, lean_object* v___y_5930_, lean_object* v___y_5931_, lean_object* v___y_5932_){
_start:
{
lean_object* v_a_5935_; uint8_t v___x_5939_; 
v___x_5939_ = lean_usize_dec_lt(v_i_5927_, v_sz_5926_);
if (v___x_5939_ == 0)
{
lean_object* v___x_5940_; 
v___x_5940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5940_, 0, v_b_5928_);
return v___x_5940_;
}
else
{
lean_object* v_snd_5941_; lean_object* v_snd_5942_; lean_object* v_fst_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_6003_; 
v_snd_5941_ = lean_ctor_get(v_b_5928_, 1);
lean_inc(v_snd_5941_);
v_snd_5942_ = lean_ctor_get(v_snd_5941_, 1);
lean_inc(v_snd_5942_);
v_fst_5943_ = lean_ctor_get(v_b_5928_, 0);
v_isSharedCheck_6003_ = !lean_is_exclusive(v_b_5928_);
if (v_isSharedCheck_6003_ == 0)
{
lean_object* v_unused_6004_; 
v_unused_6004_ = lean_ctor_get(v_b_5928_, 1);
lean_dec(v_unused_6004_);
v___x_5945_ = v_b_5928_;
v_isShared_5946_ = v_isSharedCheck_6003_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_fst_5943_);
lean_dec(v_b_5928_);
v___x_5945_ = lean_box(0);
v_isShared_5946_ = v_isSharedCheck_6003_;
goto v_resetjp_5944_;
}
v_resetjp_5944_:
{
lean_object* v_fst_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_6001_; 
v_fst_5947_ = lean_ctor_get(v_snd_5941_, 0);
v_isSharedCheck_6001_ = !lean_is_exclusive(v_snd_5941_);
if (v_isSharedCheck_6001_ == 0)
{
lean_object* v_unused_6002_; 
v_unused_6002_ = lean_ctor_get(v_snd_5941_, 1);
lean_dec(v_unused_6002_);
v___x_5949_ = v_snd_5941_;
v_isShared_5950_ = v_isSharedCheck_6001_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_fst_5947_);
lean_dec(v_snd_5941_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_6001_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
lean_object* v_array_5951_; lean_object* v_start_5952_; lean_object* v_stop_5953_; uint8_t v___x_5954_; 
v_array_5951_ = lean_ctor_get(v_snd_5942_, 0);
v_start_5952_ = lean_ctor_get(v_snd_5942_, 1);
v_stop_5953_ = lean_ctor_get(v_snd_5942_, 2);
v___x_5954_ = lean_nat_dec_lt(v_start_5952_, v_stop_5953_);
if (v___x_5954_ == 0)
{
lean_object* v___x_5956_; 
if (v_isShared_5950_ == 0)
{
v___x_5956_ = v___x_5949_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5961_; 
v_reuseFailAlloc_5961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_fst_5947_);
lean_ctor_set(v_reuseFailAlloc_5961_, 1, v_snd_5942_);
v___x_5956_ = v_reuseFailAlloc_5961_;
goto v_reusejp_5955_;
}
v_reusejp_5955_:
{
lean_object* v___x_5958_; 
if (v_isShared_5946_ == 0)
{
lean_ctor_set(v___x_5945_, 1, v___x_5956_);
v___x_5958_ = v___x_5945_;
goto v_reusejp_5957_;
}
else
{
lean_object* v_reuseFailAlloc_5960_; 
v_reuseFailAlloc_5960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5960_, 0, v_fst_5943_);
lean_ctor_set(v_reuseFailAlloc_5960_, 1, v___x_5956_);
v___x_5958_ = v_reuseFailAlloc_5960_;
goto v_reusejp_5957_;
}
v_reusejp_5957_:
{
lean_object* v___x_5959_; 
v___x_5959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5958_);
return v___x_5959_;
}
}
}
else
{
lean_object* v___x_5963_; uint8_t v_isShared_5964_; uint8_t v_isSharedCheck_5997_; 
lean_inc(v_stop_5953_);
lean_inc(v_start_5952_);
lean_inc_ref(v_array_5951_);
v_isSharedCheck_5997_ = !lean_is_exclusive(v_snd_5942_);
if (v_isSharedCheck_5997_ == 0)
{
lean_object* v_unused_5998_; lean_object* v_unused_5999_; lean_object* v_unused_6000_; 
v_unused_5998_ = lean_ctor_get(v_snd_5942_, 2);
lean_dec(v_unused_5998_);
v_unused_5999_ = lean_ctor_get(v_snd_5942_, 1);
lean_dec(v_unused_5999_);
v_unused_6000_ = lean_ctor_get(v_snd_5942_, 0);
lean_dec(v_unused_6000_);
v___x_5963_ = v_snd_5942_;
v_isShared_5964_ = v_isSharedCheck_5997_;
goto v_resetjp_5962_;
}
else
{
lean_dec(v_snd_5942_);
v___x_5963_ = lean_box(0);
v_isShared_5964_ = v_isSharedCheck_5997_;
goto v_resetjp_5962_;
}
v_resetjp_5962_:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5969_; 
v___x_5965_ = lean_array_fget(v_array_5951_, v_start_5952_);
v___x_5966_ = lean_unsigned_to_nat(1u);
v___x_5967_ = lean_nat_add(v_start_5952_, v___x_5966_);
lean_dec(v_start_5952_);
if (v_isShared_5964_ == 0)
{
lean_ctor_set(v___x_5963_, 1, v___x_5967_);
v___x_5969_ = v___x_5963_;
goto v_reusejp_5968_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_array_5951_);
lean_ctor_set(v_reuseFailAlloc_5996_, 1, v___x_5967_);
lean_ctor_set(v_reuseFailAlloc_5996_, 2, v_stop_5953_);
v___x_5969_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5968_;
}
v_reusejp_5968_:
{
lean_object* v___y_5971_; 
if (lean_obj_tag(v___x_5965_) == 0)
{
lean_object* v___x_5989_; lean_object* v___x_5990_; 
lean_del_object(v___x_5949_);
lean_del_object(v___x_5945_);
v___x_5989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5989_, 0, v_fst_5947_);
lean_ctor_set(v___x_5989_, 1, v___x_5969_);
v___x_5990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5990_, 0, v_fst_5943_);
lean_ctor_set(v___x_5990_, 1, v___x_5989_);
v_a_5935_ = v___x_5990_;
goto v___jp_5934_;
}
else
{
lean_object* v_val_5991_; lean_object* v_a_5992_; uint8_t v___x_5993_; 
v_val_5991_ = lean_ctor_get(v___x_5965_, 0);
lean_inc(v_val_5991_);
lean_dec_ref_known(v___x_5965_, 1);
v_a_5992_ = lean_array_uget_borrowed(v_as_5925_, v_i_5927_);
v___x_5993_ = lean_unbox(v_val_5991_);
lean_dec(v_val_5991_);
if (v___x_5993_ == 0)
{
lean_object* v___x_5994_; 
lean_inc(v_a_5992_);
v___x_5994_ = l_Lean_Meta_mkEqRefl(v_a_5992_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
v___y_5971_ = v___x_5994_;
goto v___jp_5970_;
}
else
{
lean_object* v___x_5995_; 
lean_inc(v_a_5992_);
v___x_5995_ = l_Lean_Meta_mkHEqRefl(v_a_5992_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_);
v___y_5971_ = v___x_5995_;
goto v___jp_5970_;
}
}
v___jp_5970_:
{
if (lean_obj_tag(v___y_5971_) == 0)
{
lean_object* v_a_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5976_; 
v_a_5972_ = lean_ctor_get(v___y_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___y_5971_, 1);
v___x_5973_ = lean_array_push(v_fst_5943_, v_a_5972_);
v___x_5974_ = lean_nat_add(v_fst_5947_, v___x_5966_);
lean_dec(v_fst_5947_);
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 1, v___x_5969_);
lean_ctor_set(v___x_5949_, 0, v___x_5974_);
v___x_5976_ = v___x_5949_;
goto v_reusejp_5975_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v___x_5974_);
lean_ctor_set(v_reuseFailAlloc_5980_, 1, v___x_5969_);
v___x_5976_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5975_;
}
v_reusejp_5975_:
{
lean_object* v___x_5978_; 
if (v_isShared_5946_ == 0)
{
lean_ctor_set(v___x_5945_, 1, v___x_5976_);
lean_ctor_set(v___x_5945_, 0, v___x_5973_);
v___x_5978_ = v___x_5945_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v___x_5973_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v___x_5976_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
v_a_5935_ = v___x_5978_;
goto v___jp_5934_;
}
}
}
else
{
lean_object* v_a_5981_; lean_object* v___x_5983_; uint8_t v_isShared_5984_; uint8_t v_isSharedCheck_5988_; 
lean_dec_ref(v___x_5969_);
lean_del_object(v___x_5949_);
lean_dec(v_fst_5947_);
lean_del_object(v___x_5945_);
lean_dec(v_fst_5943_);
v_a_5981_ = lean_ctor_get(v___y_5971_, 0);
v_isSharedCheck_5988_ = !lean_is_exclusive(v___y_5971_);
if (v_isSharedCheck_5988_ == 0)
{
v___x_5983_ = v___y_5971_;
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
else
{
lean_inc(v_a_5981_);
lean_dec(v___y_5971_);
v___x_5983_ = lean_box(0);
v_isShared_5984_ = v_isSharedCheck_5988_;
goto v_resetjp_5982_;
}
v_resetjp_5982_:
{
lean_object* v___x_5986_; 
if (v_isShared_5984_ == 0)
{
v___x_5986_ = v___x_5983_;
goto v_reusejp_5985_;
}
else
{
lean_object* v_reuseFailAlloc_5987_; 
v_reuseFailAlloc_5987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_a_5981_);
v___x_5986_ = v_reuseFailAlloc_5987_;
goto v_reusejp_5985_;
}
v_reusejp_5985_:
{
return v___x_5986_;
}
}
}
}
}
}
}
}
}
}
v___jp_5934_:
{
size_t v___x_5936_; size_t v___x_5937_; 
v___x_5936_ = ((size_t)1ULL);
v___x_5937_ = lean_usize_add(v_i_5927_, v___x_5936_);
v_i_5927_ = v___x_5937_;
v_b_5928_ = v_a_5935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8___boxed(lean_object* v_as_6005_, lean_object* v_sz_6006_, lean_object* v_i_6007_, lean_object* v_b_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_){
_start:
{
size_t v_sz_boxed_6014_; size_t v_i_boxed_6015_; lean_object* v_res_6016_; 
v_sz_boxed_6014_ = lean_unbox_usize(v_sz_6006_);
lean_dec(v_sz_6006_);
v_i_boxed_6015_ = lean_unbox_usize(v_i_6007_);
lean_dec(v_i_6007_);
v_res_6016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v_as_6005_, v_sz_boxed_6014_, v_i_boxed_6015_, v_b_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_);
lean_dec(v___y_6012_);
lean_dec_ref(v___y_6011_);
lean_dec(v___y_6010_);
lean_dec_ref(v___y_6009_);
lean_dec_ref(v_as_6005_);
return v_res_6016_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(lean_object* v___x_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_){
_start:
{
lean_object* v___x_6023_; 
v___x_6023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6017_);
return v___x_6023_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed(lean_object* v___x_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_){
_start:
{
lean_object* v_res_6030_; 
v_res_6030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0(v___x_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_);
lean_dec(v___y_6028_);
lean_dec_ref(v___y_6027_);
lean_dec(v___y_6026_);
lean_dec_ref(v___y_6025_);
return v_res_6030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(size_t v_sz_6031_, size_t v_i_6032_, lean_object* v_bs_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_){
_start:
{
uint8_t v___x_6038_; 
v___x_6038_ = lean_usize_dec_lt(v_i_6032_, v_sz_6031_);
if (v___x_6038_ == 0)
{
lean_object* v___x_6039_; 
v___x_6039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6039_, 0, v_bs_6033_);
return v___x_6039_;
}
else
{
lean_object* v_v_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; 
v_v_6040_ = lean_array_uget_borrowed(v_bs_6033_, v_i_6032_);
v___x_6041_ = l_Lean_Expr_fvarId_x21(v_v_6040_);
v___x_6042_ = l_Lean_FVarId_getUserName___redArg(v___x_6041_, v___y_6034_, v___y_6035_, v___y_6036_);
if (lean_obj_tag(v___x_6042_) == 0)
{
lean_object* v_a_6043_; lean_object* v___x_6044_; lean_object* v_bs_x27_6045_; size_t v___x_6046_; size_t v___x_6047_; lean_object* v___x_6048_; 
v_a_6043_ = lean_ctor_get(v___x_6042_, 0);
lean_inc(v_a_6043_);
lean_dec_ref_known(v___x_6042_, 1);
v___x_6044_ = lean_unsigned_to_nat(0u);
v_bs_x27_6045_ = lean_array_uset(v_bs_6033_, v_i_6032_, v___x_6044_);
v___x_6046_ = ((size_t)1ULL);
v___x_6047_ = lean_usize_add(v_i_6032_, v___x_6046_);
v___x_6048_ = lean_array_uset(v_bs_x27_6045_, v_i_6032_, v_a_6043_);
v_i_6032_ = v___x_6047_;
v_bs_6033_ = v___x_6048_;
goto _start;
}
else
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6057_; 
lean_dec_ref(v_bs_6033_);
v_a_6050_ = lean_ctor_get(v___x_6042_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_6042_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6052_ = v___x_6042_;
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v___x_6042_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
if (v_isShared_6053_ == 0)
{
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg___boxed(lean_object* v_sz_6058_, lean_object* v_i_6059_, lean_object* v_bs_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_, lean_object* v___y_6063_, lean_object* v___y_6064_){
_start:
{
size_t v_sz_boxed_6065_; size_t v_i_boxed_6066_; lean_object* v_res_6067_; 
v_sz_boxed_6065_ = lean_unbox_usize(v_sz_6058_);
lean_dec(v_sz_6058_);
v_i_boxed_6066_ = lean_unbox_usize(v_i_6059_);
lean_dec(v_i_6059_);
v_res_6067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_boxed_6065_, v_i_boxed_6066_, v_bs_6060_, v___y_6061_, v___y_6062_, v___y_6063_);
lean_dec(v___y_6063_);
lean_dec_ref(v___y_6062_);
lean_dec_ref(v___y_6061_);
return v_res_6067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(lean_object* v_xs_6068_, lean_object* v_x_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_){
_start:
{
size_t v_sz_6075_; size_t v___x_6076_; lean_object* v___x_6077_; 
v_sz_6075_ = lean_array_size(v_xs_6068_);
v___x_6076_ = ((size_t)0ULL);
v___x_6077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_6075_, v___x_6076_, v_xs_6068_, v___y_6070_, v___y_6072_, v___y_6073_);
return v___x_6077_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3___boxed(lean_object* v_xs_6078_, lean_object* v_x_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_, lean_object* v___y_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_){
_start:
{
lean_object* v_res_6085_; 
v_res_6085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__3(v_xs_6078_, v_x_6079_, v___y_6080_, v___y_6081_, v___y_6082_, v___y_6083_);
lean_dec(v___y_6083_);
lean_dec_ref(v___y_6082_);
lean_dec(v___y_6081_);
lean_dec_ref(v___y_6080_);
lean_dec_ref(v_x_6079_);
return v_res_6085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(lean_object* v___x_6086_, lean_object* v___x_6087_, lean_object* v___f_6088_, uint8_t v___x_6089_, lean_object* v_fst_6090_, lean_object* v___x_6091_, lean_object* v___x_6092_, lean_object* v___x_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_){
_start:
{
lean_object* v___x_6099_; 
v___x_6099_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v___x_6086_, v___x_6087_, v___f_6088_, v___x_6089_, v___x_6089_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_);
if (lean_obj_tag(v___x_6099_) == 0)
{
lean_object* v_a_6100_; lean_object* v___x_6102_; uint8_t v_isShared_6103_; uint8_t v_isSharedCheck_6112_; 
v_a_6100_ = lean_ctor_get(v___x_6099_, 0);
v_isSharedCheck_6112_ = !lean_is_exclusive(v___x_6099_);
if (v_isSharedCheck_6112_ == 0)
{
v___x_6102_ = v___x_6099_;
v_isShared_6103_ = v_isSharedCheck_6112_;
goto v_resetjp_6101_;
}
else
{
lean_inc(v_a_6100_);
lean_dec(v___x_6099_);
v___x_6102_ = lean_box(0);
v_isShared_6103_ = v_isSharedCheck_6112_;
goto v_resetjp_6101_;
}
v_resetjp_6101_:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6110_; 
v___x_6104_ = lean_array_push(v_fst_6090_, v_a_6100_);
v___x_6105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6105_, 0, v___x_6091_);
lean_ctor_set(v___x_6105_, 1, v___x_6092_);
v___x_6106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6093_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
v___x_6107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6104_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
v___x_6108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6108_, 0, v___x_6107_);
if (v_isShared_6103_ == 0)
{
lean_ctor_set(v___x_6102_, 0, v___x_6108_);
v___x_6110_ = v___x_6102_;
goto v_reusejp_6109_;
}
else
{
lean_object* v_reuseFailAlloc_6111_; 
v_reuseFailAlloc_6111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6111_, 0, v___x_6108_);
v___x_6110_ = v_reuseFailAlloc_6111_;
goto v_reusejp_6109_;
}
v_reusejp_6109_:
{
return v___x_6110_;
}
}
}
else
{
lean_object* v_a_6113_; lean_object* v___x_6115_; uint8_t v_isShared_6116_; uint8_t v_isSharedCheck_6120_; 
lean_dec_ref(v___x_6093_);
lean_dec_ref(v___x_6092_);
lean_dec_ref(v___x_6091_);
lean_dec(v_fst_6090_);
v_a_6113_ = lean_ctor_get(v___x_6099_, 0);
v_isSharedCheck_6120_ = !lean_is_exclusive(v___x_6099_);
if (v_isSharedCheck_6120_ == 0)
{
v___x_6115_ = v___x_6099_;
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
else
{
lean_inc(v_a_6113_);
lean_dec(v___x_6099_);
v___x_6115_ = lean_box(0);
v_isShared_6116_ = v_isSharedCheck_6120_;
goto v_resetjp_6114_;
}
v_resetjp_6114_:
{
lean_object* v___x_6118_; 
if (v_isShared_6116_ == 0)
{
v___x_6118_ = v___x_6115_;
goto v_reusejp_6117_;
}
else
{
lean_object* v_reuseFailAlloc_6119_; 
v_reuseFailAlloc_6119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_a_6113_);
v___x_6118_ = v_reuseFailAlloc_6119_;
goto v_reusejp_6117_;
}
v_reusejp_6117_:
{
return v___x_6118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed(lean_object* v___x_6121_, lean_object* v___x_6122_, lean_object* v___f_6123_, lean_object* v___x_6124_, lean_object* v_fst_6125_, lean_object* v___x_6126_, lean_object* v___x_6127_, lean_object* v___x_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_){
_start:
{
uint8_t v___x_34859__boxed_6134_; lean_object* v_res_6135_; 
v___x_34859__boxed_6134_ = lean_unbox(v___x_6124_);
v_res_6135_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5(v___x_6121_, v___x_6122_, v___f_6123_, v___x_34859__boxed_6134_, v_fst_6125_, v___x_6126_, v___x_6127_, v___x_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_);
lean_dec(v___y_6132_);
lean_dec_ref(v___y_6131_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(lean_object* v_fvars_6136_, lean_object* v_names_6137_, lean_object* v_k_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_){
_start:
{
lean_object* v___x_6144_; 
v___x_6144_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_withUserNamesImpl___redArg(v_fvars_6136_, v_names_6137_, v_k_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_);
if (lean_obj_tag(v___x_6144_) == 0)
{
lean_object* v_a_6145_; lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6152_; 
v_a_6145_ = lean_ctor_get(v___x_6144_, 0);
v_isSharedCheck_6152_ = !lean_is_exclusive(v___x_6144_);
if (v_isSharedCheck_6152_ == 0)
{
v___x_6147_ = v___x_6144_;
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
else
{
lean_inc(v_a_6145_);
lean_dec(v___x_6144_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6152_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6150_; 
if (v_isShared_6148_ == 0)
{
v___x_6150_ = v___x_6147_;
goto v_reusejp_6149_;
}
else
{
lean_object* v_reuseFailAlloc_6151_; 
v_reuseFailAlloc_6151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6151_, 0, v_a_6145_);
v___x_6150_ = v_reuseFailAlloc_6151_;
goto v_reusejp_6149_;
}
v_reusejp_6149_:
{
return v___x_6150_;
}
}
}
else
{
lean_object* v_a_6153_; lean_object* v___x_6155_; uint8_t v_isShared_6156_; uint8_t v_isSharedCheck_6160_; 
v_a_6153_ = lean_ctor_get(v___x_6144_, 0);
v_isSharedCheck_6160_ = !lean_is_exclusive(v___x_6144_);
if (v_isSharedCheck_6160_ == 0)
{
v___x_6155_ = v___x_6144_;
v_isShared_6156_ = v_isSharedCheck_6160_;
goto v_resetjp_6154_;
}
else
{
lean_inc(v_a_6153_);
lean_dec(v___x_6144_);
v___x_6155_ = lean_box(0);
v_isShared_6156_ = v_isSharedCheck_6160_;
goto v_resetjp_6154_;
}
v_resetjp_6154_:
{
lean_object* v___x_6158_; 
if (v_isShared_6156_ == 0)
{
v___x_6158_ = v___x_6155_;
goto v_reusejp_6157_;
}
else
{
lean_object* v_reuseFailAlloc_6159_; 
v_reuseFailAlloc_6159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6159_, 0, v_a_6153_);
v___x_6158_ = v_reuseFailAlloc_6159_;
goto v_reusejp_6157_;
}
v_reusejp_6157_:
{
return v___x_6158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg___boxed(lean_object* v_fvars_6161_, lean_object* v_names_6162_, lean_object* v_k_6163_, lean_object* v___y_6164_, lean_object* v___y_6165_, lean_object* v___y_6166_, lean_object* v___y_6167_, lean_object* v___y_6168_){
_start:
{
lean_object* v_res_6169_; 
v_res_6169_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6161_, v_names_6162_, v_k_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
lean_dec(v___y_6167_);
lean_dec_ref(v___y_6166_);
lean_dec(v___y_6165_);
lean_dec_ref(v___y_6164_);
lean_dec_ref(v_names_6162_);
lean_dec_ref(v_fvars_6161_);
return v_res_6169_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(lean_object* v___x_6170_, lean_object* v_xs_6171_, lean_object* v_remaining_x27_6172_, lean_object* v_ys4_6173_, lean_object* v_onAlt_6174_, lean_object* v_a_6175_, lean_object* v_altType_6176_, uint8_t v___x_6177_, uint8_t v___x_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_){
_start:
{
lean_object* v___x_6184_; 
v___x_6184_ = l_Lean_Meta_instantiateLambda(v___x_6170_, v_xs_6171_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
if (lean_obj_tag(v___x_6184_) == 0)
{
lean_object* v_a_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; 
v_a_6185_ = lean_ctor_get(v___x_6184_, 0);
lean_inc(v_a_6185_);
lean_dec_ref_known(v___x_6184_, 1);
lean_inc_ref(v_ys4_6173_);
lean_inc_ref(v_remaining_x27_6172_);
lean_inc_ref_n(v_xs_6171_, 2);
v___x_6186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6186_, 0, v_xs_6171_);
lean_ctor_set(v___x_6186_, 1, v_xs_6171_);
lean_ctor_set(v___x_6186_, 2, v_remaining_x27_6172_);
lean_ctor_set(v___x_6186_, 3, v_remaining_x27_6172_);
lean_ctor_set(v___x_6186_, 4, v_ys4_6173_);
lean_inc(v___y_6182_);
lean_inc_ref(v___y_6181_);
lean_inc(v___y_6180_);
lean_inc_ref(v___y_6179_);
v___x_6187_ = lean_apply_9(v_onAlt_6174_, v_a_6175_, v_altType_6176_, v___x_6186_, v_a_6185_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_, lean_box(0));
if (lean_obj_tag(v___x_6187_) == 0)
{
lean_object* v_a_6188_; lean_object* v___x_6189_; uint8_t v___x_6190_; lean_object* v___x_6191_; 
v_a_6188_ = lean_ctor_get(v___x_6187_, 0);
lean_inc(v_a_6188_);
lean_dec_ref_known(v___x_6187_, 1);
v___x_6189_ = l_Array_append___redArg(v_xs_6171_, v_ys4_6173_);
lean_dec_ref(v_ys4_6173_);
v___x_6190_ = 1;
v___x_6191_ = l_Lean_Meta_mkLambdaFVars(v___x_6189_, v_a_6188_, v___x_6177_, v___x_6178_, v___x_6177_, v___x_6178_, v___x_6190_, v___y_6179_, v___y_6180_, v___y_6181_, v___y_6182_);
lean_dec(v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec_ref(v___x_6189_);
return v___x_6191_;
}
else
{
lean_dec(v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec_ref(v_ys4_6173_);
lean_dec_ref(v_xs_6171_);
return v___x_6187_;
}
}
else
{
lean_dec(v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec(v___y_6180_);
lean_dec_ref(v___y_6179_);
lean_dec_ref(v_altType_6176_);
lean_dec(v_a_6175_);
lean_dec_ref(v_onAlt_6174_);
lean_dec_ref(v_ys4_6173_);
lean_dec_ref(v_remaining_x27_6172_);
lean_dec_ref(v_xs_6171_);
return v___x_6184_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed(lean_object* v___x_6192_, lean_object* v_xs_6193_, lean_object* v_remaining_x27_6194_, lean_object* v_ys4_6195_, lean_object* v_onAlt_6196_, lean_object* v_a_6197_, lean_object* v_altType_6198_, lean_object* v___x_6199_, lean_object* v___x_6200_, lean_object* v___y_6201_, lean_object* v___y_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
uint8_t v___x_34986__boxed_6206_; uint8_t v___x_34987__boxed_6207_; lean_object* v_res_6208_; 
v___x_34986__boxed_6206_ = lean_unbox(v___x_6199_);
v___x_34987__boxed_6207_ = lean_unbox(v___x_6200_);
v_res_6208_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1(v___x_6192_, v_xs_6193_, v_remaining_x27_6194_, v_ys4_6195_, v_onAlt_6196_, v_a_6197_, v_altType_6198_, v___x_34986__boxed_6206_, v___x_34987__boxed_6207_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
return v_res_6208_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(lean_object* v___x_6209_, lean_object* v___f_6210_, uint8_t v___x_6211_, lean_object* v_xs_6212_, lean_object* v_remaining_x27_6213_, lean_object* v_onAlt_6214_, lean_object* v_a_6215_, uint8_t v___x_6216_, lean_object* v_ys4_6217_, lean_object* v_altType_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_, lean_object* v___y_6221_, lean_object* v___y_6222_){
_start:
{
lean_object* v___x_6224_; 
lean_inc_ref(v___x_6209_);
v___x_6224_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v___x_6209_, v___f_6210_, v___x_6211_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
if (lean_obj_tag(v___x_6224_) == 0)
{
lean_object* v_a_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___f_6228_; lean_object* v___x_6229_; 
v_a_6225_ = lean_ctor_get(v___x_6224_, 0);
lean_inc(v_a_6225_);
lean_dec_ref_known(v___x_6224_, 1);
v___x_6226_ = lean_box(v___x_6211_);
v___x_6227_ = lean_box(v___x_6216_);
lean_inc_ref(v_xs_6212_);
v___f_6228_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__1___boxed), 14, 9);
lean_closure_set(v___f_6228_, 0, v___x_6209_);
lean_closure_set(v___f_6228_, 1, v_xs_6212_);
lean_closure_set(v___f_6228_, 2, v_remaining_x27_6213_);
lean_closure_set(v___f_6228_, 3, v_ys4_6217_);
lean_closure_set(v___f_6228_, 4, v_onAlt_6214_);
lean_closure_set(v___f_6228_, 5, v_a_6215_);
lean_closure_set(v___f_6228_, 6, v_altType_6218_);
lean_closure_set(v___f_6228_, 7, v___x_6226_);
lean_closure_set(v___f_6228_, 8, v___x_6227_);
v___x_6229_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_xs_6212_, v_a_6225_, v___f_6228_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_);
lean_dec(v_a_6225_);
lean_dec_ref(v_xs_6212_);
return v___x_6229_;
}
else
{
lean_object* v_a_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6237_; 
lean_dec_ref(v_altType_6218_);
lean_dec_ref(v_ys4_6217_);
lean_dec(v_a_6215_);
lean_dec_ref(v_onAlt_6214_);
lean_dec_ref(v_remaining_x27_6213_);
lean_dec_ref(v_xs_6212_);
lean_dec_ref(v___x_6209_);
v_a_6230_ = lean_ctor_get(v___x_6224_, 0);
v_isSharedCheck_6237_ = !lean_is_exclusive(v___x_6224_);
if (v_isSharedCheck_6237_ == 0)
{
v___x_6232_ = v___x_6224_;
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
else
{
lean_inc(v_a_6230_);
lean_dec(v___x_6224_);
v___x_6232_ = lean_box(0);
v_isShared_6233_ = v_isSharedCheck_6237_;
goto v_resetjp_6231_;
}
v_resetjp_6231_:
{
lean_object* v___x_6235_; 
if (v_isShared_6233_ == 0)
{
v___x_6235_ = v___x_6232_;
goto v_reusejp_6234_;
}
else
{
lean_object* v_reuseFailAlloc_6236_; 
v_reuseFailAlloc_6236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6236_, 0, v_a_6230_);
v___x_6235_ = v_reuseFailAlloc_6236_;
goto v_reusejp_6234_;
}
v_reusejp_6234_:
{
return v___x_6235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed(lean_object* v___x_6238_, lean_object* v___f_6239_, lean_object* v___x_6240_, lean_object* v_xs_6241_, lean_object* v_remaining_x27_6242_, lean_object* v_onAlt_6243_, lean_object* v_a_6244_, lean_object* v___x_6245_, lean_object* v_ys4_6246_, lean_object* v_altType_6247_, lean_object* v___y_6248_, lean_object* v___y_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
uint8_t v___x_35029__boxed_6253_; uint8_t v___x_35030__boxed_6254_; lean_object* v_res_6255_; 
v___x_35029__boxed_6253_ = lean_unbox(v___x_6240_);
v___x_35030__boxed_6254_ = lean_unbox(v___x_6245_);
v_res_6255_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2(v___x_6238_, v___f_6239_, v___x_35029__boxed_6253_, v_xs_6241_, v_remaining_x27_6242_, v_onAlt_6243_, v_a_6244_, v___x_35030__boxed_6254_, v_ys4_6246_, v_altType_6247_, v___y_6248_, v___y_6249_, v___y_6250_, v___y_6251_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
lean_dec(v___y_6249_);
lean_dec_ref(v___y_6248_);
return v_res_6255_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(lean_object* v___x_6256_, lean_object* v___f_6257_, uint8_t v___x_6258_, lean_object* v_remaining_x27_6259_, lean_object* v_onAlt_6260_, lean_object* v_a_6261_, uint8_t v___x_6262_, lean_object* v_extraEqualities_6263_, lean_object* v_xs_6264_, lean_object* v_altType_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_){
_start:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___f_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; 
v___x_6271_ = lean_box(v___x_6258_);
v___x_6272_ = lean_box(v___x_6262_);
v___f_6273_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__2___boxed), 15, 8);
lean_closure_set(v___f_6273_, 0, v___x_6256_);
lean_closure_set(v___f_6273_, 1, v___f_6257_);
lean_closure_set(v___f_6273_, 2, v___x_6271_);
lean_closure_set(v___f_6273_, 3, v_xs_6264_);
lean_closure_set(v___f_6273_, 4, v_remaining_x27_6259_);
lean_closure_set(v___f_6273_, 5, v_onAlt_6260_);
lean_closure_set(v___f_6273_, 6, v_a_6261_);
lean_closure_set(v___f_6273_, 7, v___x_6272_);
v___x_6274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6274_, 0, v_extraEqualities_6263_);
v___x_6275_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__1___redArg(v_altType_6265_, v___x_6274_, v___f_6273_, v___x_6258_, v___x_6258_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_);
return v___x_6275_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed(lean_object* v___x_6276_, lean_object* v___f_6277_, lean_object* v___x_6278_, lean_object* v_remaining_x27_6279_, lean_object* v_onAlt_6280_, lean_object* v_a_6281_, lean_object* v___x_6282_, lean_object* v_extraEqualities_6283_, lean_object* v_xs_6284_, lean_object* v_altType_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_){
_start:
{
uint8_t v___x_35084__boxed_6291_; uint8_t v___x_35085__boxed_6292_; lean_object* v_res_6293_; 
v___x_35084__boxed_6291_ = lean_unbox(v___x_6278_);
v___x_35085__boxed_6292_ = lean_unbox(v___x_6282_);
v_res_6293_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4(v___x_6276_, v___f_6277_, v___x_35084__boxed_6291_, v_remaining_x27_6279_, v_onAlt_6280_, v_a_6281_, v___x_35085__boxed_6292_, v_extraEqualities_6283_, v_xs_6284_, v_altType_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_);
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
return v_res_6293_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(lean_object* v_upperBound_6295_, lean_object* v_onAlt_6296_, lean_object* v_extraEqualities_6297_, lean_object* v_a_6298_, lean_object* v_b_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_){
_start:
{
lean_object* v___y_6306_; uint8_t v___x_6329_; 
v___x_6329_ = lean_nat_dec_lt(v_a_6298_, v_upperBound_6295_);
if (v___x_6329_ == 0)
{
lean_object* v___x_6330_; 
lean_dec(v_a_6298_);
lean_dec(v_extraEqualities_6297_);
lean_dec_ref(v_onAlt_6296_);
v___x_6330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6330_, 0, v_b_6299_);
return v___x_6330_;
}
else
{
lean_object* v_snd_6331_; lean_object* v_snd_6332_; lean_object* v_snd_6333_; lean_object* v_fst_6334_; lean_object* v___x_6336_; uint8_t v_isShared_6337_; uint8_t v_isSharedCheck_6441_; 
v_snd_6331_ = lean_ctor_get(v_b_6299_, 1);
lean_inc(v_snd_6331_);
v_snd_6332_ = lean_ctor_get(v_snd_6331_, 1);
lean_inc(v_snd_6332_);
v_snd_6333_ = lean_ctor_get(v_snd_6332_, 1);
lean_inc(v_snd_6333_);
v_fst_6334_ = lean_ctor_get(v_b_6299_, 0);
v_isSharedCheck_6441_ = !lean_is_exclusive(v_b_6299_);
if (v_isSharedCheck_6441_ == 0)
{
lean_object* v_unused_6442_; 
v_unused_6442_ = lean_ctor_get(v_b_6299_, 1);
lean_dec(v_unused_6442_);
v___x_6336_ = v_b_6299_;
v_isShared_6337_ = v_isSharedCheck_6441_;
goto v_resetjp_6335_;
}
else
{
lean_inc(v_fst_6334_);
lean_dec(v_b_6299_);
v___x_6336_ = lean_box(0);
v_isShared_6337_ = v_isSharedCheck_6441_;
goto v_resetjp_6335_;
}
v_resetjp_6335_:
{
lean_object* v_fst_6338_; lean_object* v___x_6340_; uint8_t v_isShared_6341_; uint8_t v_isSharedCheck_6439_; 
v_fst_6338_ = lean_ctor_get(v_snd_6331_, 0);
v_isSharedCheck_6439_ = !lean_is_exclusive(v_snd_6331_);
if (v_isSharedCheck_6439_ == 0)
{
lean_object* v_unused_6440_; 
v_unused_6440_ = lean_ctor_get(v_snd_6331_, 1);
lean_dec(v_unused_6440_);
v___x_6340_ = v_snd_6331_;
v_isShared_6341_ = v_isSharedCheck_6439_;
goto v_resetjp_6339_;
}
else
{
lean_inc(v_fst_6338_);
lean_dec(v_snd_6331_);
v___x_6340_ = lean_box(0);
v_isShared_6341_ = v_isSharedCheck_6439_;
goto v_resetjp_6339_;
}
v_resetjp_6339_:
{
lean_object* v_fst_6342_; lean_object* v___x_6344_; uint8_t v_isShared_6345_; uint8_t v_isSharedCheck_6437_; 
v_fst_6342_ = lean_ctor_get(v_snd_6332_, 0);
v_isSharedCheck_6437_ = !lean_is_exclusive(v_snd_6332_);
if (v_isSharedCheck_6437_ == 0)
{
lean_object* v_unused_6438_; 
v_unused_6438_ = lean_ctor_get(v_snd_6332_, 1);
lean_dec(v_unused_6438_);
v___x_6344_ = v_snd_6332_;
v_isShared_6345_ = v_isSharedCheck_6437_;
goto v_resetjp_6343_;
}
else
{
lean_inc(v_fst_6342_);
lean_dec(v_snd_6332_);
v___x_6344_ = lean_box(0);
v_isShared_6345_ = v_isSharedCheck_6437_;
goto v_resetjp_6343_;
}
v_resetjp_6343_:
{
lean_object* v_array_6346_; lean_object* v_start_6347_; lean_object* v_stop_6348_; uint8_t v___x_6349_; 
v_array_6346_ = lean_ctor_get(v_snd_6333_, 0);
v_start_6347_ = lean_ctor_get(v_snd_6333_, 1);
v_stop_6348_ = lean_ctor_get(v_snd_6333_, 2);
v___x_6349_ = lean_nat_dec_lt(v_start_6347_, v_stop_6348_);
if (v___x_6349_ == 0)
{
lean_object* v___x_6351_; 
if (v_isShared_6345_ == 0)
{
v___x_6351_ = v___x_6344_;
goto v_reusejp_6350_;
}
else
{
lean_object* v_reuseFailAlloc_6360_; 
v_reuseFailAlloc_6360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6360_, 0, v_fst_6342_);
lean_ctor_set(v_reuseFailAlloc_6360_, 1, v_snd_6333_);
v___x_6351_ = v_reuseFailAlloc_6360_;
goto v_reusejp_6350_;
}
v_reusejp_6350_:
{
lean_object* v___x_6353_; 
if (v_isShared_6341_ == 0)
{
lean_ctor_set(v___x_6340_, 1, v___x_6351_);
v___x_6353_ = v___x_6340_;
goto v_reusejp_6352_;
}
else
{
lean_object* v_reuseFailAlloc_6359_; 
v_reuseFailAlloc_6359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6359_, 0, v_fst_6338_);
lean_ctor_set(v_reuseFailAlloc_6359_, 1, v___x_6351_);
v___x_6353_ = v_reuseFailAlloc_6359_;
goto v_reusejp_6352_;
}
v_reusejp_6352_:
{
lean_object* v___x_6355_; 
if (v_isShared_6337_ == 0)
{
lean_ctor_set(v___x_6336_, 1, v___x_6353_);
v___x_6355_ = v___x_6336_;
goto v_reusejp_6354_;
}
else
{
lean_object* v_reuseFailAlloc_6358_; 
v_reuseFailAlloc_6358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6358_, 0, v_fst_6334_);
lean_ctor_set(v_reuseFailAlloc_6358_, 1, v___x_6353_);
v___x_6355_ = v_reuseFailAlloc_6358_;
goto v_reusejp_6354_;
}
v_reusejp_6354_:
{
lean_object* v___x_6356_; lean_object* v___f_6357_; 
v___x_6356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6356_, 0, v___x_6355_);
v___f_6357_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6357_, 0, v___x_6356_);
v___y_6306_ = v___f_6357_;
goto v___jp_6305_;
}
}
}
}
else
{
lean_object* v___x_6362_; uint8_t v_isShared_6363_; uint8_t v_isSharedCheck_6433_; 
lean_inc(v_stop_6348_);
lean_inc(v_start_6347_);
lean_inc_ref(v_array_6346_);
v_isSharedCheck_6433_ = !lean_is_exclusive(v_snd_6333_);
if (v_isSharedCheck_6433_ == 0)
{
lean_object* v_unused_6434_; lean_object* v_unused_6435_; lean_object* v_unused_6436_; 
v_unused_6434_ = lean_ctor_get(v_snd_6333_, 2);
lean_dec(v_unused_6434_);
v_unused_6435_ = lean_ctor_get(v_snd_6333_, 1);
lean_dec(v_unused_6435_);
v_unused_6436_ = lean_ctor_get(v_snd_6333_, 0);
lean_dec(v_unused_6436_);
v___x_6362_ = v_snd_6333_;
v_isShared_6363_ = v_isSharedCheck_6433_;
goto v_resetjp_6361_;
}
else
{
lean_dec(v_snd_6333_);
v___x_6362_ = lean_box(0);
v_isShared_6363_ = v_isSharedCheck_6433_;
goto v_resetjp_6361_;
}
v_resetjp_6361_:
{
lean_object* v_array_6364_; lean_object* v_start_6365_; lean_object* v_stop_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6371_; 
v_array_6364_ = lean_ctor_get(v_fst_6342_, 0);
v_start_6365_ = lean_ctor_get(v_fst_6342_, 1);
v_stop_6366_ = lean_ctor_get(v_fst_6342_, 2);
v___x_6367_ = lean_array_fget(v_array_6346_, v_start_6347_);
v___x_6368_ = lean_unsigned_to_nat(1u);
v___x_6369_ = lean_nat_add(v_start_6347_, v___x_6368_);
lean_dec(v_start_6347_);
if (v_isShared_6363_ == 0)
{
lean_ctor_set(v___x_6362_, 1, v___x_6369_);
v___x_6371_ = v___x_6362_;
goto v_reusejp_6370_;
}
else
{
lean_object* v_reuseFailAlloc_6432_; 
v_reuseFailAlloc_6432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6432_, 0, v_array_6346_);
lean_ctor_set(v_reuseFailAlloc_6432_, 1, v___x_6369_);
lean_ctor_set(v_reuseFailAlloc_6432_, 2, v_stop_6348_);
v___x_6371_ = v_reuseFailAlloc_6432_;
goto v_reusejp_6370_;
}
v_reusejp_6370_:
{
uint8_t v___x_6372_; 
v___x_6372_ = lean_nat_dec_lt(v_start_6365_, v_stop_6366_);
if (v___x_6372_ == 0)
{
lean_object* v___x_6374_; 
lean_dec(v___x_6367_);
if (v_isShared_6345_ == 0)
{
lean_ctor_set(v___x_6344_, 1, v___x_6371_);
v___x_6374_ = v___x_6344_;
goto v_reusejp_6373_;
}
else
{
lean_object* v_reuseFailAlloc_6383_; 
v_reuseFailAlloc_6383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6383_, 0, v_fst_6342_);
lean_ctor_set(v_reuseFailAlloc_6383_, 1, v___x_6371_);
v___x_6374_ = v_reuseFailAlloc_6383_;
goto v_reusejp_6373_;
}
v_reusejp_6373_:
{
lean_object* v___x_6376_; 
if (v_isShared_6341_ == 0)
{
lean_ctor_set(v___x_6340_, 1, v___x_6374_);
v___x_6376_ = v___x_6340_;
goto v_reusejp_6375_;
}
else
{
lean_object* v_reuseFailAlloc_6382_; 
v_reuseFailAlloc_6382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6382_, 0, v_fst_6338_);
lean_ctor_set(v_reuseFailAlloc_6382_, 1, v___x_6374_);
v___x_6376_ = v_reuseFailAlloc_6382_;
goto v_reusejp_6375_;
}
v_reusejp_6375_:
{
lean_object* v___x_6378_; 
if (v_isShared_6337_ == 0)
{
lean_ctor_set(v___x_6336_, 1, v___x_6376_);
v___x_6378_ = v___x_6336_;
goto v_reusejp_6377_;
}
else
{
lean_object* v_reuseFailAlloc_6381_; 
v_reuseFailAlloc_6381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6381_, 0, v_fst_6334_);
lean_ctor_set(v_reuseFailAlloc_6381_, 1, v___x_6376_);
v___x_6378_ = v_reuseFailAlloc_6381_;
goto v_reusejp_6377_;
}
v_reusejp_6377_:
{
lean_object* v___x_6379_; lean_object* v___f_6380_; 
v___x_6379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6379_, 0, v___x_6378_);
v___f_6380_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6380_, 0, v___x_6379_);
v___y_6306_ = v___f_6380_;
goto v___jp_6305_;
}
}
}
}
else
{
lean_object* v___x_6385_; uint8_t v_isShared_6386_; uint8_t v_isSharedCheck_6428_; 
lean_inc(v_stop_6366_);
lean_inc(v_start_6365_);
lean_inc_ref(v_array_6364_);
v_isSharedCheck_6428_ = !lean_is_exclusive(v_fst_6342_);
if (v_isSharedCheck_6428_ == 0)
{
lean_object* v_unused_6429_; lean_object* v_unused_6430_; lean_object* v_unused_6431_; 
v_unused_6429_ = lean_ctor_get(v_fst_6342_, 2);
lean_dec(v_unused_6429_);
v_unused_6430_ = lean_ctor_get(v_fst_6342_, 1);
lean_dec(v_unused_6430_);
v_unused_6431_ = lean_ctor_get(v_fst_6342_, 0);
lean_dec(v_unused_6431_);
v___x_6385_ = v_fst_6342_;
v_isShared_6386_ = v_isSharedCheck_6428_;
goto v_resetjp_6384_;
}
else
{
lean_dec(v_fst_6342_);
v___x_6385_ = lean_box(0);
v_isShared_6386_ = v_isSharedCheck_6428_;
goto v_resetjp_6384_;
}
v_resetjp_6384_:
{
lean_object* v_array_6387_; lean_object* v_start_6388_; lean_object* v_stop_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v___x_6393_; 
v_array_6387_ = lean_ctor_get(v_fst_6338_, 0);
v_start_6388_ = lean_ctor_get(v_fst_6338_, 1);
v_stop_6389_ = lean_ctor_get(v_fst_6338_, 2);
v___x_6390_ = lean_array_fget(v_array_6364_, v_start_6365_);
v___x_6391_ = lean_nat_add(v_start_6365_, v___x_6368_);
lean_dec(v_start_6365_);
if (v_isShared_6386_ == 0)
{
lean_ctor_set(v___x_6385_, 1, v___x_6391_);
v___x_6393_ = v___x_6385_;
goto v_reusejp_6392_;
}
else
{
lean_object* v_reuseFailAlloc_6427_; 
v_reuseFailAlloc_6427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6427_, 0, v_array_6364_);
lean_ctor_set(v_reuseFailAlloc_6427_, 1, v___x_6391_);
lean_ctor_set(v_reuseFailAlloc_6427_, 2, v_stop_6366_);
v___x_6393_ = v_reuseFailAlloc_6427_;
goto v_reusejp_6392_;
}
v_reusejp_6392_:
{
uint8_t v___x_6394_; 
v___x_6394_ = lean_nat_dec_lt(v_start_6388_, v_stop_6389_);
if (v___x_6394_ == 0)
{
lean_object* v___x_6396_; 
lean_dec(v___x_6390_);
lean_dec(v___x_6367_);
if (v_isShared_6345_ == 0)
{
lean_ctor_set(v___x_6344_, 1, v___x_6371_);
lean_ctor_set(v___x_6344_, 0, v___x_6393_);
v___x_6396_ = v___x_6344_;
goto v_reusejp_6395_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v___x_6393_);
lean_ctor_set(v_reuseFailAlloc_6405_, 1, v___x_6371_);
v___x_6396_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6395_;
}
v_reusejp_6395_:
{
lean_object* v___x_6398_; 
if (v_isShared_6341_ == 0)
{
lean_ctor_set(v___x_6340_, 1, v___x_6396_);
v___x_6398_ = v___x_6340_;
goto v_reusejp_6397_;
}
else
{
lean_object* v_reuseFailAlloc_6404_; 
v_reuseFailAlloc_6404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6404_, 0, v_fst_6338_);
lean_ctor_set(v_reuseFailAlloc_6404_, 1, v___x_6396_);
v___x_6398_ = v_reuseFailAlloc_6404_;
goto v_reusejp_6397_;
}
v_reusejp_6397_:
{
lean_object* v___x_6400_; 
if (v_isShared_6337_ == 0)
{
lean_ctor_set(v___x_6336_, 1, v___x_6398_);
v___x_6400_ = v___x_6336_;
goto v_reusejp_6399_;
}
else
{
lean_object* v_reuseFailAlloc_6403_; 
v_reuseFailAlloc_6403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6403_, 0, v_fst_6334_);
lean_ctor_set(v_reuseFailAlloc_6403_, 1, v___x_6398_);
v___x_6400_ = v_reuseFailAlloc_6403_;
goto v_reusejp_6399_;
}
v_reusejp_6399_:
{
lean_object* v___x_6401_; lean_object* v___f_6402_; 
v___x_6401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6401_, 0, v___x_6400_);
v___f_6402_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__0___boxed), 6, 1);
lean_closure_set(v___f_6402_, 0, v___x_6401_);
v___y_6306_ = v___f_6402_;
goto v___jp_6305_;
}
}
}
}
else
{
lean_object* v___x_6407_; uint8_t v_isShared_6408_; uint8_t v_isSharedCheck_6423_; 
lean_inc(v_stop_6389_);
lean_inc(v_start_6388_);
lean_inc_ref(v_array_6387_);
lean_del_object(v___x_6344_);
lean_del_object(v___x_6340_);
lean_del_object(v___x_6336_);
v_isSharedCheck_6423_ = !lean_is_exclusive(v_fst_6338_);
if (v_isSharedCheck_6423_ == 0)
{
lean_object* v_unused_6424_; lean_object* v_unused_6425_; lean_object* v_unused_6426_; 
v_unused_6424_ = lean_ctor_get(v_fst_6338_, 2);
lean_dec(v_unused_6424_);
v_unused_6425_ = lean_ctor_get(v_fst_6338_, 1);
lean_dec(v_unused_6425_);
v_unused_6426_ = lean_ctor_get(v_fst_6338_, 0);
lean_dec(v_unused_6426_);
v___x_6407_ = v_fst_6338_;
v_isShared_6408_ = v_isSharedCheck_6423_;
goto v_resetjp_6406_;
}
else
{
lean_dec(v_fst_6338_);
v___x_6407_ = lean_box(0);
v_isShared_6408_ = v_isSharedCheck_6423_;
goto v_resetjp_6406_;
}
v_resetjp_6406_:
{
lean_object* v___f_6409_; uint8_t v___x_6410_; lean_object* v_remaining_x27_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___f_6415_; lean_object* v___x_6416_; lean_object* v___x_6418_; 
v___f_6409_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___closed__0));
v___x_6410_ = 0;
v_remaining_x27_6411_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6412_ = lean_array_fget_borrowed(v_array_6387_, v_start_6388_);
v___x_6413_ = lean_box(v___x_6410_);
v___x_6414_ = lean_box(v___x_6394_);
lean_inc(v_extraEqualities_6297_);
lean_inc(v_a_6298_);
lean_inc_ref(v_onAlt_6296_);
lean_inc(v___x_6412_);
v___f_6415_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__4___boxed), 15, 8);
lean_closure_set(v___f_6415_, 0, v___x_6412_);
lean_closure_set(v___f_6415_, 1, v___f_6409_);
lean_closure_set(v___f_6415_, 2, v___x_6413_);
lean_closure_set(v___f_6415_, 3, v_remaining_x27_6411_);
lean_closure_set(v___f_6415_, 4, v_onAlt_6296_);
lean_closure_set(v___f_6415_, 5, v_a_6298_);
lean_closure_set(v___f_6415_, 6, v___x_6414_);
lean_closure_set(v___f_6415_, 7, v_extraEqualities_6297_);
v___x_6416_ = lean_nat_add(v_start_6388_, v___x_6368_);
lean_dec(v_start_6388_);
if (v_isShared_6408_ == 0)
{
lean_ctor_set(v___x_6407_, 1, v___x_6416_);
v___x_6418_ = v___x_6407_;
goto v_reusejp_6417_;
}
else
{
lean_object* v_reuseFailAlloc_6422_; 
v_reuseFailAlloc_6422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6422_, 0, v_array_6387_);
lean_ctor_set(v_reuseFailAlloc_6422_, 1, v___x_6416_);
lean_ctor_set(v_reuseFailAlloc_6422_, 2, v_stop_6389_);
v___x_6418_ = v_reuseFailAlloc_6422_;
goto v_reusejp_6417_;
}
v_reusejp_6417_:
{
lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___f_6421_; 
v___x_6419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6419_, 0, v___x_6390_);
v___x_6420_ = lean_box(v___x_6410_);
v___f_6421_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___lam__5___boxed), 13, 8);
lean_closure_set(v___f_6421_, 0, v___x_6367_);
lean_closure_set(v___f_6421_, 1, v___x_6419_);
lean_closure_set(v___f_6421_, 2, v___f_6415_);
lean_closure_set(v___f_6421_, 3, v___x_6420_);
lean_closure_set(v___f_6421_, 4, v_fst_6334_);
lean_closure_set(v___f_6421_, 5, v___x_6393_);
lean_closure_set(v___f_6421_, 6, v___x_6371_);
lean_closure_set(v___f_6421_, 7, v___x_6418_);
v___y_6306_ = v___f_6421_;
goto v___jp_6305_;
}
}
}
}
}
}
}
}
}
}
}
}
}
v___jp_6305_:
{
lean_object* v___x_6307_; 
lean_inc(v___y_6303_);
lean_inc_ref(v___y_6302_);
lean_inc(v___y_6301_);
lean_inc_ref(v___y_6300_);
v___x_6307_ = lean_apply_5(v___y_6306_, v___y_6300_, v___y_6301_, v___y_6302_, v___y_6303_, lean_box(0));
if (lean_obj_tag(v___x_6307_) == 0)
{
lean_object* v_a_6308_; lean_object* v___x_6310_; uint8_t v_isShared_6311_; uint8_t v_isSharedCheck_6320_; 
v_a_6308_ = lean_ctor_get(v___x_6307_, 0);
v_isSharedCheck_6320_ = !lean_is_exclusive(v___x_6307_);
if (v_isSharedCheck_6320_ == 0)
{
v___x_6310_ = v___x_6307_;
v_isShared_6311_ = v_isSharedCheck_6320_;
goto v_resetjp_6309_;
}
else
{
lean_inc(v_a_6308_);
lean_dec(v___x_6307_);
v___x_6310_ = lean_box(0);
v_isShared_6311_ = v_isSharedCheck_6320_;
goto v_resetjp_6309_;
}
v_resetjp_6309_:
{
if (lean_obj_tag(v_a_6308_) == 0)
{
lean_object* v_a_6312_; lean_object* v___x_6314_; 
lean_dec(v_a_6298_);
lean_dec(v_extraEqualities_6297_);
lean_dec_ref(v_onAlt_6296_);
v_a_6312_ = lean_ctor_get(v_a_6308_, 0);
lean_inc(v_a_6312_);
lean_dec_ref_known(v_a_6308_, 1);
if (v_isShared_6311_ == 0)
{
lean_ctor_set(v___x_6310_, 0, v_a_6312_);
v___x_6314_ = v___x_6310_;
goto v_reusejp_6313_;
}
else
{
lean_object* v_reuseFailAlloc_6315_; 
v_reuseFailAlloc_6315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6315_, 0, v_a_6312_);
v___x_6314_ = v_reuseFailAlloc_6315_;
goto v_reusejp_6313_;
}
v_reusejp_6313_:
{
return v___x_6314_;
}
}
else
{
lean_object* v_a_6316_; lean_object* v___x_6317_; lean_object* v___x_6318_; 
lean_del_object(v___x_6310_);
v_a_6316_ = lean_ctor_get(v_a_6308_, 0);
lean_inc(v_a_6316_);
lean_dec_ref_known(v_a_6308_, 1);
v___x_6317_ = lean_unsigned_to_nat(1u);
v___x_6318_ = lean_nat_add(v_a_6298_, v___x_6317_);
lean_dec(v_a_6298_);
v_a_6298_ = v___x_6318_;
v_b_6299_ = v_a_6316_;
goto _start;
}
}
}
else
{
lean_object* v_a_6321_; lean_object* v___x_6323_; uint8_t v_isShared_6324_; uint8_t v_isSharedCheck_6328_; 
lean_dec(v_a_6298_);
lean_dec(v_extraEqualities_6297_);
lean_dec_ref(v_onAlt_6296_);
v_a_6321_ = lean_ctor_get(v___x_6307_, 0);
v_isSharedCheck_6328_ = !lean_is_exclusive(v___x_6307_);
if (v_isSharedCheck_6328_ == 0)
{
v___x_6323_ = v___x_6307_;
v_isShared_6324_ = v_isSharedCheck_6328_;
goto v_resetjp_6322_;
}
else
{
lean_inc(v_a_6321_);
lean_dec(v___x_6307_);
v___x_6323_ = lean_box(0);
v_isShared_6324_ = v_isSharedCheck_6328_;
goto v_resetjp_6322_;
}
v_resetjp_6322_:
{
lean_object* v___x_6326_; 
if (v_isShared_6324_ == 0)
{
v___x_6326_ = v___x_6323_;
goto v_reusejp_6325_;
}
else
{
lean_object* v_reuseFailAlloc_6327_; 
v_reuseFailAlloc_6327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6327_, 0, v_a_6321_);
v___x_6326_ = v_reuseFailAlloc_6327_;
goto v_reusejp_6325_;
}
v_reusejp_6325_:
{
return v___x_6326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg___boxed(lean_object* v_upperBound_6443_, lean_object* v_onAlt_6444_, lean_object* v_extraEqualities_6445_, lean_object* v_a_6446_, lean_object* v_b_6447_, lean_object* v___y_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_){
_start:
{
lean_object* v_res_6453_; 
v_res_6453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_6443_, v_onAlt_6444_, v_extraEqualities_6445_, v_a_6446_, v_b_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_);
lean_dec(v___y_6451_);
lean_dec_ref(v___y_6450_);
lean_dec(v___y_6449_);
lean_dec_ref(v___y_6448_);
lean_dec(v_upperBound_6443_);
return v_res_6453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(lean_object* v_onParams_6454_, size_t v_sz_6455_, size_t v_i_6456_, lean_object* v_bs_6457_, lean_object* v___y_6458_, lean_object* v___y_6459_, lean_object* v___y_6460_, lean_object* v___y_6461_){
_start:
{
uint8_t v___x_6463_; 
v___x_6463_ = lean_usize_dec_lt(v_i_6456_, v_sz_6455_);
if (v___x_6463_ == 0)
{
lean_object* v___x_6464_; 
lean_dec_ref(v_onParams_6454_);
v___x_6464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6464_, 0, v_bs_6457_);
return v___x_6464_;
}
else
{
lean_object* v_v_6465_; lean_object* v___x_6466_; 
v_v_6465_ = lean_array_uget_borrowed(v_bs_6457_, v_i_6456_);
lean_inc_ref(v_onParams_6454_);
lean_inc(v___y_6461_);
lean_inc_ref(v___y_6460_);
lean_inc(v___y_6459_);
lean_inc_ref(v___y_6458_);
lean_inc(v_v_6465_);
v___x_6466_ = lean_apply_6(v_onParams_6454_, v_v_6465_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, lean_box(0));
if (lean_obj_tag(v___x_6466_) == 0)
{
lean_object* v_a_6467_; lean_object* v___x_6468_; lean_object* v_bs_x27_6469_; size_t v___x_6470_; size_t v___x_6471_; lean_object* v___x_6472_; 
v_a_6467_ = lean_ctor_get(v___x_6466_, 0);
lean_inc(v_a_6467_);
lean_dec_ref_known(v___x_6466_, 1);
v___x_6468_ = lean_unsigned_to_nat(0u);
v_bs_x27_6469_ = lean_array_uset(v_bs_6457_, v_i_6456_, v___x_6468_);
v___x_6470_ = ((size_t)1ULL);
v___x_6471_ = lean_usize_add(v_i_6456_, v___x_6470_);
v___x_6472_ = lean_array_uset(v_bs_x27_6469_, v_i_6456_, v_a_6467_);
v_i_6456_ = v___x_6471_;
v_bs_6457_ = v___x_6472_;
goto _start;
}
else
{
lean_object* v_a_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6481_; 
lean_dec_ref(v_bs_6457_);
lean_dec_ref(v_onParams_6454_);
v_a_6474_ = lean_ctor_get(v___x_6466_, 0);
v_isSharedCheck_6481_ = !lean_is_exclusive(v___x_6466_);
if (v_isSharedCheck_6481_ == 0)
{
v___x_6476_ = v___x_6466_;
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_a_6474_);
lean_dec(v___x_6466_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v___x_6479_; 
if (v_isShared_6477_ == 0)
{
v___x_6479_ = v___x_6476_;
goto v_reusejp_6478_;
}
else
{
lean_object* v_reuseFailAlloc_6480_; 
v_reuseFailAlloc_6480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6480_, 0, v_a_6474_);
v___x_6479_ = v_reuseFailAlloc_6480_;
goto v_reusejp_6478_;
}
v_reusejp_6478_:
{
return v___x_6479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6___boxed(lean_object* v_onParams_6482_, lean_object* v_sz_6483_, lean_object* v_i_6484_, lean_object* v_bs_6485_, lean_object* v___y_6486_, lean_object* v___y_6487_, lean_object* v___y_6488_, lean_object* v___y_6489_, lean_object* v___y_6490_){
_start:
{
size_t v_sz_boxed_6491_; size_t v_i_boxed_6492_; lean_object* v_res_6493_; 
v_sz_boxed_6491_ = lean_unbox_usize(v_sz_6483_);
lean_dec(v_sz_6483_);
v_i_boxed_6492_ = lean_unbox_usize(v_i_6484_);
lean_dec(v_i_6484_);
v_res_6493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6482_, v_sz_boxed_6491_, v_i_boxed_6492_, v_bs_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_);
lean_dec(v___y_6489_);
lean_dec_ref(v___y_6488_);
lean_dec(v___y_6487_);
lean_dec_ref(v___y_6486_);
return v_res_6493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(lean_object* v_declName_6494_, lean_object* v___y_6495_){
_start:
{
lean_object* v___x_6497_; lean_object* v_env_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v___x_6497_ = lean_st_ref_get(v___y_6495_);
v_env_6498_ = lean_ctor_get(v___x_6497_, 0);
lean_inc_ref(v_env_6498_);
lean_dec(v___x_6497_);
v___x_6499_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6498_, v_declName_6494_);
v___x_6500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6500_, 0, v___x_6499_);
return v___x_6500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg___boxed(lean_object* v_declName_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_){
_start:
{
lean_object* v_res_6504_; 
v_res_6504_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_6501_, v___y_6502_);
lean_dec(v___y_6502_);
return v_res_6504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(lean_object* v_matcherApp_6507_, uint8_t v_useSplitter_6508_, uint8_t v_addEqualities_6509_, lean_object* v_onParams_6510_, lean_object* v_onMotive_6511_, lean_object* v_onAlt_6512_, lean_object* v_onRemaining_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_){
_start:
{
lean_object* v___x_6519_; lean_object* v_env_6520_; lean_object* v_toMatcherInfo_6521_; lean_object* v_matcherName_6522_; lean_object* v_matcherLevels_6523_; lean_object* v_params_6524_; lean_object* v_motive_6525_; lean_object* v_discrs_6526_; lean_object* v_alts_6527_; lean_object* v_remaining_6528_; lean_object* v___y_6530_; lean_object* v___y_6531_; lean_object* v___y_6532_; lean_object* v___y_6533_; lean_object* v___y_6534_; lean_object* v___y_6535_; lean_object* v___y_6536_; lean_object* v___y_6537_; lean_object* v___y_6538_; lean_object* v___y_6539_; lean_object* v___y_6540_; lean_object* v___y_6541_; lean_object* v___y_6542_; uint8_t v_isCasesOn_6627_; lean_object* v___y_6629_; lean_object* v___y_6630_; lean_object* v___y_6631_; size_t v___y_6632_; lean_object* v___y_6633_; lean_object* v___y_6634_; lean_object* v___y_6635_; lean_object* v_matcherLevels_6636_; lean_object* v___y_6637_; lean_object* v___y_6638_; lean_object* v___y_6639_; lean_object* v___y_6640_; lean_object* v_numDiscrEqs_6833_; lean_object* v___y_6834_; lean_object* v___y_6835_; lean_object* v___y_6836_; lean_object* v___y_6837_; 
v___x_6519_ = lean_st_ref_get(v___y_6517_);
v_env_6520_ = lean_ctor_get(v___x_6519_, 0);
lean_inc_ref(v_env_6520_);
lean_dec(v___x_6519_);
v_toMatcherInfo_6521_ = lean_ctor_get(v_matcherApp_6507_, 0);
lean_inc_ref(v_toMatcherInfo_6521_);
v_matcherName_6522_ = lean_ctor_get(v_matcherApp_6507_, 1);
lean_inc_n(v_matcherName_6522_, 2);
v_matcherLevels_6523_ = lean_ctor_get(v_matcherApp_6507_, 2);
v_params_6524_ = lean_ctor_get(v_matcherApp_6507_, 3);
v_motive_6525_ = lean_ctor_get(v_matcherApp_6507_, 4);
v_discrs_6526_ = lean_ctor_get(v_matcherApp_6507_, 5);
v_alts_6527_ = lean_ctor_get(v_matcherApp_6507_, 6);
lean_inc_ref(v_alts_6527_);
v_remaining_6528_ = lean_ctor_get(v_matcherApp_6507_, 7);
lean_inc_ref(v_remaining_6528_);
v_isCasesOn_6627_ = l_Lean_isCasesOnRecursor(v_env_6520_, v_matcherName_6522_);
if (v_isCasesOn_6627_ == 0)
{
lean_object* v___x_6887_; lean_object* v_a_6888_; 
lean_inc(v_matcherName_6522_);
v___x_6887_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_matcherName_6522_, v___y_6517_);
v_a_6888_ = lean_ctor_get(v___x_6887_, 0);
lean_inc(v_a_6888_);
lean_dec_ref(v___x_6887_);
if (lean_obj_tag(v_a_6888_) == 0)
{
lean_object* v___x_6889_; lean_object* v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; lean_object* v___x_6893_; lean_object* v___x_6894_; lean_object* v_a_6895_; lean_object* v___x_6897_; uint8_t v_isShared_6898_; uint8_t v_isSharedCheck_6902_; 
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
lean_dec_ref(v_onMotive_6511_);
lean_dec_ref(v_onParams_6510_);
lean_dec_ref(v_matcherApp_6507_);
v___x_6889_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__1);
v___x_6890_ = l_Lean_MessageData_ofName(v_matcherName_6522_);
v___x_6891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6891_, 0, v___x_6889_);
lean_ctor_set(v___x_6891_, 1, v___x_6890_);
v___x_6892_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__63___closed__3);
v___x_6893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6893_, 0, v___x_6891_);
lean_ctor_set(v___x_6893_, 1, v___x_6892_);
v___x_6894_ = l_Lean_throwError___at___00__private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_updateAlts_spec__0___redArg(v___x_6893_, v___y_6514_, v___y_6515_, v___y_6516_, v___y_6517_);
v_a_6895_ = lean_ctor_get(v___x_6894_, 0);
v_isSharedCheck_6902_ = !lean_is_exclusive(v___x_6894_);
if (v_isSharedCheck_6902_ == 0)
{
v___x_6897_ = v___x_6894_;
v_isShared_6898_ = v_isSharedCheck_6902_;
goto v_resetjp_6896_;
}
else
{
lean_inc(v_a_6895_);
lean_dec(v___x_6894_);
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
else
{
lean_object* v_val_6903_; lean_object* v___x_6904_; 
v_val_6903_ = lean_ctor_get(v_a_6888_, 0);
lean_inc(v_val_6903_);
lean_dec_ref_known(v_a_6888_, 1);
v___x_6904_ = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(v_val_6903_);
lean_dec(v_val_6903_);
v_numDiscrEqs_6833_ = v___x_6904_;
v___y_6834_ = v___y_6514_;
v___y_6835_ = v___y_6515_;
v___y_6836_ = v___y_6516_;
v___y_6837_ = v___y_6517_;
goto v___jp_6832_;
}
}
else
{
lean_object* v___x_6905_; 
v___x_6905_ = lean_unsigned_to_nat(0u);
v_numDiscrEqs_6833_ = v___x_6905_;
v___y_6834_ = v___y_6514_;
v___y_6835_ = v___y_6515_;
v___y_6836_ = v___y_6516_;
v___y_6837_ = v___y_6517_;
goto v___jp_6832_;
}
v___jp_6529_:
{
lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v_aux_6545_; lean_object* v_aux_6546_; lean_object* v_aux_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___f_6551_; uint8_t v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; 
lean_inc_ref(v___y_6530_);
v___x_6543_ = lean_array_to_list(v___y_6530_);
lean_inc(v_matcherName_6522_);
v___x_6544_ = l_Lean_mkConst(v_matcherName_6522_, v___x_6543_);
v_aux_6545_ = l_Lean_mkAppN(v___x_6544_, v___y_6541_);
lean_inc_ref(v___y_6533_);
v_aux_6546_ = l_Lean_Expr_app___override(v_aux_6545_, v___y_6533_);
v_aux_6547_ = l_Lean_mkAppN(v_aux_6546_, v___y_6537_);
v___x_6548_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__1);
lean_inc_ref_n(v_aux_6547_, 2);
v___x_6549_ = l_Lean_indentExpr(v_aux_6547_);
v___x_6550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6550_, 0, v___x_6548_);
lean_ctor_set(v___x_6550_, 1, v___x_6549_);
v___f_6551_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6551_, 0, v___x_6550_);
v___x_6552_ = 0;
v___x_6553_ = lean_box(v___x_6552_);
v___x_6554_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6554_, 0, v_aux_6547_);
lean_closure_set(v___x_6554_, 1, v___x_6553_);
v___x_6555_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6554_, v___f_6551_, v___y_6534_, v___y_6538_, v___y_6542_, v___y_6539_);
if (lean_obj_tag(v___x_6555_) == 0)
{
lean_object* v___x_6556_; lean_object* v___x_6557_; 
lean_dec_ref_known(v___x_6555_, 1);
v___x_6556_ = lean_array_get_size(v_alts_6527_);
v___x_6557_ = l_Lean_Meta_inferArgumentTypesN(v___x_6556_, v_aux_6547_, v___y_6534_, v___y_6538_, v___y_6542_, v___y_6539_);
if (lean_obj_tag(v___x_6557_) == 0)
{
lean_object* v_a_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___x_6568_; 
v_a_6558_ = lean_ctor_get(v___x_6557_, 0);
lean_inc(v_a_6558_);
lean_dec_ref_known(v___x_6557_, 1);
v___x_6559_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_6507_);
v___x_6560_ = lean_array_get_size(v___x_6559_);
v___x_6561_ = lean_array_get_size(v_a_6558_);
lean_inc_n(v___y_6540_, 3);
v___x_6562_ = l_Array_toSubarray___redArg(v_alts_6527_, v___y_6540_, v___x_6556_);
v___x_6563_ = l_Array_toSubarray___redArg(v___x_6559_, v___y_6540_, v___x_6560_);
v___x_6564_ = l_Array_toSubarray___redArg(v_a_6558_, v___y_6540_, v___x_6561_);
v___x_6565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6565_, 0, v___x_6563_);
lean_ctor_set(v___x_6565_, 1, v___x_6564_);
v___x_6566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6566_, 0, v___x_6562_);
lean_ctor_set(v___x_6566_, 1, v___x_6565_);
lean_inc_ref(v___y_6535_);
v___x_6567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6567_, 0, v___y_6535_);
lean_ctor_set(v___x_6567_, 1, v___x_6566_);
v___x_6568_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v___x_6556_, v_onAlt_6512_, v___y_6536_, v___y_6540_, v___x_6567_, v___y_6534_, v___y_6538_, v___y_6542_, v___y_6539_);
if (lean_obj_tag(v___x_6568_) == 0)
{
lean_object* v_a_6569_; lean_object* v_fst_6570_; lean_object* v___x_6571_; 
v_a_6569_ = lean_ctor_get(v___x_6568_, 0);
lean_inc(v_a_6569_);
lean_dec_ref_known(v___x_6568_, 1);
v_fst_6570_ = lean_ctor_get(v_a_6569_, 0);
lean_inc(v_fst_6570_);
lean_dec(v_a_6569_);
lean_inc(v___y_6539_);
lean_inc_ref(v___y_6542_);
lean_inc(v___y_6538_);
lean_inc_ref(v___y_6534_);
v___x_6571_ = lean_apply_6(v_onRemaining_6513_, v_remaining_6528_, v___y_6534_, v___y_6538_, v___y_6542_, v___y_6539_, lean_box(0));
if (lean_obj_tag(v___x_6571_) == 0)
{
lean_object* v_a_6572_; lean_object* v___x_6574_; uint8_t v_isShared_6575_; uint8_t v_isSharedCheck_6594_; 
v_a_6572_ = lean_ctor_get(v___x_6571_, 0);
v_isSharedCheck_6594_ = !lean_is_exclusive(v___x_6571_);
if (v_isSharedCheck_6594_ == 0)
{
v___x_6574_ = v___x_6571_;
v_isShared_6575_ = v_isSharedCheck_6594_;
goto v_resetjp_6573_;
}
else
{
lean_inc(v_a_6572_);
lean_dec(v___x_6571_);
v___x_6574_ = lean_box(0);
v_isShared_6575_ = v_isSharedCheck_6594_;
goto v_resetjp_6573_;
}
v_resetjp_6573_:
{
lean_object* v_numParams_6576_; lean_object* v_numDiscrs_6577_; lean_object* v_altInfos_6578_; lean_object* v_uElimPos_x3f_6579_; lean_object* v_overlaps_6580_; lean_object* v___x_6582_; uint8_t v_isShared_6583_; uint8_t v_isSharedCheck_6592_; 
v_numParams_6576_ = lean_ctor_get(v_toMatcherInfo_6521_, 0);
v_numDiscrs_6577_ = lean_ctor_get(v_toMatcherInfo_6521_, 1);
v_altInfos_6578_ = lean_ctor_get(v_toMatcherInfo_6521_, 2);
v_uElimPos_x3f_6579_ = lean_ctor_get(v_toMatcherInfo_6521_, 3);
v_overlaps_6580_ = lean_ctor_get(v_toMatcherInfo_6521_, 5);
v_isSharedCheck_6592_ = !lean_is_exclusive(v_toMatcherInfo_6521_);
if (v_isSharedCheck_6592_ == 0)
{
lean_object* v_unused_6593_; 
v_unused_6593_ = lean_ctor_get(v_toMatcherInfo_6521_, 4);
lean_dec(v_unused_6593_);
v___x_6582_ = v_toMatcherInfo_6521_;
v_isShared_6583_ = v_isSharedCheck_6592_;
goto v_resetjp_6581_;
}
else
{
lean_inc(v_overlaps_6580_);
lean_inc(v_uElimPos_x3f_6579_);
lean_inc(v_altInfos_6578_);
lean_inc(v_numDiscrs_6577_);
lean_inc(v_numParams_6576_);
lean_dec(v_toMatcherInfo_6521_);
v___x_6582_ = lean_box(0);
v_isShared_6583_ = v_isSharedCheck_6592_;
goto v_resetjp_6581_;
}
v_resetjp_6581_:
{
lean_object* v_remaining_x27_6584_; lean_object* v___x_6586_; 
v_remaining_x27_6584_ = l_Array_append___redArg(v___y_6532_, v_a_6572_);
lean_dec(v_a_6572_);
if (v_isShared_6583_ == 0)
{
lean_ctor_set(v___x_6582_, 4, v___y_6531_);
v___x_6586_ = v___x_6582_;
goto v_reusejp_6585_;
}
else
{
lean_object* v_reuseFailAlloc_6591_; 
v_reuseFailAlloc_6591_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6591_, 0, v_numParams_6576_);
lean_ctor_set(v_reuseFailAlloc_6591_, 1, v_numDiscrs_6577_);
lean_ctor_set(v_reuseFailAlloc_6591_, 2, v_altInfos_6578_);
lean_ctor_set(v_reuseFailAlloc_6591_, 3, v_uElimPos_x3f_6579_);
lean_ctor_set(v_reuseFailAlloc_6591_, 4, v___y_6531_);
lean_ctor_set(v_reuseFailAlloc_6591_, 5, v_overlaps_6580_);
v___x_6586_ = v_reuseFailAlloc_6591_;
goto v_reusejp_6585_;
}
v_reusejp_6585_:
{
lean_object* v___x_6587_; lean_object* v___x_6589_; 
v___x_6587_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6587_, 0, v___x_6586_);
lean_ctor_set(v___x_6587_, 1, v_matcherName_6522_);
lean_ctor_set(v___x_6587_, 2, v___y_6530_);
lean_ctor_set(v___x_6587_, 3, v___y_6541_);
lean_ctor_set(v___x_6587_, 4, v___y_6533_);
lean_ctor_set(v___x_6587_, 5, v___y_6537_);
lean_ctor_set(v___x_6587_, 6, v_fst_6570_);
lean_ctor_set(v___x_6587_, 7, v_remaining_x27_6584_);
if (v_isShared_6575_ == 0)
{
lean_ctor_set(v___x_6574_, 0, v___x_6587_);
v___x_6589_ = v___x_6574_;
goto v_reusejp_6588_;
}
else
{
lean_object* v_reuseFailAlloc_6590_; 
v_reuseFailAlloc_6590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6590_, 0, v___x_6587_);
v___x_6589_ = v_reuseFailAlloc_6590_;
goto v_reusejp_6588_;
}
v_reusejp_6588_:
{
return v___x_6589_;
}
}
}
}
}
else
{
lean_object* v_a_6595_; lean_object* v___x_6597_; uint8_t v_isShared_6598_; uint8_t v_isSharedCheck_6602_; 
lean_dec(v_fst_6570_);
lean_dec_ref(v___y_6541_);
lean_dec_ref(v___y_6537_);
lean_dec_ref(v___y_6533_);
lean_dec(v___y_6532_);
lean_dec_ref(v___y_6531_);
lean_dec_ref(v___y_6530_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
v_a_6595_ = lean_ctor_get(v___x_6571_, 0);
v_isSharedCheck_6602_ = !lean_is_exclusive(v___x_6571_);
if (v_isSharedCheck_6602_ == 0)
{
v___x_6597_ = v___x_6571_;
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
else
{
lean_inc(v_a_6595_);
lean_dec(v___x_6571_);
v___x_6597_ = lean_box(0);
v_isShared_6598_ = v_isSharedCheck_6602_;
goto v_resetjp_6596_;
}
v_resetjp_6596_:
{
lean_object* v___x_6600_; 
if (v_isShared_6598_ == 0)
{
v___x_6600_ = v___x_6597_;
goto v_reusejp_6599_;
}
else
{
lean_object* v_reuseFailAlloc_6601_; 
v_reuseFailAlloc_6601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6601_, 0, v_a_6595_);
v___x_6600_ = v_reuseFailAlloc_6601_;
goto v_reusejp_6599_;
}
v_reusejp_6599_:
{
return v___x_6600_;
}
}
}
}
else
{
lean_object* v_a_6603_; lean_object* v___x_6605_; uint8_t v_isShared_6606_; uint8_t v_isSharedCheck_6610_; 
lean_dec_ref(v___y_6541_);
lean_dec_ref(v___y_6537_);
lean_dec_ref(v___y_6533_);
lean_dec(v___y_6532_);
lean_dec_ref(v___y_6531_);
lean_dec_ref(v___y_6530_);
lean_dec_ref(v_remaining_6528_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
v_a_6603_ = lean_ctor_get(v___x_6568_, 0);
v_isSharedCheck_6610_ = !lean_is_exclusive(v___x_6568_);
if (v_isSharedCheck_6610_ == 0)
{
v___x_6605_ = v___x_6568_;
v_isShared_6606_ = v_isSharedCheck_6610_;
goto v_resetjp_6604_;
}
else
{
lean_inc(v_a_6603_);
lean_dec(v___x_6568_);
v___x_6605_ = lean_box(0);
v_isShared_6606_ = v_isSharedCheck_6610_;
goto v_resetjp_6604_;
}
v_resetjp_6604_:
{
lean_object* v___x_6608_; 
if (v_isShared_6606_ == 0)
{
v___x_6608_ = v___x_6605_;
goto v_reusejp_6607_;
}
else
{
lean_object* v_reuseFailAlloc_6609_; 
v_reuseFailAlloc_6609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6609_, 0, v_a_6603_);
v___x_6608_ = v_reuseFailAlloc_6609_;
goto v_reusejp_6607_;
}
v_reusejp_6607_:
{
return v___x_6608_;
}
}
}
}
else
{
lean_object* v_a_6611_; lean_object* v___x_6613_; uint8_t v_isShared_6614_; uint8_t v_isSharedCheck_6618_; 
lean_dec_ref(v___y_6541_);
lean_dec(v___y_6540_);
lean_dec_ref(v___y_6537_);
lean_dec(v___y_6536_);
lean_dec_ref(v___y_6533_);
lean_dec(v___y_6532_);
lean_dec_ref(v___y_6531_);
lean_dec_ref(v___y_6530_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
lean_dec_ref(v_matcherApp_6507_);
v_a_6611_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6618_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6618_ == 0)
{
v___x_6613_ = v___x_6557_;
v_isShared_6614_ = v_isSharedCheck_6618_;
goto v_resetjp_6612_;
}
else
{
lean_inc(v_a_6611_);
lean_dec(v___x_6557_);
v___x_6613_ = lean_box(0);
v_isShared_6614_ = v_isSharedCheck_6618_;
goto v_resetjp_6612_;
}
v_resetjp_6612_:
{
lean_object* v___x_6616_; 
if (v_isShared_6614_ == 0)
{
v___x_6616_ = v___x_6613_;
goto v_reusejp_6615_;
}
else
{
lean_object* v_reuseFailAlloc_6617_; 
v_reuseFailAlloc_6617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6617_, 0, v_a_6611_);
v___x_6616_ = v_reuseFailAlloc_6617_;
goto v_reusejp_6615_;
}
v_reusejp_6615_:
{
return v___x_6616_;
}
}
}
}
else
{
lean_object* v_a_6619_; lean_object* v___x_6621_; uint8_t v_isShared_6622_; uint8_t v_isSharedCheck_6626_; 
lean_dec_ref(v_aux_6547_);
lean_dec_ref(v___y_6541_);
lean_dec(v___y_6540_);
lean_dec_ref(v___y_6537_);
lean_dec(v___y_6536_);
lean_dec_ref(v___y_6533_);
lean_dec(v___y_6532_);
lean_dec_ref(v___y_6531_);
lean_dec_ref(v___y_6530_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
lean_dec_ref(v_matcherApp_6507_);
v_a_6619_ = lean_ctor_get(v___x_6555_, 0);
v_isSharedCheck_6626_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6626_ == 0)
{
v___x_6621_ = v___x_6555_;
v_isShared_6622_ = v_isSharedCheck_6626_;
goto v_resetjp_6620_;
}
else
{
lean_inc(v_a_6619_);
lean_dec(v___x_6555_);
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
v___jp_6628_:
{
lean_object* v___x_6641_; lean_object* v_remaining_x27_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; lean_object* v___x_6648_; size_t v_sz_6649_; lean_object* v___x_6650_; 
v___x_6641_ = lean_unsigned_to_nat(0u);
v_remaining_x27_6642_ = ((lean_object*)(l_Lean_Meta_MatcherApp_refineThrough___lam__0___closed__0));
v___x_6643_ = l_Array_reverse___redArg(v___y_6629_);
v___x_6644_ = lean_array_get_size(v___x_6643_);
v___x_6645_ = l_Array_toSubarray___redArg(v___x_6643_, v___x_6641_, v___x_6644_);
lean_inc_ref(v___y_6630_);
v___x_6646_ = l_Array_reverse___redArg(v___y_6630_);
v___x_6647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6647_, 0, v___x_6641_);
lean_ctor_set(v___x_6647_, 1, v___x_6645_);
v___x_6648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6648_, 0, v_remaining_x27_6642_);
lean_ctor_set(v___x_6648_, 1, v___x_6647_);
v_sz_6649_ = lean_array_size(v___x_6646_);
v___x_6650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__8(v___x_6646_, v_sz_6649_, v___y_6632_, v___x_6648_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
lean_dec_ref(v___x_6646_);
if (lean_obj_tag(v___x_6650_) == 0)
{
lean_object* v_a_6651_; lean_object* v_snd_6652_; 
v_a_6651_ = lean_ctor_get(v___x_6650_, 0);
lean_inc(v_a_6651_);
lean_dec_ref_known(v___x_6650_, 1);
v_snd_6652_ = lean_ctor_get(v_a_6651_, 1);
lean_inc(v_snd_6652_);
if (v_useSplitter_6508_ == 0)
{
lean_object* v_fst_6653_; lean_object* v_fst_6654_; 
lean_dec(v___y_6634_);
v_fst_6653_ = lean_ctor_get(v_a_6651_, 0);
lean_inc(v_fst_6653_);
lean_dec(v_a_6651_);
v_fst_6654_ = lean_ctor_get(v_snd_6652_, 0);
lean_inc(v_fst_6654_);
lean_dec(v_snd_6652_);
v___y_6530_ = v_matcherLevels_6636_;
v___y_6531_ = v___y_6631_;
v___y_6532_ = v_fst_6653_;
v___y_6533_ = v___y_6633_;
v___y_6534_ = v___y_6637_;
v___y_6535_ = v_remaining_x27_6642_;
v___y_6536_ = v_fst_6654_;
v___y_6537_ = v___y_6630_;
v___y_6538_ = v___y_6638_;
v___y_6539_ = v___y_6640_;
v___y_6540_ = v___x_6641_;
v___y_6541_ = v___y_6635_;
v___y_6542_ = v___y_6639_;
goto v___jp_6529_;
}
else
{
lean_object* v_fst_6655_; lean_object* v___x_6657_; uint8_t v_isShared_6658_; uint8_t v_isSharedCheck_6822_; 
v_fst_6655_ = lean_ctor_get(v_a_6651_, 0);
v_isSharedCheck_6822_ = !lean_is_exclusive(v_a_6651_);
if (v_isSharedCheck_6822_ == 0)
{
lean_object* v_unused_6823_; 
v_unused_6823_ = lean_ctor_get(v_a_6651_, 1);
lean_dec(v_unused_6823_);
v___x_6657_ = v_a_6651_;
v_isShared_6658_ = v_isSharedCheck_6822_;
goto v_resetjp_6656_;
}
else
{
lean_inc(v_fst_6655_);
lean_dec(v_a_6651_);
v___x_6657_ = lean_box(0);
v_isShared_6658_ = v_isSharedCheck_6822_;
goto v_resetjp_6656_;
}
v_resetjp_6656_:
{
lean_object* v_fst_6659_; lean_object* v___x_6661_; uint8_t v_isShared_6662_; uint8_t v_isSharedCheck_6820_; 
v_fst_6659_ = lean_ctor_get(v_snd_6652_, 0);
v_isSharedCheck_6820_ = !lean_is_exclusive(v_snd_6652_);
if (v_isSharedCheck_6820_ == 0)
{
lean_object* v_unused_6821_; 
v_unused_6821_ = lean_ctor_get(v_snd_6652_, 1);
lean_dec(v_unused_6821_);
v___x_6661_ = v_snd_6652_;
v_isShared_6662_ = v_isSharedCheck_6820_;
goto v_resetjp_6660_;
}
else
{
lean_inc(v_fst_6659_);
lean_dec(v_snd_6652_);
v___x_6661_ = lean_box(0);
v_isShared_6662_ = v_isSharedCheck_6820_;
goto v_resetjp_6660_;
}
v_resetjp_6660_:
{
uint8_t v___x_6663_; 
v___x_6663_ = lean_bool_not(v_isCasesOn_6627_);
if (v___x_6663_ == 0)
{
lean_del_object(v___x_6661_);
lean_del_object(v___x_6657_);
lean_dec(v___y_6634_);
v___y_6530_ = v_matcherLevels_6636_;
v___y_6531_ = v___y_6631_;
v___y_6532_ = v_fst_6655_;
v___y_6533_ = v___y_6633_;
v___y_6534_ = v___y_6637_;
v___y_6535_ = v_remaining_x27_6642_;
v___y_6536_ = v_fst_6659_;
v___y_6537_ = v___y_6630_;
v___y_6538_ = v___y_6638_;
v___y_6539_ = v___y_6640_;
v___y_6540_ = v___x_6641_;
v___y_6541_ = v___y_6635_;
v___y_6542_ = v___y_6639_;
goto v___jp_6529_;
}
else
{
lean_object* v___x_6665_; uint8_t v_isShared_6666_; uint8_t v_isSharedCheck_6811_; 
v_isSharedCheck_6811_ = !lean_is_exclusive(v_matcherApp_6507_);
if (v_isSharedCheck_6811_ == 0)
{
lean_object* v_unused_6812_; lean_object* v_unused_6813_; lean_object* v_unused_6814_; lean_object* v_unused_6815_; lean_object* v_unused_6816_; lean_object* v_unused_6817_; lean_object* v_unused_6818_; lean_object* v_unused_6819_; 
v_unused_6812_ = lean_ctor_get(v_matcherApp_6507_, 7);
lean_dec(v_unused_6812_);
v_unused_6813_ = lean_ctor_get(v_matcherApp_6507_, 6);
lean_dec(v_unused_6813_);
v_unused_6814_ = lean_ctor_get(v_matcherApp_6507_, 5);
lean_dec(v_unused_6814_);
v_unused_6815_ = lean_ctor_get(v_matcherApp_6507_, 4);
lean_dec(v_unused_6815_);
v_unused_6816_ = lean_ctor_get(v_matcherApp_6507_, 3);
lean_dec(v_unused_6816_);
v_unused_6817_ = lean_ctor_get(v_matcherApp_6507_, 2);
lean_dec(v_unused_6817_);
v_unused_6818_ = lean_ctor_get(v_matcherApp_6507_, 1);
lean_dec(v_unused_6818_);
v_unused_6819_ = lean_ctor_get(v_matcherApp_6507_, 0);
lean_dec(v_unused_6819_);
v___x_6665_ = v_matcherApp_6507_;
v_isShared_6666_ = v_isSharedCheck_6811_;
goto v_resetjp_6664_;
}
else
{
lean_dec(v_matcherApp_6507_);
v___x_6665_ = lean_box(0);
v_isShared_6666_ = v_isSharedCheck_6811_;
goto v_resetjp_6664_;
}
v_resetjp_6664_:
{
lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v_aux1_6669_; lean_object* v_aux1_6670_; lean_object* v_aux1_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; lean_object* v___f_6677_; uint8_t v___x_6678_; lean_object* v___x_6679_; lean_object* v___x_6680_; lean_object* v___x_6681_; 
lean_inc_ref(v_matcherLevels_6636_);
v___x_6667_ = lean_array_to_list(v_matcherLevels_6636_);
lean_inc(v___x_6667_);
lean_inc(v_matcherName_6522_);
v___x_6668_ = l_Lean_mkConst(v_matcherName_6522_, v___x_6667_);
v_aux1_6669_ = l_Lean_mkAppN(v___x_6668_, v___y_6635_);
lean_inc_ref(v___y_6633_);
v_aux1_6670_ = l_Lean_Expr_app___override(v_aux1_6669_, v___y_6633_);
v_aux1_6671_ = l_Lean_mkAppN(v_aux1_6670_, v___y_6630_);
v___x_6672_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__3);
lean_inc_ref_n(v_aux1_6671_, 2);
v___x_6673_ = l_Lean_indentExpr(v_aux1_6671_);
v___x_6674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6674_, 0, v___x_6672_);
lean_ctor_set(v___x_6674_, 1, v___x_6673_);
v___x_6675_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5, &l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__55___closed__5);
v___x_6676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6676_, 0, v___x_6674_);
lean_ctor_set(v___x_6676_, 1, v___x_6675_);
v___f_6677_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6677_, 0, v___x_6676_);
v___x_6678_ = 0;
v___x_6679_ = lean_box(v___x_6678_);
v___x_6680_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6680_, 0, v_aux1_6671_);
lean_closure_set(v___x_6680_, 1, v___x_6679_);
v___x_6681_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6680_, v___f_6677_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
if (lean_obj_tag(v___x_6681_) == 0)
{
lean_object* v___x_6682_; lean_object* v___x_6683_; 
lean_dec_ref_known(v___x_6681_, 1);
v___x_6682_ = lean_array_get_size(v_alts_6527_);
v___x_6683_ = l_Lean_Meta_inferArgumentTypesN(v___x_6682_, v_aux1_6671_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
if (lean_obj_tag(v___x_6683_) == 0)
{
lean_object* v_a_6684_; lean_object* v___x_6685_; 
v_a_6684_ = lean_ctor_get(v___x_6683_, 0);
lean_inc(v_a_6684_);
lean_dec_ref_known(v___x_6683_, 1);
lean_inc(v___y_6640_);
lean_inc_ref(v___y_6639_);
lean_inc(v___y_6638_);
lean_inc_ref(v___y_6637_);
v___x_6685_ = lean_get_match_equations_for(v_matcherName_6522_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
if (lean_obj_tag(v___x_6685_) == 0)
{
lean_object* v_a_6686_; lean_object* v_splitterName_6687_; lean_object* v_splitterMatchInfo_6688_; lean_object* v___x_6689_; lean_object* v_aux2_6690_; lean_object* v_aux2_6691_; lean_object* v_aux2_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; lean_object* v___x_6695_; lean_object* v___x_6696_; lean_object* v___f_6697_; lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; 
v_a_6686_ = lean_ctor_get(v___x_6685_, 0);
lean_inc(v_a_6686_);
lean_dec_ref_known(v___x_6685_, 1);
v_splitterName_6687_ = lean_ctor_get(v_a_6686_, 1);
lean_inc_n(v_splitterName_6687_, 2);
v_splitterMatchInfo_6688_ = lean_ctor_get(v_a_6686_, 2);
lean_inc_ref(v_splitterMatchInfo_6688_);
lean_dec(v_a_6686_);
v___x_6689_ = l_Lean_mkConst(v_splitterName_6687_, v___x_6667_);
v_aux2_6690_ = l_Lean_mkAppN(v___x_6689_, v___y_6635_);
lean_inc_ref(v___y_6633_);
v_aux2_6691_ = l_Lean_Expr_app___override(v_aux2_6690_, v___y_6633_);
v_aux2_6692_ = l_Lean_mkAppN(v_aux2_6691_, v___y_6630_);
v___x_6693_ = lean_obj_once(&l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1, &l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1_once, _init_l_Lean_Meta_MatcherApp_transform___redArg___lam__53___closed__1);
lean_inc_ref_n(v_aux2_6692_, 2);
v___x_6694_ = l_Lean_indentExpr(v_aux2_6692_);
v___x_6695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6695_, 0, v___x_6693_);
lean_ctor_set(v___x_6695_, 1, v___x_6694_);
v___x_6696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6696_, 0, v___x_6695_);
lean_ctor_set(v___x_6696_, 1, v___x_6675_);
v___f_6697_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___redArg___lam__32), 2, 1);
lean_closure_set(v___f_6697_, 0, v___x_6696_);
v___x_6698_ = lean_box(v___x_6678_);
v___x_6699_ = lean_alloc_closure((void*)(l_Lean_Meta_check___boxed), 7, 2);
lean_closure_set(v___x_6699_, 0, v_aux2_6692_);
lean_closure_set(v___x_6699_, 1, v___x_6698_);
v___x_6700_ = l_Lean_Meta_mapErrorImp___redArg(v___x_6699_, v___f_6697_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
if (lean_obj_tag(v___x_6700_) == 0)
{
lean_object* v___x_6701_; 
lean_dec_ref_known(v___x_6700_, 1);
v___x_6701_ = l_Lean_Meta_inferArgumentTypesN(v___x_6682_, v_aux2_6692_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
if (lean_obj_tag(v___x_6701_) == 0)
{
lean_object* v_a_6702_; lean_object* v_numParams_6703_; lean_object* v_numDiscrs_6704_; lean_object* v_altInfos_6705_; lean_object* v_uElimPos_x3f_6706_; lean_object* v_overlaps_6707_; lean_object* v_altInfos_6708_; lean_object* v___x_6710_; uint8_t v_isShared_6711_; uint8_t v_isSharedCheck_6765_; 
v_a_6702_ = lean_ctor_get(v___x_6701_, 0);
lean_inc(v_a_6702_);
lean_dec_ref_known(v___x_6701_, 1);
v_numParams_6703_ = lean_ctor_get(v_toMatcherInfo_6521_, 0);
lean_inc(v_numParams_6703_);
v_numDiscrs_6704_ = lean_ctor_get(v_toMatcherInfo_6521_, 1);
lean_inc(v_numDiscrs_6704_);
v_altInfos_6705_ = lean_ctor_get(v_toMatcherInfo_6521_, 2);
lean_inc_ref(v_altInfos_6705_);
v_uElimPos_x3f_6706_ = lean_ctor_get(v_toMatcherInfo_6521_, 3);
lean_inc(v_uElimPos_x3f_6706_);
v_overlaps_6707_ = lean_ctor_get(v_toMatcherInfo_6521_, 5);
lean_inc_ref(v_overlaps_6707_);
lean_dec_ref(v_toMatcherInfo_6521_);
v_altInfos_6708_ = lean_ctor_get(v_splitterMatchInfo_6688_, 2);
v_isSharedCheck_6765_ = !lean_is_exclusive(v_splitterMatchInfo_6688_);
if (v_isSharedCheck_6765_ == 0)
{
lean_object* v_unused_6766_; lean_object* v_unused_6767_; lean_object* v_unused_6768_; lean_object* v_unused_6769_; lean_object* v_unused_6770_; 
v_unused_6766_ = lean_ctor_get(v_splitterMatchInfo_6688_, 5);
lean_dec(v_unused_6766_);
v_unused_6767_ = lean_ctor_get(v_splitterMatchInfo_6688_, 4);
lean_dec(v_unused_6767_);
v_unused_6768_ = lean_ctor_get(v_splitterMatchInfo_6688_, 3);
lean_dec(v_unused_6768_);
v_unused_6769_ = lean_ctor_get(v_splitterMatchInfo_6688_, 1);
lean_dec(v_unused_6769_);
v_unused_6770_ = lean_ctor_get(v_splitterMatchInfo_6688_, 0);
lean_dec(v_unused_6770_);
v___x_6710_ = v_splitterMatchInfo_6688_;
v_isShared_6711_ = v_isSharedCheck_6765_;
goto v_resetjp_6709_;
}
else
{
lean_inc(v_altInfos_6708_);
lean_dec(v_splitterMatchInfo_6688_);
v___x_6710_ = lean_box(0);
v_isShared_6711_ = v_isSharedCheck_6765_;
goto v_resetjp_6709_;
}
v_resetjp_6709_:
{
lean_object* v___x_6712_; lean_object* v___x_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; lean_object* v___x_6720_; lean_object* v___x_6722_; 
v___x_6712_ = lean_array_get_size(v_altInfos_6705_);
v___x_6713_ = lean_array_get_size(v_altInfos_6708_);
v___x_6714_ = lean_array_get_size(v_a_6684_);
v___x_6715_ = lean_array_get_size(v_a_6702_);
v___x_6716_ = l_Array_toSubarray___redArg(v_alts_6527_, v___x_6641_, v___x_6682_);
lean_inc_ref(v_altInfos_6705_);
v___x_6717_ = l_Array_toSubarray___redArg(v_altInfos_6705_, v___x_6641_, v___x_6712_);
v___x_6718_ = l_Array_toSubarray___redArg(v_altInfos_6708_, v___x_6641_, v___x_6713_);
v___x_6719_ = l_Array_toSubarray___redArg(v_a_6684_, v___x_6641_, v___x_6714_);
v___x_6720_ = l_Array_toSubarray___redArg(v_a_6702_, v___x_6641_, v___x_6715_);
if (v_isShared_6662_ == 0)
{
lean_ctor_set(v___x_6661_, 1, v___x_6720_);
lean_ctor_set(v___x_6661_, 0, v___x_6719_);
v___x_6722_ = v___x_6661_;
goto v_reusejp_6721_;
}
else
{
lean_object* v_reuseFailAlloc_6764_; 
v_reuseFailAlloc_6764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6764_, 0, v___x_6719_);
lean_ctor_set(v_reuseFailAlloc_6764_, 1, v___x_6720_);
v___x_6722_ = v_reuseFailAlloc_6764_;
goto v_reusejp_6721_;
}
v_reusejp_6721_:
{
lean_object* v___x_6724_; 
if (v_isShared_6658_ == 0)
{
lean_ctor_set(v___x_6657_, 1, v___x_6722_);
lean_ctor_set(v___x_6657_, 0, v___x_6718_);
v___x_6724_ = v___x_6657_;
goto v_reusejp_6723_;
}
else
{
lean_object* v_reuseFailAlloc_6763_; 
v_reuseFailAlloc_6763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6763_, 0, v___x_6718_);
lean_ctor_set(v_reuseFailAlloc_6763_, 1, v___x_6722_);
v___x_6724_ = v_reuseFailAlloc_6763_;
goto v_reusejp_6723_;
}
v_reusejp_6723_:
{
lean_object* v___x_6725_; lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6728_; 
v___x_6725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6725_, 0, v___x_6717_);
lean_ctor_set(v___x_6725_, 1, v___x_6724_);
v___x_6726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6726_, 0, v___x_6716_);
lean_ctor_set(v___x_6726_, 1, v___x_6725_);
v___x_6727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6727_, 0, v_remaining_x27_6642_);
lean_ctor_set(v___x_6727_, 1, v___x_6726_);
v___x_6728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v___x_6682_, v_onAlt_6512_, v_useSplitter_6508_, v_fst_6659_, v___y_6634_, v___x_6641_, v___x_6727_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_);
if (lean_obj_tag(v___x_6728_) == 0)
{
lean_object* v_a_6729_; lean_object* v_fst_6730_; lean_object* v___x_6731_; 
v_a_6729_ = lean_ctor_get(v___x_6728_, 0);
lean_inc(v_a_6729_);
lean_dec_ref_known(v___x_6728_, 1);
v_fst_6730_ = lean_ctor_get(v_a_6729_, 0);
lean_inc(v_fst_6730_);
lean_dec(v_a_6729_);
lean_inc(v___y_6640_);
lean_inc_ref(v___y_6639_);
lean_inc(v___y_6638_);
lean_inc_ref(v___y_6637_);
v___x_6731_ = lean_apply_6(v_onRemaining_6513_, v_remaining_6528_, v___y_6637_, v___y_6638_, v___y_6639_, v___y_6640_, lean_box(0));
if (lean_obj_tag(v___x_6731_) == 0)
{
lean_object* v_a_6732_; lean_object* v___x_6734_; uint8_t v_isShared_6735_; uint8_t v_isSharedCheck_6746_; 
v_a_6732_ = lean_ctor_get(v___x_6731_, 0);
v_isSharedCheck_6746_ = !lean_is_exclusive(v___x_6731_);
if (v_isSharedCheck_6746_ == 0)
{
v___x_6734_ = v___x_6731_;
v_isShared_6735_ = v_isSharedCheck_6746_;
goto v_resetjp_6733_;
}
else
{
lean_inc(v_a_6732_);
lean_dec(v___x_6731_);
v___x_6734_ = lean_box(0);
v_isShared_6735_ = v_isSharedCheck_6746_;
goto v_resetjp_6733_;
}
v_resetjp_6733_:
{
lean_object* v_remaining_x27_6736_; lean_object* v___x_6738_; 
v_remaining_x27_6736_ = l_Array_append___redArg(v_fst_6655_, v_a_6732_);
lean_dec(v_a_6732_);
if (v_isShared_6711_ == 0)
{
lean_ctor_set(v___x_6710_, 5, v_overlaps_6707_);
lean_ctor_set(v___x_6710_, 4, v___y_6631_);
lean_ctor_set(v___x_6710_, 3, v_uElimPos_x3f_6706_);
lean_ctor_set(v___x_6710_, 2, v_altInfos_6705_);
lean_ctor_set(v___x_6710_, 1, v_numDiscrs_6704_);
lean_ctor_set(v___x_6710_, 0, v_numParams_6703_);
v___x_6738_ = v___x_6710_;
goto v_reusejp_6737_;
}
else
{
lean_object* v_reuseFailAlloc_6745_; 
v_reuseFailAlloc_6745_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_6745_, 0, v_numParams_6703_);
lean_ctor_set(v_reuseFailAlloc_6745_, 1, v_numDiscrs_6704_);
lean_ctor_set(v_reuseFailAlloc_6745_, 2, v_altInfos_6705_);
lean_ctor_set(v_reuseFailAlloc_6745_, 3, v_uElimPos_x3f_6706_);
lean_ctor_set(v_reuseFailAlloc_6745_, 4, v___y_6631_);
lean_ctor_set(v_reuseFailAlloc_6745_, 5, v_overlaps_6707_);
v___x_6738_ = v_reuseFailAlloc_6745_;
goto v_reusejp_6737_;
}
v_reusejp_6737_:
{
lean_object* v___x_6740_; 
if (v_isShared_6666_ == 0)
{
lean_ctor_set(v___x_6665_, 7, v_remaining_x27_6736_);
lean_ctor_set(v___x_6665_, 6, v_fst_6730_);
lean_ctor_set(v___x_6665_, 5, v___y_6630_);
lean_ctor_set(v___x_6665_, 4, v___y_6633_);
lean_ctor_set(v___x_6665_, 3, v___y_6635_);
lean_ctor_set(v___x_6665_, 2, v_matcherLevels_6636_);
lean_ctor_set(v___x_6665_, 1, v_splitterName_6687_);
lean_ctor_set(v___x_6665_, 0, v___x_6738_);
v___x_6740_ = v___x_6665_;
goto v_reusejp_6739_;
}
else
{
lean_object* v_reuseFailAlloc_6744_; 
v_reuseFailAlloc_6744_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_6744_, 0, v___x_6738_);
lean_ctor_set(v_reuseFailAlloc_6744_, 1, v_splitterName_6687_);
lean_ctor_set(v_reuseFailAlloc_6744_, 2, v_matcherLevels_6636_);
lean_ctor_set(v_reuseFailAlloc_6744_, 3, v___y_6635_);
lean_ctor_set(v_reuseFailAlloc_6744_, 4, v___y_6633_);
lean_ctor_set(v_reuseFailAlloc_6744_, 5, v___y_6630_);
lean_ctor_set(v_reuseFailAlloc_6744_, 6, v_fst_6730_);
lean_ctor_set(v_reuseFailAlloc_6744_, 7, v_remaining_x27_6736_);
v___x_6740_ = v_reuseFailAlloc_6744_;
goto v_reusejp_6739_;
}
v_reusejp_6739_:
{
lean_object* v___x_6742_; 
if (v_isShared_6735_ == 0)
{
lean_ctor_set(v___x_6734_, 0, v___x_6740_);
v___x_6742_ = v___x_6734_;
goto v_reusejp_6741_;
}
else
{
lean_object* v_reuseFailAlloc_6743_; 
v_reuseFailAlloc_6743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6743_, 0, v___x_6740_);
v___x_6742_ = v_reuseFailAlloc_6743_;
goto v_reusejp_6741_;
}
v_reusejp_6741_:
{
return v___x_6742_;
}
}
}
}
}
else
{
lean_object* v_a_6747_; lean_object* v___x_6749_; uint8_t v_isShared_6750_; uint8_t v_isSharedCheck_6754_; 
lean_dec(v_fst_6730_);
lean_del_object(v___x_6710_);
lean_dec_ref(v_overlaps_6707_);
lean_dec(v_uElimPos_x3f_6706_);
lean_dec_ref(v_altInfos_6705_);
lean_dec(v_numDiscrs_6704_);
lean_dec(v_numParams_6703_);
lean_dec(v_splitterName_6687_);
lean_del_object(v___x_6665_);
lean_dec(v_fst_6655_);
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
v_a_6747_ = lean_ctor_get(v___x_6731_, 0);
v_isSharedCheck_6754_ = !lean_is_exclusive(v___x_6731_);
if (v_isSharedCheck_6754_ == 0)
{
v___x_6749_ = v___x_6731_;
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
else
{
lean_inc(v_a_6747_);
lean_dec(v___x_6731_);
v___x_6749_ = lean_box(0);
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
v_resetjp_6748_:
{
lean_object* v___x_6752_; 
if (v_isShared_6750_ == 0)
{
v___x_6752_ = v___x_6749_;
goto v_reusejp_6751_;
}
else
{
lean_object* v_reuseFailAlloc_6753_; 
v_reuseFailAlloc_6753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_a_6747_);
v___x_6752_ = v_reuseFailAlloc_6753_;
goto v_reusejp_6751_;
}
v_reusejp_6751_:
{
return v___x_6752_;
}
}
}
}
else
{
lean_object* v_a_6755_; lean_object* v___x_6757_; uint8_t v_isShared_6758_; uint8_t v_isSharedCheck_6762_; 
lean_del_object(v___x_6710_);
lean_dec_ref(v_overlaps_6707_);
lean_dec(v_uElimPos_x3f_6706_);
lean_dec_ref(v_altInfos_6705_);
lean_dec(v_numDiscrs_6704_);
lean_dec(v_numParams_6703_);
lean_dec(v_splitterName_6687_);
lean_del_object(v___x_6665_);
lean_dec(v_fst_6655_);
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_onRemaining_6513_);
v_a_6755_ = lean_ctor_get(v___x_6728_, 0);
v_isSharedCheck_6762_ = !lean_is_exclusive(v___x_6728_);
if (v_isSharedCheck_6762_ == 0)
{
v___x_6757_ = v___x_6728_;
v_isShared_6758_ = v_isSharedCheck_6762_;
goto v_resetjp_6756_;
}
else
{
lean_inc(v_a_6755_);
lean_dec(v___x_6728_);
v___x_6757_ = lean_box(0);
v_isShared_6758_ = v_isSharedCheck_6762_;
goto v_resetjp_6756_;
}
v_resetjp_6756_:
{
lean_object* v___x_6760_; 
if (v_isShared_6758_ == 0)
{
v___x_6760_ = v___x_6757_;
goto v_reusejp_6759_;
}
else
{
lean_object* v_reuseFailAlloc_6761_; 
v_reuseFailAlloc_6761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6761_, 0, v_a_6755_);
v___x_6760_ = v_reuseFailAlloc_6761_;
goto v_reusejp_6759_;
}
v_reusejp_6759_:
{
return v___x_6760_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_6771_; lean_object* v___x_6773_; uint8_t v_isShared_6774_; uint8_t v_isSharedCheck_6778_; 
lean_dec_ref(v_splitterMatchInfo_6688_);
lean_dec(v_splitterName_6687_);
lean_dec(v_a_6684_);
lean_del_object(v___x_6665_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
v_a_6771_ = lean_ctor_get(v___x_6701_, 0);
v_isSharedCheck_6778_ = !lean_is_exclusive(v___x_6701_);
if (v_isSharedCheck_6778_ == 0)
{
v___x_6773_ = v___x_6701_;
v_isShared_6774_ = v_isSharedCheck_6778_;
goto v_resetjp_6772_;
}
else
{
lean_inc(v_a_6771_);
lean_dec(v___x_6701_);
v___x_6773_ = lean_box(0);
v_isShared_6774_ = v_isSharedCheck_6778_;
goto v_resetjp_6772_;
}
v_resetjp_6772_:
{
lean_object* v___x_6776_; 
if (v_isShared_6774_ == 0)
{
v___x_6776_ = v___x_6773_;
goto v_reusejp_6775_;
}
else
{
lean_object* v_reuseFailAlloc_6777_; 
v_reuseFailAlloc_6777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6777_, 0, v_a_6771_);
v___x_6776_ = v_reuseFailAlloc_6777_;
goto v_reusejp_6775_;
}
v_reusejp_6775_:
{
return v___x_6776_;
}
}
}
}
else
{
lean_object* v_a_6779_; lean_object* v___x_6781_; uint8_t v_isShared_6782_; uint8_t v_isSharedCheck_6786_; 
lean_dec_ref(v_aux2_6692_);
lean_dec_ref(v_splitterMatchInfo_6688_);
lean_dec(v_splitterName_6687_);
lean_dec(v_a_6684_);
lean_del_object(v___x_6665_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
v_a_6779_ = lean_ctor_get(v___x_6700_, 0);
v_isSharedCheck_6786_ = !lean_is_exclusive(v___x_6700_);
if (v_isSharedCheck_6786_ == 0)
{
v___x_6781_ = v___x_6700_;
v_isShared_6782_ = v_isSharedCheck_6786_;
goto v_resetjp_6780_;
}
else
{
lean_inc(v_a_6779_);
lean_dec(v___x_6700_);
v___x_6781_ = lean_box(0);
v_isShared_6782_ = v_isSharedCheck_6786_;
goto v_resetjp_6780_;
}
v_resetjp_6780_:
{
lean_object* v___x_6784_; 
if (v_isShared_6782_ == 0)
{
v___x_6784_ = v___x_6781_;
goto v_reusejp_6783_;
}
else
{
lean_object* v_reuseFailAlloc_6785_; 
v_reuseFailAlloc_6785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6785_, 0, v_a_6779_);
v___x_6784_ = v_reuseFailAlloc_6785_;
goto v_reusejp_6783_;
}
v_reusejp_6783_:
{
return v___x_6784_;
}
}
}
}
else
{
lean_object* v_a_6787_; lean_object* v___x_6789_; uint8_t v_isShared_6790_; uint8_t v_isSharedCheck_6794_; 
lean_dec(v_a_6684_);
lean_dec(v___x_6667_);
lean_del_object(v___x_6665_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
v_a_6787_ = lean_ctor_get(v___x_6685_, 0);
v_isSharedCheck_6794_ = !lean_is_exclusive(v___x_6685_);
if (v_isSharedCheck_6794_ == 0)
{
v___x_6789_ = v___x_6685_;
v_isShared_6790_ = v_isSharedCheck_6794_;
goto v_resetjp_6788_;
}
else
{
lean_inc(v_a_6787_);
lean_dec(v___x_6685_);
v___x_6789_ = lean_box(0);
v_isShared_6790_ = v_isSharedCheck_6794_;
goto v_resetjp_6788_;
}
v_resetjp_6788_:
{
lean_object* v___x_6792_; 
if (v_isShared_6790_ == 0)
{
v___x_6792_ = v___x_6789_;
goto v_reusejp_6791_;
}
else
{
lean_object* v_reuseFailAlloc_6793_; 
v_reuseFailAlloc_6793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6793_, 0, v_a_6787_);
v___x_6792_ = v_reuseFailAlloc_6793_;
goto v_reusejp_6791_;
}
v_reusejp_6791_:
{
return v___x_6792_;
}
}
}
}
else
{
lean_object* v_a_6795_; lean_object* v___x_6797_; uint8_t v_isShared_6798_; uint8_t v_isSharedCheck_6802_; 
lean_dec(v___x_6667_);
lean_del_object(v___x_6665_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
v_a_6795_ = lean_ctor_get(v___x_6683_, 0);
v_isSharedCheck_6802_ = !lean_is_exclusive(v___x_6683_);
if (v_isSharedCheck_6802_ == 0)
{
v___x_6797_ = v___x_6683_;
v_isShared_6798_ = v_isSharedCheck_6802_;
goto v_resetjp_6796_;
}
else
{
lean_inc(v_a_6795_);
lean_dec(v___x_6683_);
v___x_6797_ = lean_box(0);
v_isShared_6798_ = v_isSharedCheck_6802_;
goto v_resetjp_6796_;
}
v_resetjp_6796_:
{
lean_object* v___x_6800_; 
if (v_isShared_6798_ == 0)
{
v___x_6800_ = v___x_6797_;
goto v_reusejp_6799_;
}
else
{
lean_object* v_reuseFailAlloc_6801_; 
v_reuseFailAlloc_6801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6801_, 0, v_a_6795_);
v___x_6800_ = v_reuseFailAlloc_6801_;
goto v_reusejp_6799_;
}
v_reusejp_6799_:
{
return v___x_6800_;
}
}
}
}
else
{
lean_object* v_a_6803_; lean_object* v___x_6805_; uint8_t v_isShared_6806_; uint8_t v_isSharedCheck_6810_; 
lean_dec_ref(v_aux1_6671_);
lean_dec(v___x_6667_);
lean_del_object(v___x_6665_);
lean_del_object(v___x_6661_);
lean_dec(v_fst_6659_);
lean_del_object(v___x_6657_);
lean_dec(v_fst_6655_);
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
v_a_6803_ = lean_ctor_get(v___x_6681_, 0);
v_isSharedCheck_6810_ = !lean_is_exclusive(v___x_6681_);
if (v_isSharedCheck_6810_ == 0)
{
v___x_6805_ = v___x_6681_;
v_isShared_6806_ = v_isSharedCheck_6810_;
goto v_resetjp_6804_;
}
else
{
lean_inc(v_a_6803_);
lean_dec(v___x_6681_);
v___x_6805_ = lean_box(0);
v_isShared_6806_ = v_isSharedCheck_6810_;
goto v_resetjp_6804_;
}
v_resetjp_6804_:
{
lean_object* v___x_6808_; 
if (v_isShared_6806_ == 0)
{
v___x_6808_ = v___x_6805_;
goto v_reusejp_6807_;
}
else
{
lean_object* v_reuseFailAlloc_6809_; 
v_reuseFailAlloc_6809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6809_, 0, v_a_6803_);
v___x_6808_ = v_reuseFailAlloc_6809_;
goto v_reusejp_6807_;
}
v_reusejp_6807_:
{
return v___x_6808_;
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
lean_object* v_a_6824_; lean_object* v___x_6826_; uint8_t v_isShared_6827_; uint8_t v_isSharedCheck_6831_; 
lean_dec_ref(v_matcherLevels_6636_);
lean_dec_ref(v___y_6635_);
lean_dec(v___y_6634_);
lean_dec_ref(v___y_6633_);
lean_dec_ref(v___y_6631_);
lean_dec_ref(v___y_6630_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
lean_dec_ref(v_matcherApp_6507_);
v_a_6824_ = lean_ctor_get(v___x_6650_, 0);
v_isSharedCheck_6831_ = !lean_is_exclusive(v___x_6650_);
if (v_isSharedCheck_6831_ == 0)
{
v___x_6826_ = v___x_6650_;
v_isShared_6827_ = v_isSharedCheck_6831_;
goto v_resetjp_6825_;
}
else
{
lean_inc(v_a_6824_);
lean_dec(v___x_6650_);
v___x_6826_ = lean_box(0);
v_isShared_6827_ = v_isSharedCheck_6831_;
goto v_resetjp_6825_;
}
v_resetjp_6825_:
{
lean_object* v___x_6829_; 
if (v_isShared_6827_ == 0)
{
v___x_6829_ = v___x_6826_;
goto v_reusejp_6828_;
}
else
{
lean_object* v_reuseFailAlloc_6830_; 
v_reuseFailAlloc_6830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6830_, 0, v_a_6824_);
v___x_6829_ = v_reuseFailAlloc_6830_;
goto v_reusejp_6828_;
}
v_reusejp_6828_:
{
return v___x_6829_;
}
}
}
}
v___jp_6832_:
{
size_t v_sz_6838_; size_t v___x_6839_; lean_object* v___x_6840_; 
v_sz_6838_ = lean_array_size(v_params_6524_);
v___x_6839_ = ((size_t)0ULL);
lean_inc_ref(v_params_6524_);
lean_inc_ref(v_onParams_6510_);
v___x_6840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6510_, v_sz_6838_, v___x_6839_, v_params_6524_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_);
if (lean_obj_tag(v___x_6840_) == 0)
{
lean_object* v_a_6841_; size_t v_sz_6842_; lean_object* v___x_6843_; 
v_a_6841_ = lean_ctor_get(v___x_6840_, 0);
lean_inc(v_a_6841_);
lean_dec_ref_known(v___x_6840_, 1);
v_sz_6842_ = lean_array_size(v_discrs_6526_);
lean_inc_ref(v_discrs_6526_);
v___x_6843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__6(v_onParams_6510_, v_sz_6842_, v___x_6839_, v_discrs_6526_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_);
if (lean_obj_tag(v___x_6843_) == 0)
{
lean_object* v_a_6844_; lean_object* v___x_6845_; lean_object* v___x_6846_; lean_object* v___f_6847_; uint8_t v___x_6848_; lean_object* v___x_6849_; 
v_a_6844_ = lean_ctor_get(v___x_6843_, 0);
lean_inc_n(v_a_6844_, 2);
lean_dec_ref_known(v___x_6843_, 1);
v___x_6845_ = lean_box(v_addEqualities_6509_);
v___x_6846_ = ((lean_object*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed__const__1));
lean_inc_ref(v_discrs_6526_);
lean_inc_ref(v_toMatcherInfo_6521_);
v___f_6847_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___lam__3___boxed), 13, 6);
lean_closure_set(v___f_6847_, 0, v_onMotive_6511_);
lean_closure_set(v___f_6847_, 1, v_toMatcherInfo_6521_);
lean_closure_set(v___f_6847_, 2, v_a_6844_);
lean_closure_set(v___f_6847_, 3, v___x_6845_);
lean_closure_set(v___f_6847_, 4, v___x_6846_);
lean_closure_set(v___f_6847_, 5, v_discrs_6526_);
v___x_6848_ = 0;
lean_inc_ref(v_motive_6525_);
v___x_6849_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Meta_MatcherApp_addArg_spec__1___redArg(v_motive_6525_, v___f_6847_, v___x_6848_, v___y_6834_, v___y_6835_, v___y_6836_, v___y_6837_);
if (lean_obj_tag(v___x_6849_) == 0)
{
lean_object* v_a_6850_; lean_object* v_snd_6851_; lean_object* v_snd_6852_; lean_object* v_uElimPos_x3f_6853_; 
v_a_6850_ = lean_ctor_get(v___x_6849_, 0);
lean_inc(v_a_6850_);
lean_dec_ref_known(v___x_6849_, 1);
v_snd_6851_ = lean_ctor_get(v_a_6850_, 1);
v_snd_6852_ = lean_ctor_get(v_snd_6851_, 1);
lean_inc(v_snd_6852_);
v_uElimPos_x3f_6853_ = lean_ctor_get(v_toMatcherInfo_6521_, 3);
if (lean_obj_tag(v_uElimPos_x3f_6853_) == 0)
{
lean_object* v_fst_6854_; lean_object* v_fst_6855_; lean_object* v_snd_6856_; 
v_fst_6854_ = lean_ctor_get(v_a_6850_, 0);
lean_inc(v_fst_6854_);
lean_dec(v_a_6850_);
v_fst_6855_ = lean_ctor_get(v_snd_6852_, 0);
lean_inc(v_fst_6855_);
v_snd_6856_ = lean_ctor_get(v_snd_6852_, 1);
lean_inc(v_snd_6856_);
lean_dec(v_snd_6852_);
lean_inc_ref(v_matcherLevels_6523_);
v___y_6629_ = v_fst_6855_;
v___y_6630_ = v_a_6844_;
v___y_6631_ = v_snd_6856_;
v___y_6632_ = v___x_6839_;
v___y_6633_ = v_fst_6854_;
v___y_6634_ = v_numDiscrEqs_6833_;
v___y_6635_ = v_a_6841_;
v_matcherLevels_6636_ = v_matcherLevels_6523_;
v___y_6637_ = v___y_6834_;
v___y_6638_ = v___y_6835_;
v___y_6639_ = v___y_6836_;
v___y_6640_ = v___y_6837_;
goto v___jp_6628_;
}
else
{
lean_object* v_fst_6857_; lean_object* v_fst_6858_; lean_object* v_fst_6859_; lean_object* v_snd_6860_; lean_object* v_val_6861_; lean_object* v___x_6862_; 
lean_inc(v_snd_6851_);
v_fst_6857_ = lean_ctor_get(v_a_6850_, 0);
lean_inc(v_fst_6857_);
lean_dec(v_a_6850_);
v_fst_6858_ = lean_ctor_get(v_snd_6851_, 0);
lean_inc(v_fst_6858_);
lean_dec(v_snd_6851_);
v_fst_6859_ = lean_ctor_get(v_snd_6852_, 0);
lean_inc(v_fst_6859_);
v_snd_6860_ = lean_ctor_get(v_snd_6852_, 1);
lean_inc(v_snd_6860_);
lean_dec(v_snd_6852_);
v_val_6861_ = lean_ctor_get(v_uElimPos_x3f_6853_, 0);
lean_inc_ref(v_matcherLevels_6523_);
v___x_6862_ = lean_array_set(v_matcherLevels_6523_, v_val_6861_, v_fst_6858_);
v___y_6629_ = v_fst_6859_;
v___y_6630_ = v_a_6844_;
v___y_6631_ = v_snd_6860_;
v___y_6632_ = v___x_6839_;
v___y_6633_ = v_fst_6857_;
v___y_6634_ = v_numDiscrEqs_6833_;
v___y_6635_ = v_a_6841_;
v_matcherLevels_6636_ = v___x_6862_;
v___y_6637_ = v___y_6834_;
v___y_6638_ = v___y_6835_;
v___y_6639_ = v___y_6836_;
v___y_6640_ = v___y_6837_;
goto v___jp_6628_;
}
}
else
{
lean_object* v_a_6863_; lean_object* v___x_6865_; uint8_t v_isShared_6866_; uint8_t v_isSharedCheck_6870_; 
lean_dec(v_a_6844_);
lean_dec(v_a_6841_);
lean_dec(v_numDiscrEqs_6833_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
lean_dec_ref(v_matcherApp_6507_);
v_a_6863_ = lean_ctor_get(v___x_6849_, 0);
v_isSharedCheck_6870_ = !lean_is_exclusive(v___x_6849_);
if (v_isSharedCheck_6870_ == 0)
{
v___x_6865_ = v___x_6849_;
v_isShared_6866_ = v_isSharedCheck_6870_;
goto v_resetjp_6864_;
}
else
{
lean_inc(v_a_6863_);
lean_dec(v___x_6849_);
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
lean_dec(v_a_6841_);
lean_dec(v_numDiscrEqs_6833_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
lean_dec_ref(v_onMotive_6511_);
lean_dec_ref(v_matcherApp_6507_);
v_a_6871_ = lean_ctor_get(v___x_6843_, 0);
v_isSharedCheck_6878_ = !lean_is_exclusive(v___x_6843_);
if (v_isSharedCheck_6878_ == 0)
{
v___x_6873_ = v___x_6843_;
v_isShared_6874_ = v_isSharedCheck_6878_;
goto v_resetjp_6872_;
}
else
{
lean_inc(v_a_6871_);
lean_dec(v___x_6843_);
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
else
{
lean_object* v_a_6879_; lean_object* v___x_6881_; uint8_t v_isShared_6882_; uint8_t v_isSharedCheck_6886_; 
lean_dec(v_numDiscrEqs_6833_);
lean_dec_ref(v_remaining_6528_);
lean_dec_ref(v_alts_6527_);
lean_dec(v_matcherName_6522_);
lean_dec_ref(v_toMatcherInfo_6521_);
lean_dec_ref(v_onRemaining_6513_);
lean_dec_ref(v_onAlt_6512_);
lean_dec_ref(v_onMotive_6511_);
lean_dec_ref(v_onParams_6510_);
lean_dec_ref(v_matcherApp_6507_);
v_a_6879_ = lean_ctor_get(v___x_6840_, 0);
v_isSharedCheck_6886_ = !lean_is_exclusive(v___x_6840_);
if (v_isSharedCheck_6886_ == 0)
{
v___x_6881_ = v___x_6840_;
v_isShared_6882_ = v_isSharedCheck_6886_;
goto v_resetjp_6880_;
}
else
{
lean_inc(v_a_6879_);
lean_dec(v___x_6840_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4___boxed(lean_object* v_matcherApp_6906_, lean_object* v_useSplitter_6907_, lean_object* v_addEqualities_6908_, lean_object* v_onParams_6909_, lean_object* v_onMotive_6910_, lean_object* v_onAlt_6911_, lean_object* v_onRemaining_6912_, lean_object* v___y_6913_, lean_object* v___y_6914_, lean_object* v___y_6915_, lean_object* v___y_6916_, lean_object* v___y_6917_){
_start:
{
uint8_t v_useSplitter_boxed_6918_; uint8_t v_addEqualities_boxed_6919_; lean_object* v_res_6920_; 
v_useSplitter_boxed_6918_ = lean_unbox(v_useSplitter_6907_);
v_addEqualities_boxed_6919_ = lean_unbox(v_addEqualities_6908_);
v_res_6920_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6906_, v_useSplitter_boxed_6918_, v_addEqualities_boxed_6919_, v_onParams_6909_, v_onMotive_6910_, v_onAlt_6911_, v_onRemaining_6912_, v___y_6913_, v___y_6914_, v___y_6915_, v___y_6916_);
lean_dec(v___y_6916_);
lean_dec_ref(v___y_6915_);
lean_dec(v___y_6914_);
lean_dec_ref(v___y_6913_);
return v_res_6920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType(lean_object* v_matcherApp_6926_, lean_object* v_a_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_, lean_object* v_a_6930_){
_start:
{
lean_object* v_toMatcherInfo_6932_; lean_object* v_matcherName_6933_; lean_object* v_matcherLevels_6934_; lean_object* v_params_6935_; lean_object* v_alts_6936_; lean_object* v_remaining_6937_; lean_object* v___f_6938_; lean_object* v___f_6939_; lean_object* v_nExtra_6940_; uint8_t v___x_6941_; lean_object* v___f_6942_; uint8_t v___x_6943_; lean_object* v___x_6944_; lean_object* v___x_6945_; lean_object* v___f_6946_; lean_object* v___x_6947_; 
v_toMatcherInfo_6932_ = lean_ctor_get(v_matcherApp_6926_, 0);
v_matcherName_6933_ = lean_ctor_get(v_matcherApp_6926_, 1);
v_matcherLevels_6934_ = lean_ctor_get(v_matcherApp_6926_, 2);
v_params_6935_ = lean_ctor_get(v_matcherApp_6926_, 3);
v_alts_6936_ = lean_ctor_get(v_matcherApp_6926_, 6);
v_remaining_6937_ = lean_ctor_get(v_matcherApp_6926_, 7);
v___f_6938_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__0));
v___f_6939_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__1));
v_nExtra_6940_ = lean_array_get_size(v_remaining_6937_);
v___x_6941_ = 1;
v___f_6942_ = ((lean_object*)(l_Lean_Meta_MatcherApp_inferMatchType___closed__2));
v___x_6943_ = 0;
v___x_6944_ = lean_box(v___x_6943_);
v___x_6945_ = lean_box(v___x_6941_);
lean_inc_ref(v_matcherLevels_6934_);
lean_inc_ref(v_params_6935_);
lean_inc(v_matcherName_6933_);
lean_inc_ref(v_toMatcherInfo_6932_);
lean_inc_ref(v_alts_6936_);
v___f_6946_ = lean_alloc_closure((void*)(l_Lean_Meta_MatcherApp_inferMatchType___lam__3___boxed), 15, 8);
lean_closure_set(v___f_6946_, 0, v_nExtra_6940_);
lean_closure_set(v___f_6946_, 1, v___x_6944_);
lean_closure_set(v___f_6946_, 2, v___x_6945_);
lean_closure_set(v___f_6946_, 3, v_alts_6936_);
lean_closure_set(v___f_6946_, 4, v_toMatcherInfo_6932_);
lean_closure_set(v___f_6946_, 5, v_matcherName_6933_);
lean_closure_set(v___f_6946_, 6, v_params_6935_);
lean_closure_set(v___f_6946_, 7, v_matcherLevels_6934_);
v___x_6947_ = l_Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4(v_matcherApp_6926_, v___x_6941_, v___x_6943_, v___f_6938_, v___f_6946_, v___f_6942_, v___f_6939_, v_a_6927_, v_a_6928_, v_a_6929_, v_a_6930_);
return v___x_6947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_inferMatchType___boxed(lean_object* v_matcherApp_6948_, lean_object* v_a_6949_, lean_object* v_a_6950_, lean_object* v_a_6951_, lean_object* v_a_6952_, lean_object* v_a_6953_){
_start:
{
lean_object* v_res_6954_; 
v_res_6954_ = l_Lean_Meta_MatcherApp_inferMatchType(v_matcherApp_6948_, v_a_6949_, v_a_6950_, v_a_6951_, v_a_6952_);
lean_dec(v_a_6952_);
lean_dec_ref(v_a_6951_);
lean_dec(v_a_6950_);
lean_dec_ref(v_a_6949_);
return v_res_6954_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(lean_object* v_a_6955_, lean_object* v_termAlt_6956_, lean_object* v_inst_6957_, lean_object* v_R_6958_, lean_object* v_a_6959_, lean_object* v_b_6960_, lean_object* v_c_6961_, lean_object* v___y_6962_, lean_object* v___y_6963_, lean_object* v___y_6964_, lean_object* v___y_6965_){
_start:
{
lean_object* v___x_6967_; 
v___x_6967_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___redArg(v_a_6955_, v_termAlt_6956_, v_a_6959_, v_b_6960_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_);
return v___x_6967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2___boxed(lean_object* v_a_6968_, lean_object* v_termAlt_6969_, lean_object* v_inst_6970_, lean_object* v_R_6971_, lean_object* v_a_6972_, lean_object* v_b_6973_, lean_object* v_c_6974_, lean_object* v___y_6975_, lean_object* v___y_6976_, lean_object* v___y_6977_, lean_object* v___y_6978_, lean_object* v___y_6979_){
_start:
{
lean_object* v_res_6980_; 
v_res_6980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_inferMatchType_spec__2(v_a_6968_, v_termAlt_6969_, v_inst_6970_, v_R_6971_, v_a_6972_, v_b_6973_, v_c_6974_, v___y_6975_, v___y_6976_, v___y_6977_, v___y_6978_);
lean_dec(v___y_6978_);
lean_dec_ref(v___y_6977_);
lean_dec(v___y_6976_);
lean_dec_ref(v___y_6975_);
return v_res_6980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(lean_object* v_00_u03b1_6981_, lean_object* v_fvars_6982_, lean_object* v_names_6983_, lean_object* v_k_6984_, lean_object* v___y_6985_, lean_object* v___y_6986_, lean_object* v___y_6987_, lean_object* v___y_6988_){
_start:
{
lean_object* v___x_6990_; 
v___x_6990_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___redArg(v_fvars_6982_, v_names_6983_, v_k_6984_, v___y_6985_, v___y_6986_, v___y_6987_, v___y_6988_);
return v___x_6990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9___boxed(lean_object* v_00_u03b1_6991_, lean_object* v_fvars_6992_, lean_object* v_names_6993_, lean_object* v_k_6994_, lean_object* v___y_6995_, lean_object* v___y_6996_, lean_object* v___y_6997_, lean_object* v___y_6998_, lean_object* v___y_6999_){
_start:
{
lean_object* v_res_7000_; 
v_res_7000_ = l_Lean_Meta_MatcherApp_withUserNames___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__9(v_00_u03b1_6991_, v_fvars_6992_, v_names_6993_, v_k_6994_, v___y_6995_, v___y_6996_, v___y_6997_, v___y_6998_);
lean_dec(v___y_6998_);
lean_dec_ref(v___y_6997_);
lean_dec(v___y_6996_);
lean_dec_ref(v___y_6995_);
lean_dec_ref(v_names_6993_);
lean_dec_ref(v_fvars_6992_);
return v_res_7000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(lean_object* v_00_u03b1_7001_, lean_object* v_origAltType_7002_, lean_object* v_altInfo_7003_, lean_object* v_k_7004_, lean_object* v___y_7005_, lean_object* v___y_7006_, lean_object* v___y_7007_, lean_object* v___y_7008_){
_start:
{
lean_object* v___x_7010_; 
v___x_7010_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___redArg(v_origAltType_7002_, v_altInfo_7003_, v_k_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_);
return v___x_7010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13___boxed(lean_object* v_00_u03b1_7011_, lean_object* v_origAltType_7012_, lean_object* v_altInfo_7013_, lean_object* v_k_7014_, lean_object* v___y_7015_, lean_object* v___y_7016_, lean_object* v___y_7017_, lean_object* v___y_7018_, lean_object* v___y_7019_){
_start:
{
lean_object* v_res_7020_; 
v_res_7020_ = l___private_Lean_Meta_Match_MatcherApp_Transform_0__Lean_Meta_MatcherApp_forallAltTelescope_x27___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__13(v_00_u03b1_7011_, v_origAltType_7012_, v_altInfo_7013_, v_k_7014_, v___y_7015_, v___y_7016_, v___y_7017_, v___y_7018_);
lean_dec(v___y_7018_);
lean_dec_ref(v___y_7017_);
lean_dec(v___y_7016_);
lean_dec_ref(v___y_7015_);
return v_res_7020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(lean_object* v_declName_7021_, lean_object* v___y_7022_, lean_object* v___y_7023_, lean_object* v___y_7024_, lean_object* v___y_7025_){
_start:
{
lean_object* v___x_7027_; 
v___x_7027_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___redArg(v_declName_7021_, v___y_7025_);
return v___x_7027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15___boxed(lean_object* v_declName_7028_, lean_object* v___y_7029_, lean_object* v___y_7030_, lean_object* v___y_7031_, lean_object* v___y_7032_, lean_object* v___y_7033_){
_start:
{
lean_object* v_res_7034_; 
v_res_7034_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__15(v_declName_7028_, v___y_7029_, v___y_7030_, v___y_7031_, v___y_7032_);
lean_dec(v___y_7032_);
lean_dec_ref(v___y_7031_);
lean_dec(v___y_7030_);
lean_dec_ref(v___y_7029_);
return v_res_7034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(size_t v_sz_7035_, size_t v_i_7036_, lean_object* v_bs_7037_, lean_object* v___y_7038_, lean_object* v___y_7039_, lean_object* v___y_7040_, lean_object* v___y_7041_){
_start:
{
lean_object* v___x_7043_; 
v___x_7043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___redArg(v_sz_7035_, v_i_7036_, v_bs_7037_, v___y_7038_, v___y_7040_, v___y_7041_);
return v___x_7043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5___boxed(lean_object* v_sz_7044_, lean_object* v_i_7045_, lean_object* v_bs_7046_, lean_object* v___y_7047_, lean_object* v___y_7048_, lean_object* v___y_7049_, lean_object* v___y_7050_, lean_object* v___y_7051_){
_start:
{
size_t v_sz_boxed_7052_; size_t v_i_boxed_7053_; lean_object* v_res_7054_; 
v_sz_boxed_7052_ = lean_unbox_usize(v_sz_7044_);
lean_dec(v_sz_7044_);
v_i_boxed_7053_ = lean_unbox_usize(v_i_7045_);
lean_dec(v_i_7045_);
v_res_7054_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__5(v_sz_boxed_7052_, v_i_boxed_7053_, v_bs_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_);
lean_dec(v___y_7050_);
lean_dec_ref(v___y_7049_);
lean_dec(v___y_7048_);
lean_dec_ref(v___y_7047_);
return v_res_7054_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(lean_object* v_upperBound_7055_, lean_object* v_onAlt_7056_, lean_object* v_extraEqualities_7057_, lean_object* v_inst_7058_, lean_object* v_R_7059_, lean_object* v_a_7060_, lean_object* v_b_7061_, lean_object* v_c_7062_, lean_object* v___y_7063_, lean_object* v___y_7064_, lean_object* v___y_7065_, lean_object* v___y_7066_){
_start:
{
lean_object* v___x_7068_; 
v___x_7068_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___redArg(v_upperBound_7055_, v_onAlt_7056_, v_extraEqualities_7057_, v_a_7060_, v_b_7061_, v___y_7063_, v___y_7064_, v___y_7065_, v___y_7066_);
return v___x_7068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10___boxed(lean_object* v_upperBound_7069_, lean_object* v_onAlt_7070_, lean_object* v_extraEqualities_7071_, lean_object* v_inst_7072_, lean_object* v_R_7073_, lean_object* v_a_7074_, lean_object* v_b_7075_, lean_object* v_c_7076_, lean_object* v___y_7077_, lean_object* v___y_7078_, lean_object* v___y_7079_, lean_object* v___y_7080_, lean_object* v___y_7081_){
_start:
{
lean_object* v_res_7082_; 
v_res_7082_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__10(v_upperBound_7069_, v_onAlt_7070_, v_extraEqualities_7071_, v_inst_7072_, v_R_7073_, v_a_7074_, v_b_7075_, v_c_7076_, v___y_7077_, v___y_7078_, v___y_7079_, v___y_7080_);
lean_dec(v___y_7080_);
lean_dec_ref(v___y_7079_);
lean_dec(v___y_7078_);
lean_dec_ref(v___y_7077_);
lean_dec(v_upperBound_7069_);
return v_res_7082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(lean_object* v_upperBound_7083_, lean_object* v_onAlt_7084_, uint8_t v_useSplitter_7085_, lean_object* v_extraEqualities_7086_, lean_object* v_numDiscrEqs_7087_, lean_object* v_inst_7088_, lean_object* v_R_7089_, lean_object* v_a_7090_, lean_object* v_b_7091_, lean_object* v_c_7092_, lean_object* v___y_7093_, lean_object* v___y_7094_, lean_object* v___y_7095_, lean_object* v___y_7096_){
_start:
{
lean_object* v___x_7098_; 
v___x_7098_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___redArg(v_upperBound_7083_, v_onAlt_7084_, v_useSplitter_7085_, v_extraEqualities_7086_, v_numDiscrEqs_7087_, v_a_7090_, v_b_7091_, v___y_7093_, v___y_7094_, v___y_7095_, v___y_7096_);
return v___x_7098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14___boxed(lean_object* v_upperBound_7099_, lean_object* v_onAlt_7100_, lean_object* v_useSplitter_7101_, lean_object* v_extraEqualities_7102_, lean_object* v_numDiscrEqs_7103_, lean_object* v_inst_7104_, lean_object* v_R_7105_, lean_object* v_a_7106_, lean_object* v_b_7107_, lean_object* v_c_7108_, lean_object* v___y_7109_, lean_object* v___y_7110_, lean_object* v___y_7111_, lean_object* v___y_7112_, lean_object* v___y_7113_){
_start:
{
uint8_t v_useSplitter_boxed_7114_; lean_object* v_res_7115_; 
v_useSplitter_boxed_7114_ = lean_unbox(v_useSplitter_7101_);
v_res_7115_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_MatcherApp_transform___at___00Lean_Meta_MatcherApp_inferMatchType_spec__4_spec__14(v_upperBound_7099_, v_onAlt_7100_, v_useSplitter_boxed_7114_, v_extraEqualities_7102_, v_numDiscrEqs_7103_, v_inst_7104_, v_R_7105_, v_a_7106_, v_b_7107_, v_c_7108_, v___y_7109_, v___y_7110_, v___y_7111_, v___y_7112_);
lean_dec(v___y_7112_);
lean_dec_ref(v___y_7111_);
lean_dec(v___y_7110_);
lean_dec_ref(v___y_7109_);
lean_dec(v_upperBound_7099_);
return v_res_7115_;
}
}
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_AltTelescopes(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
